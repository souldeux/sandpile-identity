"""Two-round inductive check of the fixed families on the odd grid.

Induction over consecutive pairs of rounds: if every family holds at rounds t-1 and t, and round t
is exactly one parallel step after round t-1 (on the window's inner cells), then every family holds
at round t+1. Base: rounds 0 (all zero) and 1 (diagonal cell (d,d) has k-d topples, all else 0) --
checked by hand in PROOF-NOTES. The previous round carries the "freshness" information: a cell
holds at most 3 grains plus what it received in the last round.
"""
import itertools
import json
import os
import sys
import multiprocessing as mp

import z3

import invariant_engine as IE
import odd_houdini as O
from houdini_general import anchor_ok


def fams():
    fx = O.fixed()
    for c in fx:
        if c['name'] == 'V1':
            c['bound'] = [2, -2, 0, 0]          # V(y,x) <= 2(k - y)
        if c['name'] == 'Vd':
            c['thr'] = 2                         # d <= k-2 only
    fx.append({'name': 'H2', 'kind': 'hpair', 't': [[[0, 1], 1], [[0, 0], -1]], 'bound': [2, -1, -1, -2], 'thr': 0})
    fx.append({'name': 'CU2', 'kind': 'cross', 't': [[[-2, 0], 1], [[0, 0], -1]], 'bound': [0, 0, 0, 2], 'thr': 0})
    drop = set(os.environ.get('DROP', '').split(',')) - {''}
    return [c for c in fx if c['name'] not in drop]


def check_window(args):
    wk, prof, timeout = args
    fx = fams()
    w = IE.Window(O.GEOM, wk, prof)
    if not w.ok:
        return wk, prof, [], [], 0
    k = w.k
    # previous-round variables, one per canonical cell
    prev = {key: z3.Int("P" + str(v)) for key, v in w.var.items()}
    def TP(o):
        kk = w.key(o)
        return z3.IntVal(0) if kk is None else prev[kk]
    def unreflected(o):
        c = w.cc.get(o)
        if c is None or c[0] is None:
            return False
        for (kk, aa, bb), p in zip(w.smp, c):
            yy, xx = IE.anchor_coords(wk, kk, aa, bb)
            if p != (yy + o[0], xx + o[1]):
                return False
        return True
    def valid(kind, o):
        return unreflected(o) and all(anchor_ok(kind, 'odd', kk, p[0], p[1]) for (kk, _, _), p in zip(w.smp, w.cc[o]))
    def expr(c, o, Tf):
        terms = []
        for (dy, dx), cf in c['t']:
            q = (o[0] + dy, o[1] + dx)
            if q not in w.cc:
                return None
            v = Tf(q)
            if v is None:
                return None
            terms.append(cf * v)
        Y, X = w.ay + o[0], w.ax + o[1]
        ck, cy, cx, c0 = c['bound']
        ineq = sum(terms) <= ck * k + cy * Y + cx * X + c0
        return z3.Implies(k - X >= max(c['thr'], 1), ineq) if c['thr'] else ineq
    s = z3.Solver()
    s.set('timeout', timeout * 1000)
    s.add(w.cons)
    s.add([v >= 0 for v in prev.values()])
    # families at both rounds
    for c in fx:
        for o in w.offs:
            if valid(c['kind'], o):
                for Tf in (w.T, TP):
                    e = expr(c, o, Tf)
                    if e is not None:
                        s.add(e)
    # contents >= 0 at both rounds; one exact parallel step prev -> current on inner cells; monotone in time
    seen = set()
    for o in w.offs:
        kk = w.key(o)
        if kk is None or kk in seen:
            continue
        seen.add(kk)
        s.add(w.T(o) >= TP(o))
        if max(abs(o[0]), abs(o[1])) <= w.R - 1:
            nb = ((-1, 0), (1, 0), (0, -1), (0, 1))
            Sc = w.D(kk) + sum(w.T((o[0] + a, o[1] + b)) for a, b in nb)
            Sp = w.D(kk) + sum(TP((o[0] + a, o[1] + b)) for a, b in nb)
            s.add(Sc - 4 * w.T(o) >= 0, Sp - 4 * TP(o) >= 0)
            s.add(4 * w.T(o) <= Sp, Sp <= 4 * w.T(o) + 3)
    # next round on cells within radius R-2 (their neighbours are inner cells)
    nx, ncons = w.next_vars(w.R - 2)
    s.add(ncons)
    bad, unk, n = [], [], 0
    for c in fx:
        if not valid(c['kind'], (0, 0)):
            continue
        g = expr(c, (0, 0), lambda q: w.NT(nx, q))
        if g is None:
            continue
        s.push(); s.add(z3.Not(g)); r = s.check(); s.pop()
        if r == z3.unsat:
            n += 1
        elif r == z3.sat:
            bad.append(c['name'])
            if os.environ.get('SHOWCEX') == c['name']:
                s.push(); s.add(z3.Not(g)); s.check(); m = s.model(); s.pop()
                print(f"CEX {c['name']} in {wk} {prof}: k={m.eval(k)} anchor=({m.eval(w.ay)},{m.eval(w.ax)})")
                for lab, Tf in (("prev", TP), ("now ", w.T)):
                    for a in range(-2, 2):
                        row = []
                        for b in range(-2, 3):
                            kk_ = w.key((a, b))
                            row.append("   ." if kk_ is None else f"{m.eval(Tf((a, b)), model_completion=True).as_long():4d}")
                        print(f"  {lab} row {a:+d}:", "".join(row))
                nxt = {o: m.eval(w.NT(nx, o), model_completion=True) for o in [(0, 0), (-1, 0), (0, -1), (0, 1)] if w.NT(nx, o) is not None}
                print("  next:", {str(o): str(v) for o, v in nxt.items()})
        else:
            unk.append(c['name'])
    return wk, prof, bad, unk, n


def main():
    windows = [('cell', p) for p in itertools.product(*IE.PROFILE_VALUES['cell'])]
    windows += [('diag', p) for p in itertools.product(*IE.PROFILE_VALUES['diag'])]
    windows += [('cross', p) for p in itertools.product(*IE.PROFILE_VALUES['cross'])]
    windows = [(wk, p) for wk, p in windows if IE.Window(O.GEOM, wk, p).ok]
    print(f"{len(windows)} windows", flush=True)
    fails, total = [], 0
    with mp.Pool(int(sys.argv[1]) if len(sys.argv) > 1 else 14) as pool:
        for wk, p, bad, unk, n in pool.imap_unordered(check_window, [(wk, p, 600) for wk, p in windows]):
            total += n
            if bad or unk:
                fails.append((wk, str(p), bad, unk))
                print(f"  {wk} {p}: NOT PROVEN {bad} unresolved {unk}", flush=True)
    print(f"proven goals: {total}; windows with failures: {len(fails)}", flush=True)
    json.dump(fails, open("odd_check2_failures.json", "w"))


if __name__ == "__main__":
    main()
