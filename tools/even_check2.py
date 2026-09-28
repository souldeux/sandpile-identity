"""Two-round inductive check on the even grid, including the mixed-round family

    LA(j):  T_t(k-1,j-1) - 2 T_t(k-1,j) + T_t(k-1,j+1)  +  [T_t(k-1,j) - T_{t-1}(k-1,j)]  >= -1

for 0 <= j <= k-1 (T(k-1,-1) = 0 is the sink, T(k-1,k) = T(k-1,k-1) by mirror symmetry).
At the final state the bracket is 0, so LA gives (L): the second difference of the odometer along
row k-1 is >= -1, i.e. every seam value s = 2 + second difference is >= 1.

Induction over pairs of rounds: families at t-1 and t (single-round ones at both rounds, LA on
the pair) + T_t = F(T_{t-1}) on inner cells  =>  families at t+1 (LA on the pair (t, t+1)).
Base: rounds 0 and 1 (checked in PROOF-NOTES).
"""
import itertools
import json
import os
import sys
import multiprocessing as mp

import z3

import invariant_engine as IE
from houdini_general import anchor_ok

GEOM = IE.Geometry('even')


def single_families():
    return [
        {'name': 'H0', 'kind': 'hpair', 't': [[[0, 0], 1], [[0, 1], -1]], 'bound': [0, 0, 0, 0]},
        {'name': 'H1', 'kind': 'hpair', 't': [[[0, 1], 1], [[0, 0], -1]], 'bound': [2, 0, -2, -3]},
        {'name': 'EDGE', 'kind': 'edge', 't': [[[0, 0], 1]], 'bound': [2, 0, 0, -1]},
        {'name': 'V0', 'kind': 'vpair', 't': [[[0, 0], 1], [[-1, 0], -1]], 'bound': [0, 0, 0, 0]},
        {'name': 'V1', 'kind': 'vpair', 't': [[[-1, 0], 1], [[0, 0], -1]], 'bound': [2, -2, 0, 0]},
        {'name': 'E', 'kind': 'diag', 't': [[[0, 0], 1], [[0, -1], -1]], 'bound': [2, 0, -2, -1]},
    ]


def la_anchor_ok(k, Y, X):
    return Y == k - 1 and 0 <= X <= k - 1


# mixed-round families: sum of coef * T_round(anchor + offset) <= rhs, anchored on row k-1
MIXED = [
    # VA: T_{t-1}(k-2, j) - T_t(k-1, j) <= 1   (step into the midline row exceeds 1 only after the
    #     cell above toppled), for 0 <= j <= k-2
    # VA_y: T_{t-1}(y-1, x) - T_t(y, x) <= 2(k - y) - 1  (a vertical step is at its maximum only right
    #       after the cell above toppled); every cell below the diagonal with y >= 1. At y = k-1 this is VA.
    ('VAy', lambda k, Y, X: 1 <= Y <= k - 1 and 0 <= X <= Y - 1, [((-1, 0), 'prev', 1), ((0, 0), 'now', -1)],
     ('lin', 2, -2, 0, -1)),
    # VD: 2 T(k-2, j) - T(k-1, j-1) - T(k-1, j+1) <= 4   (i.e. 2V - D <= 4), for 0 <= j <= k-2
    ('VD', lambda k, Y, X: Y == k - 1 and 0 <= X <= k - 2,
     [((-1, 0), 'now', 2), ((0, -1), 'now', -1), ((0, 1), 'now', -1)], 4),
    # with v = midline row, u = row above:  z = 2 + u + vl + vr - 3v (grains), delta = u - v (step)
    # P1: a step of 2 forces >= 4 grains:            3u - v - vl - vr <= 6
    ('P1', lambda k, Y, X: Y == k - 1 and 0 <= X <= k - 2,
     [((-1, 0), 'now', 3), ((0, 0), 'now', -1), ((0, -1), 'now', -1), ((0, 1), 'now', -1)], 6),
    # P2: at least one grain:                        3v - u - vl - vr <= 1
    ('P2', lambda k, Y, X: Y == k - 1 and 0 <= X <= k - 2,
     [((0, 0), 'now', 3), ((-1, 0), 'now', -1), ((0, -1), 'now', -1), ((0, 1), 'now', -1)], 1),
    # P3: z <= 2 + 2 delta:                          vl + vr - v - u <= 0
    ('P3', lambda k, Y, X: Y == k - 1 and 0 <= X <= k - 2,
     [((0, -1), 'now', 1), ((0, 1), 'now', 1), ((0, 0), 'now', -1), ((-1, 0), 'now', -1)], 0),
    # P5: a tight cell has a neighbour with step 2:  6v - 2vl - 2vr - ul - ur <= 3   (j <= k-3)
    ('P5', lambda k, Y, X: Y == k - 1 and 0 <= X <= k - 3,
     [((0, 0), 'now', 6), ((0, -1), 'now', -2), ((0, 1), 'now', -2), ((-1, -1), 'now', -1), ((-1, 1), 'now', -1)], 3),
]


def check_window(args):
    wk, prof, timeout = args
    fams = single_families()
    w = IE.Window(GEOM, wk, prof)
    if not w.ok:
        return wk, prof, [], [], 0
    k = w.k
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
        if not unreflected(o):
            return False
        if kind == 'LA':
            return all(la_anchor_ok(kk, p[0], p[1]) for (kk, _, _), p in zip(w.smp, w.cc[o]))
        return all(anchor_ok(kind, 'even', kk, p[0], p[1]) for (kk, _, _), p in zip(w.smp, w.cc[o]))
    def fexpr(c, o, Tf):
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
        return sum(terms) <= ck * k + cy * Y + cx * X + c0
    def la_expr(o, Tnow, Tbefore):
        cells = [(o[0], o[1] - 1), o, (o[0], o[1] + 1)]
        if any(q not in w.cc for q in cells):
            return None
        vals = [Tnow(q) for q in cells] + [Tbefore(o)]
        if any(v is None for v in vals):
            return None
        a, b, c, bp = vals
        return a - 2 * b + c + (b - bp) >= -1
    s = z3.Solver()
    s.set('timeout', timeout * 1000)
    s.add(w.cons)
    s.add([v >= 0 for v in prev.values()])
    for c in fams:
        for o in w.offs:
            if valid(c['kind'], o):
                for Tf in (w.T, TP):
                    e = fexpr(c, o, Tf)
                    if e is not None:
                        s.add(e)
    for o in w.offs:
        if valid('LA', o):
            e = la_expr(o, w.T, TP)
            if e is not None:
                s.add(e)
    def mixed_valid(pred, o):
        return unreflected(o) and all(pred(kk, p[0], p[1]) for (kk, _, _), p in zip(w.smp, w.cc[o]))
    def mixed_expr(terms, rhs, o, Tnow, Tprev):
        acc = []
        for (dy, dx), rd, cf in terms:
            q = (o[0] + dy, o[1] + dx)
            if q not in w.cc:
                return None
            v = (Tnow if rd == 'now' else Tprev)(q)
            if v is None:
                return None
            acc.append(cf * v)
        if isinstance(rhs, tuple):
            _, ck, cy, cx, c0 = rhs
            Y, X = w.ay + o[0], w.ax + o[1]
            return sum(acc) <= ck * k + cy * Y + cx * X + c0
        return sum(acc) <= rhs
    for name, pred, terms, rhs in MIXED:
        for o in w.offs:
            if mixed_valid(pred, o):
                e = mixed_expr(terms, rhs, o, w.T, TP)
                if e is not None:
                    s.add(e)
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
    nx, ncons = w.next_vars(w.R - 2)
    s.add(ncons)
    NT = lambda q: w.NT(nx, q)
    bad, unk, n = [], [], 0
    goals = []
    for c in fams:
        if valid(c['kind'], (0, 0)):
            g = fexpr(c, (0, 0), NT)
            if g is not None:
                goals.append((c['name'], g))
    if valid('LA', (0, 0)):
        g = la_expr((0, 0), NT, w.T)
        if g is not None:
            goals.append(('LA', g))
    for name, pred, terms, rhs in MIXED:
        if mixed_valid(pred, (0, 0)):
            g = mixed_expr(terms, rhs, (0, 0), NT, w.T)
            if g is not None:
                goals.append((name, g))
    for name, g in goals:
        s.push(); s.add(z3.Not(g)); r = s.check(); s.pop()
        if r == z3.unsat:
            n += 1
        elif r == z3.sat:
            bad.append(name)
            if os.environ.get('SHOWCEX') == name:
                s.push(); s.add(z3.Not(g)); s.check(); m = s.model(); s.pop()
                print(f"CEX {name} in {wk} {prof}: k={m.eval(k)} anchor=({m.eval(w.ay)},{m.eval(w.ax)})")
                for lab, Tf in (("prev", TP), ("now ", w.T), ("next", NT)):
                    for a in range(-2, 2):
                        row = []
                        for b in range(-2, 3):
                            kk_ = w.key((a, b))
                            if kk_ is None:
                                row.append("   ."); continue
                            v = Tf((a, b))
                            row.append("   ?" if v is None else f"{m.eval(v, model_completion=True).as_long():4d}")
                        print(f"  {lab} row {a:+d}:", "".join(row))
        else:
            unk.append(name)
    return wk, prof, bad, unk, n


def main():
    windows = [('cell', p) for p in itertools.product(*IE.PROFILE_VALUES['cell'])]
    windows += [('diag', p) for p in itertools.product(*IE.PROFILE_VALUES['diag'])]
    windows = [(wk, p) for wk, p in windows if IE.Window(GEOM, wk, p).ok]
    print(f"{len(windows)} windows", flush=True)
    fails, total = [], 0
    with mp.Pool(int(sys.argv[1]) if len(sys.argv) > 1 else 14) as pool:
        for wk, p, bad, unk, n in pool.imap_unordered(check_window, [(wk, p, 600) for wk, p in windows]):
            total += n
            if bad or unk:
                fails.append((wk, str(p), bad, unk))
                print(f"  {wk} {p}: NOT PROVEN {bad} unresolved {unk}", flush=True)
    print(f"proven goals: {total}; windows with failures: {len(fails)}", flush=True)
    json.dump(fails, open("even_check2_failures.json", "w"))


if __name__ == "__main__":
    main()
