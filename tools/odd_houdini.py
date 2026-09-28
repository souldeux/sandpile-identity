"""Houdini for the odd grid (condition (M)), using invariant_engine windows.

Candidates (all as linear inequalities over grid offsets from an anchor, bound
ck*k + cy*Y + cx*X + c0 with (Y, X) the anchor, optionally only where k - X >= thr):
  fixed:  H0, H1, V0, V1, EDGE (quarter cells), E, Vd (diagonal), C0, C1, Mstar (cross), CENTRE
  mined:  named 2-cell differences (1-2 terms) around diagonal anchors and around cross anchors.
Background: nonnegative contents. Goals: first a real-valued check, then integers; timeouts are
rechecked with a long limit and reported, never silently dropped. Per-task results are cached.

Usage: python odd_houdini.py [--workers 14]
"""
import hashlib
import itertools
import json
import os
import sys
import time

import numpy as np
import z3

import invariant_engine as IE
from houdini_general import start_pile, rounds, anchor_ok

NAMED_DIAG = {
    'E0': ((0, 0), (0, -1)), 'E1': ((1, 1), (1, 0)), 'Em': ((-1, -1), (-1, -2)),
    'Vd0': ((0, 0), (1, 0)), 'Vdm': ((-1, -1), (0, -1)),
    'V1': ((0, -1), (1, -1)), 'V2': ((1, 0), (2, 0)),
    'H1': ((0, -1), (0, -2)), 'H2': ((1, 0), (1, -1)),
    'G1': ((0, 0), (1, 1)), 'G0': ((-1, -1), (0, 0)),
}
NAMED_CROSS = {                     # anchor (k, x): sigma_x
    'C': ((-1, 0), (0, 0)),         # v_x - sigma_x
    'Cl': ((-1, -1), (0, -1)),      # v_{x-1} - sigma_{x-1}
    'Cr': ((-1, 1), (0, 1)),        # v_{x+1} - sigma_{x+1}
    'Sx': ((0, 1), (0, 0)),         # sigma_{x+1} - sigma_x
    'Sxl': ((0, 0), (0, -1)),       # sigma_x - sigma_{x-1}
    'Vx': ((-1, 1), (-1, 0)),       # v_{x+1} - v_x
    'Vxl': ((-1, 0), (-1, -1)),     # v_x - v_{x-1}
    'U': ((-2, 0), (-1, 0)),        # T(k-2,x) - v_x
    'Ul': ((-2, -1), (-1, -1)),
    'Ur': ((-2, 1), (-1, 1)),
}
ALPHAS = range(0, 4)
THRS = (0, 3)
GEOM = IE.Geometry('odd')


def combos(named):
    names = sorted(named)
    out, seen = [], set()
    for n in (1, 2):
        for ns in itertools.combinations(names, n):
            for sg in itertools.product((1, -1), repeat=n):
                t = {}
                for name, s in zip(ns, sg):
                    a, b = named[name]
                    t[a] = t.get(a, 0) + s
                    t[b] = t.get(b, 0) - s
                t = tuple(sorted((o, c) for o, c in t.items() if c))
                if t and t not in seen:
                    seen.add(t)
                    out.append(('+'.join(('' if s > 0 else '-') + nm for nm, s in zip(ns, sg)), t))
    return out


def mine(kind, named, ks):
    temps = combos(named)
    cells = sorted({o for a, b in named.values() for o in (a, b)})
    best = {}
    for k in ks:
        c = start_pile('odd', k)
        anchors = [(d, d) for d in range(k)] if kind == 'diag' else [(k, x) for x in range(k)]
        idx = {}
        for o in cells:
            ys, xs, ok = [], [], []
            for (ay, ax) in anchors:
                cc = GEOM.canon(k, ay + o[0], ax + o[1])
                ys.append(cc[0] if cc else 0); xs.append(cc[1] if cc else 0); ok.append(1 if cc else 0)
            idx[o] = (np.array(ys), np.array(xs), np.array(ok))
        kx = np.array([k - ax for (_, ax) in anchors])
        for T in rounds(c):
            vals = {o: T[idx[o][0], idx[o][1]] * idx[o][2] for o in cells}
            for name, t in temps:
                v = sum(cf * vals[o] for o, cf in t)
                for thr in THRS:
                    m = kx >= max(thr, 1)
                    if not m.any():
                        continue
                    for a in ALPHAS:
                        w = int((v[m] - a * kx[m]).max())
                        key = (name, a, thr)
                        if key not in best or w > best[key][1]:
                            best[key] = (t, w)
    out = []
    for (name, a, thr), (t, b) in best.items():
        out.append({'name': f"{kind}:{name}", 'kind': kind, 't': [[list(o), c] for o, c in t],
                    'bound': [a, 0, -a, b], 'thr': thr})
    return out


def fixed():
    F = [('H0', 'hpair', [[[0, 0], 1], [[0, 1], -1]], [0, 0, 0, 0]),
         ('H1', 'hpair', [[[0, 1], 1], [[0, 0], -1]], [2, 0, -2, -3]),
         ('V0', 'vpair', [[[0, 0], 1], [[-1, 0], -1]], [0, 0, 0, 0]),
         ('V1', 'vpair', [[[-1, 0], 1], [[0, 0], -1]], [2, -1, -1, -1]),
         ('EDGE', 'edge', [[[0, 0], 1]], [2, 0, 0, -1]),
         ('E', 'diag', [[[0, 0], 1], [[0, -1], -1]], [2, 0, -2, -1]),
         ('Vd', 'diag', [[[0, 0], 1], [[1, 0], -1]], [2, 0, -2, -2]),
         ('C0', 'cross', [[[0, 0], 1], [[-1, 0], -1]], [0, 0, 0, 0]),
         ('C1', 'cross', [[[-1, 0], 1], [[0, 0], -1]], [0, 0, 0, 1]),
         ('Mstar', 'cross', [[[-1, 0], 2], [[0, -1], -1], [[0, 1], -1]], [0, 0, 0, 2]),
         ('CENTRE', 'centre', [[[0, 1], 1], [[0, 0], -1]], [0, 0, 0, 0])]
    return [{'name': n, 'kind': k, 't': t, 'bound': b, 'thr': 0} for n, k, t, b in F]


def pool(cache="odd_pool.json"):
    if os.path.exists(cache):
        return json.load(open(cache))
    ks = list(range(5, 36))
    p = mine('diag', NAMED_DIAG, ks) + mine('cross', NAMED_CROSS, ks)
    json.dump(p, open(cache, 'w'))
    return p


# ------------------------------------------------------------------ windows
class Built:
    pass


def build(wkind, prof, cands, live, sort):
    w = IE.Window(GEOM, wkind, prof)
    b = Built(); b.w = w
    if not w.ok:
        return b
    if sort is z3.Real:
        # rebuild variables as reals: re-create the var map with the same keys
        for key in list(w.var):
            w.var[key] = z3.Real(str(w.var[key]))
        w.cons = list(w.base) + [v >= 0 for v in w.var.values()]
    k = w.k
    def unreflected(o):
        c = w.cc.get(o)
        if c is None or c[0] is None:
            return False
        for (kk, aa, bb), p in zip(w.smp, c):
            yy, xx = IE.anchor_coords(wkind, kk, aa, bb)
            if p != (yy + o[0], xx + o[1]):
                return False
        return True
    def valid(kind, o):
        if not unreflected(o):
            return False
        return all(anchor_ok(kind, 'odd', kk, p[0], p[1]) for (kk, _, _), p in zip(w.smp, w.cc[o]))
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
    s.add(w.cons)
    s.add(w.content_constraints())
    for i in live:
        c = cands[i]
        for o in w.offs:
            if valid(c['kind'], o):
                e = expr(c, o, w.T)
                if e is not None:
                    s.add(e)
    nx, ncons = w.next_vars(w.R - 1)
    if sort is z3.Real:
        nx = {kk: z3.Real(str(v)) for kk, v in nx.items()}
        ncons = []
        for o in w.offs:
            if max(abs(o[0]), abs(o[1])) > w.R - 1:
                continue
            kk = w.key(o)
            if kk is None or kk not in nx or any(str(x) == str(nx[kk]) for x in []):
                continue
        # rebuild floor constraints for real next vars
        seen = set()
        for o in w.offs:
            if max(abs(o[0]), abs(o[1])) > w.R - 1:
                continue
            kk = w.key(o)
            if kk is None or kk in seen:
                continue
            seen.add(kk)
            S = w.D(kk) + sum(w.T((o[0] + a, o[1] + bb)) for a, bb in ((-1, 0), (1, 0), (0, -1), (0, 1)))
            ncons += [4 * nx[kk] <= S, S <= 4 * nx[kk] + 3]
    s.add(ncons)
    goals = {}
    for i in live:
        c = cands[i]
        if valid(c['kind'], (0, 0)):
            e = expr(c, (0, 0), lambda q: w.NT(nx, q))
            if e is not None:
                goals[i] = e
    b.s, b.goals = s, goals
    return b


def work(args):
    wkind, prof, sl, nsl, cands, live, timeout = args
    tag = f"{wkind}_" + "_".join(str(x).replace("'", "").replace(" ", "") for x in prof) + f"_s{sl}of{nsl}"
    lh = hashlib.sha1(",".join(map(str, sorted(live))).encode()).hexdigest()[:12]
    cache = f"oh_result_{lh}_{tag}.json"
    if os.path.exists(cache):
        r = json.load(open(cache)); return set(r[0]), set(r[1]), r[2]
    br = build(wkind, prof, cands, live, z3.Real)
    if not br.w.ok:
        json.dump([[], [], 0], open(cache, 'w')); return set(), set(), 0
    bi = build(wkind, prof, cands, live, z3.Int)
    br.s.set('timeout', 30000); bi.s.set('timeout', timeout * 1000)
    mine_ = [i for n_, i in enumerate(sorted(bi.goals)) if n_ % nsl == sl]
    dropped, proven, unknown = set(), set(), set()
    log = open(f"oh_{tag}.log", "a"); t0 = time.time()
    for n_done, i in enumerate(mine_):
        if i in dropped:
            continue
        br.s.push(); br.s.add(z3.Not(br.goals[i])); r = br.s.check(); br.s.pop()
        if r == z3.unsat:
            proven.add(i); continue
        bi.s.push(); bi.s.add(z3.Not(bi.goals[i])); r = bi.s.check()
        if r == z3.unsat:
            bi.s.pop(); proven.add(i)
        elif r == z3.sat:
            m = bi.s.model(); bi.s.pop()
            dropped |= {j for j in mine_ if j not in dropped and j not in proven
                        and z3.is_false(m.eval(bi.goals[j], model_completion=True))} | {i}
        else:
            bi.s.pop(); unknown.add(i)
        if n_done % 100 == 0:
            log.write(f"{time.time()-t0:6.0f}s {n_done}/{len(mine_)} proven {len(proven)} dropped {len(dropped)} unknown {len(unknown)}" + chr(10)); log.flush()
    bi.s.set('timeout', 600000)
    still = set()
    for i in sorted(unknown - dropped):
        bi.s.push(); bi.s.add(z3.Not(bi.goals[i])); r = bi.s.check(); bi.s.pop()
        if r == z3.unsat:
            proven.add(i)
        elif r == z3.sat:
            dropped.add(i)
        else:
            still.add(i)
    log.write(f"{time.time()-t0:6.0f}s done proven {len(proven)} dropped {len(dropped)} unresolved {len(still)}" + chr(10)); log.close()
    json.dump([sorted(dropped), sorted(still), len(proven)], open(cache, 'w'))
    return dropped, still, len(proven)


def main():
    import multiprocessing as mp
    workers = 14
    for i, a in enumerate(sys.argv):
        if a == '--workers':
            workers = int(sys.argv[i + 1])
    fx = fixed()
    cands = fx + pool()
    print(f"{len(cands)} candidates ({len(fx)} fixed)", flush=True)
    windows = [('cell', p) for p in itertools.product(*IE.PROFILE_VALUES['cell'])]
    windows += [('diag', p) for p in itertools.product(*IE.PROFILE_VALUES['diag'])]
    windows += [('cross', p) for p in itertools.product(*IE.PROFILE_VALUES['cross'])]
    # drop impossible windows up front
    windows = [(wk, p) for wk, p in windows if IE.Window(GEOM, wk, p).ok]
    print(f"{len(windows)} feasible windows", flush=True)
    live = set(range(len(cands)))
    rnd = 0
    with mp.Pool(workers) as pool_:
        while True:
            rnd += 1
            tasks = []
            for wk, p in windows:
                nsl = 1 if wk == 'cell' else (6 if 'ge' in str(p[0]) and 'ge' in str(p[1]) else 2)
                tasks += [(wk, p, s, nsl, cands, live, 60) for s in range(nsl)]
            res = pool_.map(work, tasks, chunksize=1)
            dropped = set().union(*[r[0] for r in res])
            unresolved = set().union(*[r[1] for r in res])
            live -= dropped
            fx_alive = [cands[i]['name'] for i in range(len(fx)) if i in live]
            print(f"round {rnd}: dropped {len(dropped)}, {len(live)} remain, unresolved {len(unresolved)}; fixed alive: {fx_alive}", flush=True)
            if not dropped:
                break
    json.dump({'live': [cands[i] for i in sorted(live)], 'unresolved': sorted(unresolved)}, open("odd_live.json", "w"))
    need = {'C0', 'C1', 'Mstar', 'CENTRE', 'H0', 'H1', 'V0', 'V1', 'EDGE', 'E', 'Vd'}
    alive = {cands[i]['name'] for i in live}
    print("fixed families alive:", sorted(need & alive), " missing:", sorted(need - alive), flush=True)


if __name__ == "__main__":
    main()
