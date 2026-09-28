"""Houdini over mixed invariant families, even or odd geometry (see invariant_engine.py).

Usage:  python houdini_general.py odd  [--workers 12] [--timeout 20]

A candidate is (name, anchor_kind, template, bound) where
  template = ((dy, dx, coef), ...) over grid offsets from the anchor cell (y, x),
  bound    = (ck, cy, cx, c0) meaning  sum coef*T <= ck*k + cy*y + cx*x + c0,
  anchor_kind in {'hpair', 'vpair', 'edge', 'diag', 'cross', 'centre'} restricts where the
  anchor may sit (all in the fundamental region, unreflected).
Fixed families carry exact bounds; mined templates get beta from simulation data.
"""
import itertools
import json
import os
import sys
import time

import numpy as np
import z3

import invariant_engine as IE


def lap(f):
    p = np.pad(f, 1)
    return 4 * f - p[:-2, 1:-1] - p[2:, 1:-1] - p[1:-1, :-2] - p[1:-1, 2:]


def start_pile(kind, k):
    m = 2 * k
    y, x = np.indices((m, m))
    dep = np.minimum(np.minimum(y, x), np.minimum(m - 1 - y, m - 1 - x)) + 1
    Dm = lap(2 * k * dep - dep * dep + dep)
    if kind == 'even':
        return Dm
    n = m + 1
    c = np.full((n, n), 2, np.int64)
    c[k, k] = 0
    keep = [i for i in range(n) if i != k]
    c[np.ix_(keep, keep)] = Dm
    return c


def rounds(c):
    T = np.zeros_like(c)
    while True:
        yield T
        P = np.pad(T, 1)
        N = P[:-2, 1:-1] + P[2:, 1:-1] + P[1:-1, :-2] + P[1:-1, 2:]
        T2 = (c + N) // 4
        if (T2 == T).all():
            return
        T = T2


# ------------------------------------------------------------------ anchors
def anchor_ok(kind, geomkind, k, Y, X):
    """Is the (canonical == actual) cell (Y, X) a valid anchor for this kind?"""
    top = k - 1                                   # last quarter row
    if kind == 'hpair':
        return 0 <= X <= Y - 1 and Y <= top
    if kind == 'vpair':
        return 0 <= X <= Y - 1 and 1 <= Y <= top
    if kind == 'edge':
        return X == 0 and 0 <= Y <= top
    if kind == 'diag':
        return X == Y and 0 <= Y <= top
    if kind == 'cross':
        return geomkind == 'odd' and Y == k and 0 <= X <= k - 1
    if kind == 'centre':
        return geomkind == 'odd' and Y == k and X == k - 1
    raise ValueError(kind)


def fixed_candidates(geomkind):
    C = []
    C.append(('H0', 'hpair', ((0, 0, 1), (0, 1, -1)), (0, 0, 0, 0)))
    C.append(('H1', 'hpair', ((0, 1, 1), (0, 0, -1)), (2, 0, -2, -3)))
    C.append(('V0', 'vpair', ((0, 0, 1), (-1, 0, -1)), (0, 0, 0, 0)))
    C.append(('V1', 'vpair', ((-1, 0, 1), (0, 0, -1)), (2, -1, -1, -1)))
    C.append(('EDGE', 'edge', ((0, 0, 1),), (2, 0, 0, -1)))
    C.append(('E', 'diag', ((0, 0, 1), (0, -1, -1)), (2, 0, -2, -1)))       # E(d) <= 2(k-d)-1
    C.append(('Vd', 'diag', ((0, 0, 1), (1, 0, -1)), (2, 0, -2, -2)))      # Vd(d) <= 2(k-d)-2
    if geomkind == 'odd':
        C.append(('C0', 'cross', ((0, 0, 1), (-1, 0, -1)), (0, 0, 0, 0)))          # sigma <= v
        C.append(('C1', 'cross', ((-1, 0, 1), (0, 0, -1)), (0, 0, 0, 1)))         # v - sigma <= 1
        C.append(('Mstar', 'cross', ((-1, 0, 2), (0, -1, -1), (0, 1, -1)), (0, 0, 0, 2)))
        C.append(('CENTRE', 'centre', ((0, 1, 1), (0, 0, -1)), (0, 0, 0, 0)))    # T(k,k) <= T(k,k-1)
    return C


DIAG_CELLS = [(0, 0), (0, -1), (0, -2), (1, 0), (1, -1), (-1, -1), (1, 1), (2, 0), (-1, -2)]
CROSS_CELLS = [(0, 0), (0, -1), (0, 1), (-1, 0), (-1, -1), (-1, 1), (-2, 0), (0, -2), (0, 2)]


def mined_templates(cells):
    temps = set()
    for n in (2, 3):
        for sup in itertools.combinations(cells, n):
            for coefs in itertools.product((-2, -1, 1, 2), repeat=n):
                if sum(coefs) != 0 or (n == 2 and max(abs(c) for c in coefs) == 2):
                    continue
                if np.gcd.reduce([abs(c) for c in coefs]) != 1:
                    continue
                temps.add(tuple(sorted((o[0], o[1], c) for o, c in zip(sup, coefs))))
    return sorted(temps)


def geom_T(geom, T, k, Y, X):
    c = geom.canon(k, Y, X)
    return 0 if c is None else int(T[c])


def mine(geomkind, sizes, cache):
    if os.path.exists(cache):
        return [tuple(x) if not isinstance(x, list) else x for x in json.load(open(cache))]
    geom = IE.Geometry(geomkind)
    fams = [('diag', DIAG_CELLS)] + ([('cross', CROSS_CELLS)] if geomkind == 'odd' else [])
    temps = [(kind, t) for kind, cells in fams for t in mined_templates(cells)]
    best = {(kind, t): [-10**9] * 4 for kind, t in temps}
    for k in sizes:
        c = start_pile(geomkind, k)
        anchors = {'diag': [(d, d) for d in range(k)],
                   'cross': [(k, x) for x in range(k)]}
        for T in rounds(c):
            for kind, t in temps:
                b = best[(kind, t)]
                for (ay, ax) in anchors[kind]:
                    v = sum(cf * geom_T(geom, T, k, ay + dy, ax + dx) for dy, dx, cf in t)
                    for a in range(4):
                        w = v - a * (k - ax)
                        if w > b[a]:
                            b[a] = w
    out = []
    for (kind, t), bs in best.items():
        for a in range(4):
            out.append((f"{kind}:{t}:a{a}", kind, t, (a, 0, -a, bs[a])))
    json.dump(out, open(cache, 'w'))
    return out


def norm(c):
    name, kind, t, bound = c
    return (name, kind, tuple(tuple(x) for x in t), tuple(bound))


# ------------------------------------------------------------------ one Houdini round in one window
def window_round(args):
    geomkind, wkind, prof, cands, live, timeout = args
    geom = IE.Geometry(geomkind)
    w = IE.Window(geom, wkind, prof)
    if not w.ok:
        return set()
    k = w.k
    # symbolic actual coordinates of window offset o (only used for unreflected anchors)
    def actual(o):
        return (w.ay + o[0], w.ax + o[1])
    def unreflected(o):
        c = w.cc.get(o)
        if c is None or c[0] is None:
            return False
        for (kk, aa, bb), p in zip(w.smp, c):
            yy, xx = IE.anchor_coords(wkind, kk, aa, bb)
            if p != (yy + o[0], xx + o[1]):
                return False
        return True
    def valid_anchor(kind, o):
        if not unreflected(o):
            return False
        for (kk, aa, bb), p in zip(w.smp, w.cc[o]):
            if not anchor_ok(kind, geomkind, kk, p[0], p[1]):
                return False
        return True
    def expr(c, o, Tf):
        name, kind, t, (ck, cy, cx, c0) = c
        terms = []
        for dy, dx, cf in t:
            q = (o[0] + dy, o[1] + dx)
            if q not in w.cc:
                return None
            v = Tf(q)
            if v is None:
                return None
            terms.append(cf * v)
        Y, X = actual(o)
        return sum(terms) <= ck * k + cy * Y + cx * X + c0
    s = z3.Solver()
    s.set('timeout', timeout * 1000)
    s.add(w.cons)
    s.add(w.content_constraints())
    for i in live:
        c = cands[i]
        for o in w.offs:
            if valid_anchor(c[1], o):
                e = expr(c, o, w.T)
                if e is not None:
                    s.add(e)
    nx, ncons = w.next_vars(w.R - 1)
    s.add(ncons)
    goals = {}
    for i in live:
        c = cands[i]
        if valid_anchor(c[1], (0, 0)):
            e = expr(c, (0, 0), lambda q: w.NT(nx, q))
            if e is not None:
                goals[i] = e
    dropped, proven = set(), set()
    tag = f"{geomkind}_{wkind}_" + "_".join(str(x).replace("'", "").replace(" ", "") for x in prof)
    log = open(f"hg_{tag}.log", "a")
    t0 = time.time()
    order = list(goals)
    for n_done, i in enumerate(order):
        if i in dropped:
            continue
        s.push()
        s.add(z3.Not(goals[i]))
        r = s.check()
        if r == z3.unsat:
            s.pop()
            proven.add(i)
        elif r == z3.sat:
            mdl = s.model()
            s.pop()
            killed = {j for j in order if j not in dropped and j not in proven
                      and z3.is_false(mdl.eval(goals[j], model_completion=True))}
            dropped |= killed | {i}
        else:
            s.pop()
            dropped.add(i)
        if n_done % 50 == 0:
            log.write(f"{time.time()-t0:7.0f}s {n_done}/{len(order)} proven {len(proven)} dropped {len(dropped)}" + chr(10))
            log.flush()
    log.write(f"{time.time()-t0:7.0f}s done proven {len(proven)} dropped {len(dropped)}" + chr(10))
    log.close()
    return dropped


def main():
    import multiprocessing as mp
    geomkind = sys.argv[1] if len(sys.argv) > 1 else 'odd'
    workers = 12
    timeout = 20
    for i, a in enumerate(sys.argv):
        if a == '--workers':
            workers = int(sys.argv[i + 1])
        if a == '--timeout':
            timeout = int(sys.argv[i + 1])
    sizes = list(range(5, 41))
    cands = [norm(c) for c in fixed_candidates(geomkind)]
    print(f"mining templates on k = {sizes[0]}..{sizes[-1]} ({geomkind}) ...", flush=True)
    cands += [norm(c) for c in mine(geomkind, sizes, f"hg_mined_{geomkind}.json")]
    print(f"{len(cands)} candidates ({len(fixed_candidates(geomkind))} fixed)", flush=True)
    windows = [('cell', p) for p in itertools.product(*IE.PROFILE_VALUES['cell'])]
    windows += [('diag', p) for p in itertools.product(*IE.PROFILE_VALUES['diag'])]
    if geomkind == 'odd':
        windows += [('cross', p) for p in itertools.product(*IE.PROFILE_VALUES['cross'])]
    live = set(range(len(cands)))
    rnd = 0
    with mp.Pool(workers) as pool:
        while True:
            rnd += 1
            res = pool.map(window_round, [(geomkind, wk, p, cands, live, timeout) for wk, p in windows], chunksize=1)
            dropped = set().union(*res)
            live -= dropped
            fixed_alive = [cands[i][0] for i in sorted(live) if i < len(fixed_candidates(geomkind))]
            print(f"round {rnd}: dropped {len(dropped)}, {len(live)} remain; fixed alive: {fixed_alive}", flush=True)
            if not dropped:
                break
    json.dump([cands[i] for i in sorted(live)], open(f"hg_live_{geomkind}.json", 'w'))
    nfix = len(fixed_candidates(geomkind))
    ok = all(i in live for i in range(nfix))
    print("ALL FIXED FAMILIES SURVIVE (inductive):" if ok else "some fixed families dropped:", ok, flush=True)


if __name__ == "__main__":
    main()
