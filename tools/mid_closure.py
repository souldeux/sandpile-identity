"""Core-guided closure for the midline facts on the even grid (two-round induction).

Anchor: a cell (k-1, j) on the row beside the midline, 0 <= j <= k-2.
Features (grid offsets from the anchor, 'n' = round t, 'p' = round t-1):
  v_b = T_n(k-1, j+b), b in -2..2;  u_b = T_n(k-2, j+b), b in -1..1;  w0 = T_n(k-3, j);
  pv_b = T_p(k-1, j+b), b in -1..1; pu0 = T_p(k-2, j).
Candidates: integer combinations of 2-4 features with coefficients summing to 0, bound = the
largest value seen over all simulated round pairs (from the base pair (round 0, round 1) on).
Targets: LA, VA, VD. Background (untracked): H0, H1, EDGE, V0, V1', E at both rounds, the exact
parallel step between the rounds, nonnegative contents, counts nondecreasing in time.
"""
import itertools
import json
import multiprocessing as mp
import os
import sys
import time

import numpy as np
import z3

import invariant_engine as IE
from houdini_general import anchor_ok, start_pile
import even_check2 as EC

GEOM = IE.Geometry('even')
FEATS = ([('n', (0, b)) for b in range(-2, 3)] + [('n', (-1, b)) for b in range(-1, 2)] + [('n', (-2, 0))]
         + [('p', (0, b)) for b in range(-1, 2)] + [('p', (-1, 0))])


def templates():
    out, seen = [], set()
    idx = range(len(FEATS))
    for n in (2, 3, 4):
        for sup in itertools.combinations(idx, n):
            for co in itertools.product((-2, -1, 1, 2), repeat=n):
                if sum(co) != 0 or (n == 4 and max(abs(c) for c in co) > 1):
                    continue
                if np.gcd.reduce([abs(c) for c in co]) != 1:
                    continue
                t = tuple(sorted(zip(sup, co)))
                if t not in seen:
                    seen.add(t); out.append(t)
    return out


def mine(temps, ks):
    best = np.full(len(temps), -10**9)
    C = np.zeros((len(temps), len(FEATS)), dtype=np.int64)
    for ti, t in enumerate(temps):
        for i, c in t:
            C[ti, i] = c
    for k in ks:
        D = start_pile('even', k)
        Tp = np.zeros_like(D)
        P = np.pad(Tp, 1)
        T = (D + P[:-2, 1:-1] + P[2:, 1:-1] + P[1:-1, :-2] + P[1:-1, 2:]) // 4
        J = np.arange(k - 1)
        def col(A, dy, dx):
            out = []
            for j in J:
                c = GEOM.canon(k, k - 1 + dy, j + dx)
                out.append(0 if c is None else int(A[c]))
            return np.array(out)
        while True:
            F = np.stack([col(T if r == 'n' else Tp, dy, dx) for r, (dy, dx) in FEATS])
            best = np.maximum(best, (C @ F).max(axis=1))
            P = np.pad(T, 1)
            T2 = (D + P[:-2, 1:-1] + P[2:, 1:-1] + P[1:-1, :-2] + P[1:-1, 2:]) // 4
            if (T2 == T).all():
                break
            Tp, T = T, T2
    return best


def pool(cache="mid_pool.json"):
    if os.path.exists(cache):
        return json.load(open(cache))
    temps = templates()
    best = mine(temps, list(range(3, 41)))
    out = []
    for t, b in zip(temps, best):
        terms = [[list(FEATS[i][1]), FEATS[i][0], int(c)] for i, c in t]
        out.append({'name': '+'.join(f"{c}*{FEATS[i][0]}{FEATS[i][1]}" for i, c in t), 'terms': terms, 'rhs': int(b)})
    json.dump(out, open(cache, 'w'))
    return out


def targets():
    return [
        {'name': 'LA', 'terms': [[[0, -1], 'n', 1], [[0, 0], 'n', -1], [[0, 1], 'n', 1], [[0, 0], 'p', -1]], 'rhs': None, 'ge': -1},
        {'name': 'VA', 'terms': [[[-1, 0], 'p', 1], [[0, 0], 'n', -1]], 'rhs': 1},
        {'name': 'VD', 'terms': [[[-1, 0], 'n', 2], [[0, -1], 'n', -1], [[0, 1], 'n', -1]], 'rhs': 4},
    ]


def fact_expr(c, o, Tn, Tp, w):
    acc = []
    for (dy, dx), rd, cf in c['terms']:
        q = (o[0] + dy, o[1] + dx)
        if q not in w.cc:
            return None
        v = (Tn if rd == 'n' else Tp)(q)
        if v is None:
            return None
        acc.append(cf * v)
    if c.get('ge') is not None:
        return sum(acc) >= c['ge']
    return sum(acc) <= c['rhs']


class MidWindow:
    def __init__(self, prof, cands, sort):
        w = IE.Window(GEOM, 'cell', prof)
        self.ok = w.ok
        if not w.ok:
            return
        if sort is z3.Real:
            for key in list(w.var):
                w.var[key] = z3.Real(str(w.var[key]))
            w.cons = list(w.base) + [v >= 0 for v in w.var.values()]
        k = w.k
        prev = {key: sort("P" + str(v)) for key, v in w.var.items()}
        TP = lambda o: z3.IntVal(0) if w.key(o) is None else prev[w.key(o)]
        def unreflected(o):
            c = w.cc.get(o)
            if c is None or c[0] is None:
                return False
            for (kk, aa, bb), p in zip(w.smp, c):
                if p != (aa + o[0], bb + o[1]):
                    return False
            return True
        def valid(pred, o):
            return unreflected(o) and all(pred(kk, p[0], p[1]) for (kk, _, _), p in zip(w.smp, w.cc[o]))
        mid = lambda kk, Y, X: Y == kk - 1 and 0 <= X <= kk - 2
        s = z3.Solver()
        s.add(w.cons); s.add([v >= 0 for v in prev.values()])
        for c in EC.single_families():
            for o in w.offs:
                if valid(lambda kk, Y, X, kind=c['kind']: anchor_ok(kind, 'even', kk, Y, X), o):
                    for Tf in (w.T, TP):
                        e = EC_fexpr(c, o, Tf, w)
                        if e is not None:
                            s.add(e)
        seen = set()
        for o in w.offs:
            kk_ = w.key(o)
            if kk_ is None or kk_ in seen:
                continue
            seen.add(kk_)
            s.add(w.T(o) >= TP(o))
            if max(abs(o[0]), abs(o[1])) <= w.R - 1:
                nb = ((-1, 0), (1, 0), (0, -1), (0, 1))
                Sc = w.D(kk_) + sum(w.T((o[0] + a, o[1] + b)) for a, b in nb)
                Sp = w.D(kk_) + sum(TP((o[0] + a, o[1] + b)) for a, b in nb)
                s.add(Sc - 4 * w.T(o) >= 0, Sp - 4 * TP(o) >= 0, 4 * w.T(o) <= Sp, Sp <= 4 * w.T(o) + 3)
        nx = {}
        for o in w.offs:
            if max(abs(o[0]), abs(o[1])) > w.R - 2:
                continue
            kk_ = w.key(o)
            if kk_ is None or kk_ in nx:
                continue
            n = sort("N" + str(w.var[kk_]))
            S = w.D(kk_) + sum(w.T((o[0] + a, o[1] + b)) for a, b in ((-1, 0), (1, 0), (0, -1), (0, 1)))
            s.add(4 * n <= S, S <= 4 * n + 3)
            nx[kk_] = n
        NT = lambda o: z3.IntVal(0) if w.key(o) is None else nx.get(w.key(o))
        self.lit, self.goal, self.inst = {}, {}, {}
        for i, c in enumerate(cands):
            p = z3.Bool(f"p{i}")
            used = False
            for o in w.offs:
                if valid(mid, o):
                    e = fact_expr(c, o, w.T, TP, w)
                    if e is not None:
                        s.add(z3.Implies(p, e)); used = True
                        self.inst.setdefault(i, []).append(e)
            if used:
                self.lit[i] = p
            if valid(mid, (0, 0)):
                g = fact_expr(c, (0, 0), NT, w.T, w)
                if g is not None:
                    self.goal[i] = g
        self.s = s

    def check(self, i, banned, timeout, allowed=None, want_blockers=False):
        if i not in self.goal:
            return 'n/a', []
        self.s.push(); self.s.add(z3.Not(self.goal[i])); self.s.set('timeout', timeout * 1000)
        r = self.s.check(*[p for j, p in self.lit.items() if j not in banned and (allowed is None or j in allowed)])
        out = []
        if r == z3.unsat:
            out = [int(str(p)[1:]) for p in self.s.unsat_core()]
        elif r == z3.sat and want_blockers:
            m = self.s.model()
            for j, exprs in self.inst.items():
                if j in banned or (allowed is not None and j in allowed):
                    continue
                if any(z3.is_false(m.eval(e, model_completion=True)) for e in exprs):
                    out.append(j)
        self.s.pop()
        return str(r), out


def EC_fexpr(c, o, Tf, w):
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
    return sum(terms) <= ck * w.k + cy * Y + cx * X + c0


def worker(wid, profs, cands, inq, outq, timeout):
    built = {}
    for p in profs:
        wi = MidWindow(p, cands, z3.Int)
        if wi.ok:
            built[str(p)] = (MidWindow(p, cands, z3.Real), wi)
    outq.put(('ready', wid, list(built)))
    while True:
        msg = inq.get()
        if msg is None:
            return
        i, key, banned, required, tmo = msg
        wr, wi = built[key]
        small = set(required) | {i}
        r, core = wr.check(i, banned, 30, small)
        if r != 'unsat' and r != 'n/a':
            r, core = wi.check(i, banned, tmo, small, want_blockers=True)
        outq.put(('res', i, key, r, core))


def main():
    nworkers = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    tg = targets()
    t0 = time.time()
    cands = tg + pool()
    print(f"{len(cands)} facts ({len(tg)} targets) [{time.time()-t0:.0f}s]", flush=True)
    profs = [p for p in itertools.product(*IE.PROFILE_VALUES['cell']) if p[3] == 0]
    profs = [p for p in profs if IE.Window(GEOM, 'cell', p).ok]
    print(f"{len(profs)} midline windows", flush=True)
    outq = mp.Queue(); inqs, owner, keys = [], {}, []
    for w_ in range(nworkers):
        q = mp.Queue(); inqs.append(q)
        mp.Process(target=worker, args=(w_, profs[w_::nworkers], cands, q, outq, 90), daemon=True).start()
    for _ in range(nworkers):
        _, wid, ks = outq.get()
        for key in ks:
            owner[key] = wid; keys.append(key)
    print(f"built {len(keys)} windows [{time.time()-t0:.0f}s]", flush=True)
    banned = set(json.load(open("mid_banned.json"))) if os.path.exists("mid_banned.json") else set()
    required = set(range(len(tg)))
    cores, queued = {}, set()
    inflight = 0
    tries = {}
    def submit(i, key):
        nonlocal inflight
        if (i, key) in queued or i in banned:
            return
        tmo = 90 * (4 ** tries.get((i, key), 0))
        queued.add((i, key)); inqs[owner[key]].put((i, key, frozenset(banned), frozenset(required), tmo)); inflight += 1
    def simplicity(j):
        c = cands[j]
        return (len(c['terms']), sum(abs(t[2]) for t in c['terms']), abs(c.get('rhs') or 0))
    for i in required:
        for key in keys:
            submit(i, key)
    done = 0
    while inflight:
        _, i, key, r, core = outq.get()
        inflight -= 1; queued.discard((i, key)); done += 1
        if done % 200 == 0:
            print(f"  [{time.time()-t0:.0f}s] {done} checks, required {len(required)}, banned {len(banned)}, in flight {inflight}", flush=True)
        if i in banned or i not in required:
            continue
        if r == 'n/a':
            cores[(i, key)] = []; continue
        if r == 'unsat':
            if any(j in banned for j in core):
                submit(i, key); continue
            cores[(i, key)] = core
            for j in core:
                if j not in required:
                    required.add(j)
                    for kk in keys:
                        submit(j, kk)
            continue
        if r == 'unknown':
            tries[(i, key)] = tries.get((i, key), 0) + 1
            if tries[(i, key)] <= 2:
                print(f"  timeout on [{i}] {cands[i]['name']} in {key}; retrying longer", flush=True)
                submit(i, key); continue
        if r == 'sat' and core:
            add = sorted(core, key=simplicity)[:3]
            for j in add:
                if j not in required:
                    required.add(j)
                    for kk in keys:
                        submit(j, kk)
            submit(i, key)
            continue
        banned.add(i); required.discard(i)
        json.dump(sorted(banned), open("mid_banned.json", "w"))
        print(f"  ban [{i}] {cands[i]['name']} <= {cands[i].get('rhs')} ({r} in {key})", flush=True)
        if i < len(tg):
            print(f"FAILED: target {cands[i]['name']} not provable from the pool", flush=True)
            for q in inqs: q.put(None)
            return 1
        for (j, kk), cr in list(cores.items()):
            if i in cr:
                del cores[(j, kk)]; submit(j, kk)
    for q in inqs:
        q.put(None)
    out = [cands[i] for i in sorted(required)]
    json.dump(out, open("mid_closed.json", "w"))
    print(f"CLOSED: {len(required)} facts, {len(banned)} banned, {done} checks [{time.time()-t0:.0f}s]", flush=True)
    for c in out:
        print(f"   {c['name']}  {'>= ' + str(c['ge']) if c.get('ge') is not None else '<= ' + str(c['rhs'])}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
