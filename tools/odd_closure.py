"""Parallel core-guided closure for the odd grid.

Targets: the fixed families (quarter H0/H1/EDGE/V0/V1' with V1' = V <= 2(k-y), E, Vd for d <= k-2,
cross C0/C1/Mstar, centre). Pool: mined odd candidates (odd_pool.json). A fact is required once
some proof uses it (unsat core); a fact that cannot be proven from the non-banned pool is banned
and every proof that used it is redone. Result: a closed set of facts, each proven in every window
from facts in the set (+ nonnegative contents).
"""
import itertools
import json
import multiprocessing as mp
import os
import sys
import time

import z3

import invariant_engine as IE
import odd_houdini as O
from houdini_general import anchor_ok


def targets():
    fx = O.fixed()
    for c in fx:
        if c['name'] == 'V1':
            c['bound'] = [2, -2, 0, 0]          # V(y,x) <= 2(k-y)
        if c['name'] == 'Vd':
            c['thr'] = 2                         # only d <= k-2; at d = k-1 the cell below is on the cross
    return fx


class TrackedWindow:
    def __init__(self, wkind, prof, cands, sort):
        w = IE.Window(O.GEOM, wkind, prof)
        self.ok = w.ok
        if not w.ok:
            return
        if sort is z3.Real:
            for key in list(w.var):
                w.var[key] = z3.Real(str(w.var[key]))
            w.cons = list(w.base) + [v >= 0 for v in w.var.values()]
        self.w, self.wkind = w, wkind
        k = w.k
        s = z3.Solver()
        s.add(w.cons)
        s.add(w.content_constraints())
        def unreflected(o):
            c = w.cc.get(o)
            if c is None or c[0] is None:
                return False
            for (kk, aa, bb), p in zip(w.smp, c):
                yy, xx = IE.anchor_coords(wkind, kk, aa, bb)
                if p != (yy + o[0], xx + o[1]):
                    return False
            return True
        self.valid = lambda kind, o: unreflected(o) and all(
            anchor_ok(kind, 'odd', kk, p[0], p[1]) for (kk, _, _), p in zip(w.smp, w.cc[o]))
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
        self.lit = {}
        for i, c in enumerate(cands):
            p = z3.Bool(f"p{i}")
            used = False
            for o in w.offs:
                if self.valid(c['kind'], o):
                    e = expr(c, o, w.T)
                    if e is not None:
                        s.add(z3.Implies(p, e)); used = True
            if used:
                self.lit[i] = p
        nx, ncons = w.next_vars(w.R - 1)
        if sort is z3.Real:
            nx = {kk: z3.Real(str(v)) for kk, v in nx.items()}
            ncons, seen = [], set()
            for o in w.offs:
                if max(abs(o[0]), abs(o[1])) > w.R - 1:
                    continue
                kk = w.key(o)
                if kk is None or kk in seen:
                    continue
                seen.add(kk)
                S = w.D(kk) + sum(w.T((o[0] + a, o[1] + b)) for a, b in ((-1, 0), (1, 0), (0, -1), (0, 1)))
                ncons += [4 * nx[kk] <= S, S <= 4 * nx[kk] + 3]
        s.add(ncons)
        self.goal = {}
        for i, c in enumerate(cands):
            if self.valid(c['kind'], (0, 0)):
                e = expr(c, (0, 0), lambda q: w.NT(nx, q))
                if e is not None:
                    self.goal[i] = e
        self.s = s

    def check(self, i, banned, timeout, allowed=None):
        if i not in self.goal:
            return 'n/a', []
        self.s.push()
        self.s.add(z3.Not(self.goal[i]))
        self.s.set('timeout', timeout * 1000)
        r = self.s.check(*[p for j, p in self.lit.items() if j not in banned and (allowed is None or j in allowed)])
        core = [int(str(p)[1:]) for p in self.s.unsat_core()] if r == z3.unsat else []
        self.s.pop()
        return str(r), core


def worker(wid, windows, cands, inq, outq, timeout):
    built = {}
    for wk, p in windows:
        ti = TrackedWindow(wk, p, cands, z3.Int)
        if ti.ok:
            built[(wk, str(p))] = (TrackedWindow(wk, p, cands, z3.Real), ti)
    outq.put(('ready', wid, [key for key in built]))
    while True:
        msg = inq.get()
        if msg is None:
            return
        i, key, banned, required = msg
        tr, ti = built[key]
        small = set(required) | {i}
        # 1) only the currently required facts (small, fast; core stays inside the set)
        r, core = tr.check(i, banned, 30, small)
        if r != 'unsat' and r != 'n/a':
            r, core = ti.check(i, banned, timeout, small)
        # 2) the whole non-banned pool
        if r != 'unsat' and r != 'n/a':
            r, core = tr.check(i, banned, 30)
            if r != 'unsat':
                r, core = ti.check(i, banned, timeout)
                if r == 'unknown':                  # never ban on a short timeout: one long retry
                    r, core = ti.check(i, banned, timeout * 10)
        outq.put(('res', i, key, r, core))


def main():
    nworkers = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 90
    tg = targets()
    cands = tg + O.pool()
    ntg = len(tg)
    windows = [('cell', p) for p in itertools.product(*IE.PROFILE_VALUES['cell'])]
    windows += [('diag', p) for p in itertools.product(*IE.PROFILE_VALUES['diag'])]
    windows += [('cross', p) for p in itertools.product(*IE.PROFILE_VALUES['cross'])]
    windows = [(wk, p) for wk, p in windows if IE.Window(O.GEOM, wk, p).ok]
    print(f"{len(cands)} facts ({ntg} targets), {len(windows)} windows, {nworkers} workers", flush=True)
    t0 = time.time()
    outq = mp.Queue()
    inqs, procs, owner = [], [], {}
    for w_ in range(nworkers):
        mine = windows[w_::nworkers]
        q = mp.Queue(); inqs.append(q)
        pr = mp.Process(target=worker, args=(w_, mine, cands, q, outq, timeout), daemon=True)
        pr.start(); procs.append(pr)
    keys = []
    for _ in range(nworkers):
        tag, wid, ks = outq.get()
        for key in ks:
            owner[key] = wid; keys.append(key)
    print(f"built in {time.time()-t0:.0f}s ({len(keys)} windows)", flush=True)
    banned = set()
    if os.path.exists("odd_closure_banned.json"):
        banned = set(json.load(open("odd_closure_banned.json")))
    required = set(range(ntg))
    cores = {}
    queued = set()
    inflight = 0
    def submit(i, key):
        nonlocal inflight
        if (i, key) in queued or i in banned:
            return
        queued.add((i, key))
        inqs[owner[key]].put((i, key, frozenset(banned), frozenset(required)))
        inflight += 1
    for i in required:
        for key in keys:
            submit(i, key)
    done = 0
    while inflight:
        _, i, key, r, core = outq.get()
        inflight -= 1; queued.discard((i, key)); done += 1
        if done % 200 == 0:
            json.dump(sorted(banned), open("odd_closure_banned.json", "w"))
            print(f"  [{time.time()-t0:.0f}s] {done} checks, required {len(required)}, banned {len(banned)}, in flight {inflight}", flush=True)
        if i in banned or i not in required:
            continue
        if r == 'n/a':
            cores[(i, key)] = []
            continue
        if r == 'unsat':
            if any(j in banned for j in core):
                submit(i, key); continue          # stale core: redo with current bans
            cores[(i, key)] = core
            for j in core:
                if j not in required:
                    required.add(j)
                    for kk in keys:
                        submit(j, kk)
            continue
        banned.add(i); required.discard(i)
        c = cands[i]
        print(f"  ban [{i}] {c['name']} {c['bound']} thr{c['thr']} ({r} in {key})", flush=True)
        json.dump(sorted(banned), open("odd_closure_banned.json", "w"))
        if i < ntg:
            print(f"FAILED: target family {c['name']} not provable from the pool", flush=True)
            for q in inqs: q.put(None)
            return 1
        for (j, kk), cr in list(cores.items()):
            if i in cr:
                del cores[(j, kk)]
                submit(j, kk)
    for q in inqs:
        q.put(None)
    out = [cands[i] for i in sorted(required)]
    json.dump(out, open("odd_closed.json", "w"))
    print(f"CLOSED: {len(required)} facts, {len(banned)} banned, {done} checks, {time.time()-t0:.0f}s", flush=True)
    for c in out:
        print(f"   {c['name']} {c['bound']} thr{c['thr']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
