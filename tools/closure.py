"""Core-guided backward closure for the even-grid diagonal invariants.

required := {E, Vd}. For each required fact and each diagonal window profile, prove it with
all non-banned pool facts available as tracked hypotheses (plus the H/V families and
nonnegative contents, always). UNSAT: record the core and require its members. SAT or
unknown: ban the fact and re-prove every fact whose recorded core used it. At the end,
every required fact is proven in every profile from a core inside the required set,
so required (+ background) is an inductive invariant.
"""
import itertools
import json
import os
import sys
import time

import z3

import fast_houdini as F
import houdini_diag as H

PROFS = [p for p in itertools.product(H.D_TOP, H.D_CEN)]


class Prof:
    """One window profile with all pool facts added as tracked (retractable) hypotheses."""
    def __init__(self, prof, pool, sort=z3.Int):
        H.TSORT = sort
        w = H.Window(prof)
        self.ok = w.ok
        if not w.ok:
            return
        self.w = w
        s = z3.Solver()
        s.add(w.cons + w.hv_constraints() + w.content_constraints())
        self.lit = {}
        anchors = w.diag_anchors()
        for i, c in enumerate(pool):
            t = F.tmpl(c)
            p = z3.Bool(f"p{i}")
            used = False
            for j in anchors:
                ex = w.template_expr(t, j)
                if ex is None:
                    continue
                kd = w.k - (w.d + j)
                s.add(z3.Implies(p, z3.Implies(kd >= max(c['thr'], 1), ex <= c['a'] * kd + c['b'])))
                used = True
            if used:
                self.lit[i] = p
        nx = {}
        for o in w.group:
            if max(abs(o[0]), abs(o[1])) <= 2 and not any(w.same(o, o2) for o2 in nx):
                n, cc = w.nxt(o, f"n_{o[0]}_{o[1]}".replace('-', 'm')); s.add(cc); nx[o] = n
        self.nx = nx
        self.s = s
        self.pool = pool

    def N(self, o):
        w = self.w
        if o not in w.group:
            return z3.IntVal(0)
        for o2, v in self.nx.items():
            if w.same(o, o2):
                return v
        return None

    def check(self, i, banned, timeout):
        c = self.pool[i]
        t = F.tmpl(c)
        ns = [self.N(o) for o, _ in t]
        if any(x is None for x in ns):
            return 'n/a', []
        kd = self.w.k - self.w.d
        goal = z3.Implies(kd >= max(c['thr'], 1), sum(cf * n for (o, cf), n in zip(t, ns)) <= c['a'] * kd + c['b'])
        self.s.push()
        self.s.add(z3.Not(goal))
        self.s.set('timeout', timeout * 1000)
        assum = [p for j, p in self.lit.items() if j not in banned and j != i] + \
                ([self.lit[i]] if i in self.lit and i not in banned else [])
        r = self.s.check(*assum)
        core = []
        if r == z3.unsat:
            core = [int(str(p)[1:]) for p in self.s.unsat_core()]
        self.s.pop()
        return str(r), core


def main():
    pool = F.fixed()[:2] + F.make_pool()
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    print(f"pool {len(pool)}; building {len(PROFS)} profiles ...", flush=True)
    t0 = time.time()
    profs = {p: Prof(p, pool) for p in PROFS}
    profs = {p: v for p, v in profs.items() if v.ok}
    rprofs = {p: Prof(p, pool, z3.Real) for p in profs}
    print(f"built in {time.time()-t0:.0f}s", flush=True)
    required = {0, 1}
    banned = set()
    if os.path.exists("closure_banned.json"):
        banned = set(json.load(open("closure_banned.json")))
        print(f"preloaded {len(banned)} bans", flush=True)
    cores = {}                      # (fact, prof) -> core list
    todo = []                       # de-duplicated work list
    queued = set()
    def push(item):
        if item not in queued:
            queued.add(item); todo.append(item)
    for i in required:
        for p in profs:
            push((i, p))
    nchecks = 0
    while todo:
        i, p = todo.pop()
        queued.discard((i, p))
        nchecks += 1
        if nchecks % 50 == 0:
            json.dump(sorted(banned), open("closure_banned.json", "w"))
            print(f"    [{time.time()-t0:.0f}s] checks {nchecks}, required {len(required)}, banned {len(banned)}, pending {len(todo)}", flush=True)
        if i in banned:
            continue
        r, core = rprofs[p].check(i, banned, 30)      # real relaxation: its UNSAT core is valid for integers
        if r != 'unsat' and r != 'n/a':
            r, core = profs[p].check(i, banned, timeout)
        if r == 'n/a':
            cores[(i, p)] = []
            continue
        if r == 'unsat':
            cores[(i, p)] = core
            for j in core:
                if j not in required:
                    required.add(j)
                    for q in profs:
                        push((j, q))
            continue
        # not provable from the non-banned pool: ban it, re-prove dependents
        banned.add(i)
        required.discard(i)
        name = pool[i]['name']
        print(f"  ban [{i}] {name} <= {pool[i]['a']}(k-d)+{pool[i]['b']}"
              f"{' [k-d>=' + str(pool[i]['thr']) + ']' if pool[i]['thr'] else ''} ({r} in {p})", flush=True)
        if i in (0, 1):
            print("FAILED: a target fact is not provable from this pool", flush=True)
            json.dump({'banned': sorted(banned)}, open("closure_failed.json", "w"))
            return 1
        json.dump(sorted(banned), open("closure_banned.json", "w"))
        for (j, q), cr in list(cores.items()):
            if i in cr:
                del cores[(j, q)]
                push((j, q))
        print(f"    required {len(required)}, banned {len(banned)}, pending {len(todo)}", flush=True)
    print(f"CLOSED: {len(required)} facts, each proven in every profile from facts in the set "
          f"({len(banned)} banned) in {time.time()-t0:.0f}s", flush=True)
    out = [pool[i] for i in sorted(required)]
    json.dump(out, open("even_closed.json", "w"))
    for c in out:
        print(f"   {c['name']} <= {c['a']}(k-d)+{c['b']}" + (f"  [k-d>={c['thr']}]" if c['thr'] else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
