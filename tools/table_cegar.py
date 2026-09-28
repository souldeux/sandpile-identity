"""Counterexample-guided search for TABLE invariants near the midline (even grid, two-round).

Quantities (bounded near the midline; horizontal steps are never used):
  z(o) grains, d(o) = T(o-(1,0)) - T(o) step into o from above, A(o) = T(o) - P(o) last-round topples.
A shape is a list of (quantity, offset); its table is the set of value tuples seen in simulations
(from the base pair (round 0, round 1) on). Anchors: cells (y, x) below the diagonal with
r = k-1-y in 0..RMAX; tables are mined separately per anchor class (r, x-class, s-class).
Only shapes whose next-round values are computable in a radius-3 window are used (z only at the
anchor, d and A within one cell of it, d only on rows 0 and +1).

Loop: check every live table (+ LA) in every window of the band; for each counterexample,
add library shapes whose mined table excludes the counterexample's current state.
"""
import itertools
import json
import os
import sys
import time
import multiprocessing as mp

import numpy as np
import z3

import invariant_engine as IE
from houdini_general import anchor_ok, start_pile
import even_check2 as EC

GEOM = IE.Geometry('even')
RMAX = 3
KMAX = int(os.environ.get('KMAX', 44))


def aclass(k, y, x):
    r = k - 1 - y
    s_ = y - x
    return (r, min(x, 2), min(s_, 3))


# shape library
CELLS1 = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]
BASIC = [('z', (0, 0))] + [('A', o) for o in CELLS1] + [('d', o) for o in CELLS1 if o[0] in (0, 1)]


def library():
    lib = []
    for n in (2, 3):
        for comb in itertools.combinations(BASIC, n):
            lib.append(tuple(comb))
    return lib


def simulate_tuples(shapes):
    """For each shape and anchor class, the set of tuples seen."""
    out = [dict() for _ in shapes]
    for k in range(RMAX + 3, KMAX + 1):
        D = start_pile('even', k)
        Tp = np.zeros_like(D)
        P = np.pad(Tp, 1)
        T = (D + P[:-2, 1:-1] + P[2:, 1:-1] + P[1:-1, :-2] + P[1:-1, 2:]) // 4
        anchors = [(y, x) for y in range(k - 1 - RMAX, k) for x in range(0, y)]
        while True:
            Pn = np.pad(T, 1)
            Z = D + Pn[:-2, 1:-1] + Pn[2:, 1:-1] + Pn[1:-1, :-2] + Pn[1:-1, 2:] - 4 * T
            def g(A_, y, x):
                c = GEOM.canon(k, y, x)
                return 0 if c is None else int(A_[c])
            def q(kind, y, x):
                if kind == 'z':
                    c = GEOM.canon(k, y, x)
                    return 0 if c is None else int(Z[c])
                if kind == 'd':
                    return g(T, y - 1, x) - g(T, y, x)
                return g(T, y, x) - g(Tp, y, x)
            for (y, x) in anchors:
                cl = aclass(k, y, x)
                cache = {}
                for si, sh in enumerate(shapes):
                    tup = []
                    for kind, o in sh:
                        key = (kind, o)
                        if key not in cache:
                            cache[key] = q(kind, y + o[0], x + o[1])
                        tup.append(cache[key])
                    out[si].setdefault(cl, set()).add(tuple(tup))
            T2 = (D + Pn[:-2, 1:-1] + Pn[2:, 1:-1] + Pn[1:-1, :-2] + Pn[1:-1, 2:]) // 4
            if (T2 == T).all():
                break
            Tp, T = T, T2
    return out


def build_window(prof, shapes, tabs, timeout):
    w = IE.Window(GEOM, 'cell', prof)
    if not w.ok:
        return None
    k = w.k
    prev = {key: z3.Int("P" + str(v)) for key, v in w.var.items()}
    TP = lambda o: z3.IntVal(0) if w.key(o) is None else prev[w.key(o)]
    def unreflected(o):
        c = w.cc.get(o)
        if c is None or c[0] is None:
            return False
        return all(p == (aa + o[0], bb + o[1]) for (kk, aa, bb), p in zip(w.smp, c))
    def anchor_cls(o):
        if not unreflected(o):
            return None
        cs = set()
        for (kk, aa, bb), p in zip(w.smp, w.cc[o]):
            Y, X = p
            if not (kk - 1 - RMAX <= Y <= kk - 1 and 0 <= X <= Y - 1):
                return None
            cs.add(aclass(kk, Y, X))
        return cs.pop() if len(cs) == 1 else None
    def qexpr(kind, o, Tn, Tb):
        if kind == 'd':
            a, b = Tn((o[0] - 1, o[1])), Tn(o)
            return None if a is None or b is None else a - b
        if kind == 'A':
            a, b = Tn(o), Tb(o)
            return None if a is None or b is None else a - b
        kk_ = w.key(o)
        if kk_ is None:
            return z3.IntVal(0)
        nb = [Tn((o[0] + a, o[1] + b)) for a, b in ((-1, 0), (1, 0), (0, -1), (0, 1))]
        c = Tn(o)
        if c is None or any(v is None for v in nb):
            return None
        return w.D(kk_) + sum(nb) - 4 * c
    def needed(o, sh):
        need = []
        for kind, off in sh:
            oo = (o[0] + off[0], o[1] + off[1])
            need.append(oo)
            if kind == 'd':
                need.append((oo[0] - 1, oo[1]))
            if kind == 'z':
                need += [(oo[0] + a, oo[1] + b) for a, b in ((-1, 0), (1, 0), (0, -1), (0, 1))]
        return all(q in w.cc for q in need)
    def texpr(si, o, cl, Tn, Tb):
        sh = shapes[si]
        allowed = tabs[si].get(cl)
        if not allowed or not needed(o, sh):
            return None
        vals = [qexpr(kind, (o[0] + off[0], o[1] + off[1]), Tn, Tb) for kind, off in sh]
        if any(v is None for v in vals):
            return None
        return z3.Or([z3.And([v == t for v, t in zip(vals, tup)]) for tup in allowed])
    s = z3.Solver()
    s.set('timeout', timeout * 1000)
    s.add(w.cons); s.add([v >= 0 for v in prev.values()])
    def valid(kind, o):
        return unreflected(o) and all(anchor_ok(kind, 'even', kk, p[0], p[1]) for (kk, _, _), p in zip(w.smp, w.cc[o]))
    for c in EC.single_families():
        for o in w.offs:
            if valid(c['kind'], o):
                for Tf in (w.T, TP):
                    terms = []
                    ok = True
                    for (dy, dx), cf in c['t']:
                        q = (o[0] + dy, o[1] + dx)
                        if q not in w.cc:
                            ok = False; break
                        terms.append(cf * Tf(q))
                    if ok:
                        Y, X = w.ay + o[0], w.ax + o[1]
                        ck, cy, cx, c0 = c['bound']
                        s.add(sum(terms) <= ck * k + cy * Y + cx * X + c0)
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
    nx, ncons = w.next_vars(w.R - 2)
    s.add(ncons)
    NT = lambda o: w.NT(nx, o)
    for o in w.offs:
        cl = anchor_cls(o)
        if cl is None:
            continue
        for si in range(len(shapes)):
            e = texpr(si, o, cl, w.T, TP)
            if e is not None:
                s.add(e)
    # LA on midline anchors
    def la(o, Tn, Tb):
        cells = [(o[0], o[1] - 1), o, (o[0], o[1] + 1)]
        if any(q not in w.cc for q in cells):
            return None
        vals = [Tn(q) for q in cells] + [Tb(o)]
        if any(v is None for v in vals):
            return None
        a, b, cc, bp = vals
        return a - 2 * b + cc + (b - bp) >= -1
    def is_mid(o):
        cl = anchor_cls(o)
        return cl is not None and cl[0] == 0
    for o in w.offs:
        if is_mid(o):
            e = la(o, w.T, TP)
            if e is not None:
                s.add(e)
    goals = []
    c0 = anchor_cls((0, 0))
    if c0 is not None:
        for si in range(len(shapes)):
            gexp = texpr(si, (0, 0), c0, NT, w.T)
            if gexp is not None:
                goals.append((si, gexp))
        if c0[0] == 0:
            g = la((0, 0), NT, w.T)
            if g is not None:
                goals.append(('LA', g))
    ctx = dict(w=w, TP=TP, NT=NT, qexpr=qexpr, anchor_cls=anchor_cls, c0=c0)
    return s, goals, ctx


def check(args):
    prof, shapes, tabs, timeout, done = args
    b = build_window(prof, shapes, tabs, timeout)
    if b is None:
        return prof, [], [], []
    s, goals, ctx = b
    fails, cexs, proven = [], [], []
    w, TP = ctx['w'], ctx['TP']
    skip = set()
    for name, g in goals:
        key = str(name) if name == 'LA' else json.dumps([list(q) for q in shapes[name]])
        if key in done or name in skip:
            continue
        s.push(); s.add(z3.Not(g)); r = s.check()
        if r == z3.unsat:
            proven.append(key)
        if r == z3.sat:
            m = s.model()
            # record the current-round values of every basic quantity at every anchor in the window
            per_anchor = []
            for o in w.offs:
                cl = ctx['anchor_cls'](o)
                if cl is None:
                    continue
                vals = {}
                for kind, off in BASIC:
                    e = ctx['qexpr'](kind, (o[0] + off[0], o[1] + off[1]), w.T, TP)
                    if e is not None:
                        vals[(kind, off)] = m.eval(e, model_completion=True).as_long()
                per_anchor.append((cl, vals))
            fails.append(name)
            cexs.append((name, ctx['c0'], per_anchor))
            for nm2, g2 in goals:                      # every other goal this state breaks
                if nm2 != name and nm2 not in skip and z3.is_false(m.eval(g2, model_completion=True)):
                    skip.add(nm2); fails.append(nm2)
        elif r != z3.unsat:
            fails.append((name, 'unknown'))
        s.pop()
    return prof, fails, cexs, proven


def main():
    nworkers = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    t0 = time.time()
    lib = library()
    print(f"library: {len(lib)} shapes; mining k <= {KMAX} ...", flush=True)
    if os.path.exists("lib_tabs.json"):
        raw = json.load(open("lib_tabs.json"))
        libtabs = [{tuple(json.loads(c)): set(map(tuple, v)) for c, v in d.items()} for d in raw]
    else:
        libtabs = simulate_tuples(lib)
        json.dump([{json.dumps(list(c)): sorted(v) for c, v in d.items()} for d in libtabs], open("lib_tabs.json", "w"))
    print(f"mined [{time.time()-t0:.0f}s]", flush=True)
    # start with the two midline tables of table_check (TA, TC) expressed as shapes
    start = [(('d', (0, -1)), ('z', (0, 0)), ('d', (0, 0)), ('A', (0, 0)), ('d', (0, 1))),
             (('z', (0, 0)), ('d', (0, 0)), ('A', (0, 0)), ('A', (-1, 0)))]
    extra_tabs = simulate_tuples(start)
    shapes = list(start)
    tabs = list(extra_tabs)
    if os.path.exists("cegar_shapes.json"):
        saved = [tuple((q[0], tuple(q[1])) for q in sh) for sh in json.load(open("cegar_shapes.json"))]
        for sh in saved:
            if sh not in shapes and sh in lib:
                shapes.append(sh); tabs.append(libtabs[lib.index(sh)])
        print(f"resumed with {len(shapes)} tables", flush=True)
    profs = [p for p in itertools.product(*IE.PROFILE_VALUES['cell'])
             if (p[3] in (0, 1, 2, 3)) and IE.Window(GEOM, 'cell', p).ok]
    print(f"{len(profs)} band windows", flush=True)
    cache = json.load(open("cegar_proven.json")) if os.path.exists("cegar_proven.json") else {}
    for it in range(1, 40):
        with mp.Pool(nworkers) as pool:
            res = pool.map(check, [(p, shapes, tabs, 120, set(cache.get(str(p), []))) for p in profs], chunksize=1)
        for p, _, _, pr in res:
            cache.setdefault(str(p), []).extend(pr)
        json.dump(cache, open("cegar_proven.json", "w"))
        fails = [(p, f) for p, f, _, _ in res if f]
        cexs = [c for _, _, cs, _ in res for c in cs]
        nla = sum(1 for _, f in fails for x in f if x == 'LA')
        print(f"iter {it}: {len(shapes)} tables, {len(fails)} windows failing, {len(cexs)} counterexamples, "
              f"LA failures {nla} [{time.time()-t0:.0f}s]", flush=True)
        if not fails:
            print("ALL TABLES AND LA INDUCTIVE", flush=True)
            json.dump([[list(map(list, sh)), {json.dumps(list(c)): sorted(v) for c, v in t.items()}] for sh, t in zip(shapes, tabs)],
                      open("table_invariant.json", "w"))
            return 0
        added = 0
        for name, cl0, anchors in cexs:
            # a library table at ANY anchor of the window that excludes the counterexample's state
            best = None
            for cl, vals in anchors:
                for li, sh in enumerate(lib):
                    if sh in shapes or not all(q in vals for q in sh):
                        continue
                    allowed = libtabs[li].get(cl)
                    if allowed is None:
                        continue
                    if tuple(vals[q] for q in sh) not in allowed:
                        key = (len(sh), sum(len(v) for v in libtabs[li].values()))
                        if best is None or key < best[0]:
                            best = (key, li)
            cl = cl0
            if best is None:
                print(f"  no library table blocks a counterexample to {name} in class {cl}", flush=True)
                continue
            li = best[1]
            if lib[li] not in shapes:
                shapes.append(lib[li]); tabs.append(libtabs[li]); added += 1
        print(f"  added {added} tables", flush=True)
        json.dump([[list(q) for q in sh] for sh in shapes], open("cegar_shapes.json", "w"))
        if added == 0:
            print("STUCK: counterexamples are not excluded by any library table (they look like reachable states)", flush=True)
            return 1
    return 1


if __name__ == "__main__":
    sys.exit(main())
