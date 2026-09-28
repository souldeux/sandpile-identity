"""Which candidates does the Vd proof actually use? (unsat cores), and are those provable?"""
import json, sys, time, z3
import houdini_diag as H
import fast_houdini as F

cands = json.load(open("vd_repaired.json"))
prof = eval(sys.argv[1]) if len(sys.argv) > 1 else (('ge', 3), ('ge', 3))


def tracked(prof, cands, target):
    H.TSORT = z3.Int
    w = H.Window(prof)
    s = z3.Solver()
    s.add(w.cons + w.hv_constraints() + w.content_constraints())
    lits = {}
    anchors = w.diag_anchors()
    for i, c in enumerate(cands):
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
            lits[i] = p
    nx = {}
    for o in w.group:
        if max(abs(o[0]), abs(o[1])) <= 2 and not any(w.same(o, o2) for o2 in nx):
            n, cc = w.nxt(o, f"n_{o[0]}_{o[1]}".replace('-', 'm')); s.add(cc); nx[o] = n
    def N(o):
        if o not in w.group:
            return z3.IntVal(0)
        for o2, v in nx.items():
            if w.same(o, o2):
                return v
    c = cands[target]
    t = F.tmpl(c)
    kd = w.k - w.d
    goal = z3.Implies(kd >= max(c['thr'], 1), sum(cf * N(o) for (o, cf), _ in zip(t, t)) <= c['a'] * kd + c['b'])
    s.add(z3.Not(goal))
    return s, lits


TARGET = int(sys.argv[2]) if len(sys.argv) > 2 else 1
s, lits = tracked(prof, cands, TARGET)
s.set('timeout', 600000)
t0 = time.time()
r = s.check(*lits.values())
print(f"target {TARGET} ({cands[TARGET]['name']} <= {cands[TARGET]['a']}(k-d)+{cands[TARGET]['b']}) in {prof}: {r} ({time.time()-t0:.0f}s)", flush=True)
if r == z3.unsat:
    core = [int(str(p)[1:]) for p in s.unsat_core()]
    print(f"core size {len(core)}:", flush=True)
    for i in sorted(core):
        c = cands[i]
        print(f"   [{i}] {c['name']} <= {c['a']}(k-d)+{c['b']}" + (f"  [k-d>={c['thr']}]" if c['thr'] else ""), flush=True)
    json.dump(sorted(core), open(f"core_{TARGET}_{len(core)}.json", "w"))
