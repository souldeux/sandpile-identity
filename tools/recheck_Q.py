"""E, Vd and the six-cell family Q, checked exactly with z3 on top of the H/V families and contents.
Q(d): [T(d,d-1)-T(d+1,d-1)] + [T(d+1,d)-T(d+2,d)] - [T(d,d)-T(d,d-1)] - [T(d+1,d+1)-T(d+1,d)] <= 4(k-d)-9,
imposed only where k - d >= 4."""
import itertools, time, z3
import houdini_diag as H
E = (((0, -1), -1), ((0, 0), 1))
Vd = (((0, 0), 1), ((1, 0), -1))
Q = (((0, -1), 2), ((1, -1), -1), ((1, 0), 2), ((2, 0), -1), ((0, 0), -1), ((1, 1), -1))
FAM = [("E", E, 2, -1, 0), ("Vd", Vd, 2, -2, 0), ("Q", Q, 4, -9, 4)]   # (name, template, alpha, beta, min k-d)
CELLS = [(0, 0), (0, -1), (0, -2), (1, 0), (1, -1), (-1, -1), (1, 1), (2, 0), (-1, -2), (2, 1), (1, 2), (2, -1), (3, 0), (2, 2)]
bad = 0
for prof in itertools.product(H.D_TOP, H.D_CEN):
    w = H.Window(prof)
    if not w.ok:
        continue
    kc, dc = w.smp[0]
    s = z3.Solver()
    s.add(w.cons + w.hv_constraints() + w.content_constraints())
    for name, t, a, b, mind in FAM:
        for j in w.diag_anchors():
            ex = w.template_expr(t, j)
            if ex is None:
                continue
            kd = w.k - (w.d + j)
            s.add(z3.Implies(kd >= mind, ex <= a * kd + b))
    nx = {}
    for o in w.group:
        if max(abs(o[0]), abs(o[1])) <= 2 and not any(w.same(o, o2) for o2 in nx):
            n, c = w.nxt(o, f"n_{o[0]}_{o[1]}".replace('-', 'm')); s.add(c); nx[o] = n
    def N(o):
        if o not in w.group:
            return z3.IntVal(0)
        for o2, v in nx.items():
            if w.same(o, o2):
                return v
    for name, t, a, b, mind in FAM:
        ns = [N(o) for o, _ in t]
        if any(x is None for x in ns):
            print(f"{prof} {name}: cells outside radius 2 (skipped)"); continue
        kd = w.k - w.d
        goal = z3.Implies(kd >= mind, sum(c * n for (o, c), n in zip(t, ns)) <= a * kd + b)
        s.push(); s.add(z3.Not(goal)); t0 = time.time(); r = s.check(); dt = time.time() - t0
        line = f"{prof} {name}: {r} ({dt:.1f}s)"
        if r != z3.unsat:
            bad += 1
            if r == z3.sat:
                m = s.model()
                line += f"  k,d=({m.eval(w.k)},{m.eval(w.d)})  now={ {o: str(m.eval(w.T(o), model_completion=True)) for o in CELLS} }"
        print(line, flush=True)
        s.pop()
print("FAILURES:", bad)
