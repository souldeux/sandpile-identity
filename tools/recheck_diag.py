"""Re-add E and Vd on top of the Houdini survivors and check them with no timeout."""
import json, time, itertools, sys, z3
import houdini_diag as H
live = [(tuple((tuple(e[0]), e[1]) for e in t), a, b) for t, a, b in json.load(open("houdini_live.json"))]
E = (((0, -1), -1), ((0, 0), 1)); Vd = (((0, 0), 1), ((1, 0), -1))
cands = live + [(E, 2, -1), (Vd, 2, -2)]
CELLS = [(0, 0), (0, -1), (0, -2), (1, 0), (1, -1), (-1, -1), (1, 1), (2, 0), (-1, -2), (2, 1), (1, 2)]
for prof in itertools.product(H.D_TOP, H.D_CEN):
    w = H.Window(prof)
    if not w.ok:
        continue
    hyp = []
    for t, a, b in cands:
        for j in w.diag_anchors():
            ex = w.template_expr(t, j)
            if ex is not None:
                hyp.append(ex <= a * (w.k - (w.d + j)) + b)
    s = z3.Solver(); s.add(w.cons + w.hv_constraints() + w.content_constraints() + hyp)
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
    for name, (t, a, b) in (("E", (E, 2, -1)), ("Vd", (Vd, 2, -2))):
        goal = sum(c * N(o) for o, c in t) <= a * (w.k - w.d) + b
        s.push(); s.add(z3.Not(goal)); t0 = time.time(); r = s.check(); dt = time.time() - t0
        msg = f"{prof} {name}: {r} ({dt:.1f}s)"
        if r == z3.sat:
            m = s.model()
            kd = (m.eval(w.k), m.eval(w.d))
            loc = {o: m.eval(w.T(o), model_completion=True) for o in CELLS}
            nxt = {o: m.eval(N(o), model_completion=True) for o in [(0, 0), (0, -1), (1, 0)] if N(o) is not None}
            msg += f"\n    k,d = {kd}\n    T now  = { {o: str(v) for o, v in loc.items()} }\n    T next = { {o: str(v) for o, v in nxt.items()} }"
        print(msg, flush=True)
        s.pop()
