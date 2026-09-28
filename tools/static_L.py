"""Static attack on (L): does the final state alone force seams >= 1?

Final LBR odometer a on a window next to the midline (generic arm position: away from the border,
the diagonal and the centre, so D = 2 there and e = 2 - (L a)). Constraints:
  * stability 0 <= e <= 3 on window cells whose neighbours are all in the window (or mirrored)
  * the proven (U) bounds H0, H1, V0, V1' (at the end of the avalanche)
  * mirror symmetry a(k, x) = a(k-1, x)
  * recurrence: no forbidden subconfiguration inside the window (+ mirror), added lazily (CEGAR)
Goal: s = 2 + a(j-1) - 2a(j) + a(j+1) <= 0 at the centre column of the midline row.
UNSAT means (L) holds at generic arm cells from (U) + stability + recurrence alone.
"""
import sys, itertools
import z3

R = int(sys.argv[1]) if len(sys.argv) > 1 else 3      # rows above the midline row
C = int(sys.argv[2]) if len(sys.argv) > 2 else 3      # columns each side
rows = range(0, R + 1)            # r = 0 is the midline row y = k-1; r grows upward
cols = range(-C, C + 1)

a = {(r, c): z3.Int(f"a_{r}_{c}") for r in rows for c in cols}
kx = z3.Int("kx")                 # k - x at column 0 (distance to the centre column)
kx_min = C + R + 3                # generic: well away from the diagonal and the centre
s = z3.Solver()
s.add(kx >= kx_min)
for v in a.values():
    s.add(v >= 0)

def A(r, c):
    if r == -1:                   # the mirror row below the midline row
        return a[(0, c)]
    return a.get((r, c))

def e_of(r, c):
    nb = [A(r - 1, c), A(r + 1, c), A(r, c - 1), A(r, c + 1)]
    if any(v is None for v in nb):
        return None
    return 2 - 4 * a[(r, c)] + sum(nb)

E = {}
for r in rows:
    for c in cols:
        e = e_of(r, c)
        if e is not None:
            E[(r, c)] = e
            s.add(e >= 0, e <= 3)

# (U) at the end: rows y = k-1-r, T(y-1,x) is the cell above (r+1)
for r in rows:
    for c in cols:
        if (r, c + 1) in a:
            h = a[(r, c + 1)] - a[(r, c)]
            s.add(h >= 0, h <= 2 * (kx - c) - 3)
        if (r + 1, c) in a:
            v = a[(r + 1, c)] - a[(r, c)]
            s.add(v >= 0, v <= 2 * (r + 1))

import os
GOAL=os.environ.get("GOAL","seam")
LEFT=int(os.environ.get("LEFT","0"))
seam = 2 + a[(0, -1)] - 2 * a[(0, 0)] + a[(0, 1)]
dlt = lambda c: a[(1, c)] - a[(0, c)]
sm = lambda c: 2 + a[(0, c-1)] - 2 * a[(0, c)] + a[(0, c+1)]
if GOAL == "seam": s.add(seam <= 0)
else: s.add(dlt(0) >= 2)
# induction along the row from the border: facts already established at columns left of 0
if LEFT:
    for c in cols:
        if c < 0:
            s.add(dlt(c) <= 1)
            if c > -C: s.add(sm(c) >= 1)


cells = list(E)                   # cells with a known grain count (mirror cells share them)

def forbidden_in(model):
    """Largest forbidden set within the known cells + their mirrors, by local burning."""
    ev = {c: model.eval(E[c]).as_long() for c in cells}
    S = set((r, c, m) for (r, c) in cells for m in ((0,) if r > 0 else (0, 1)))
    def nbrs(p):
        r, c, m = p
        out = [(r + 1, c, m), (r, c - 1, m), (r, c + 1, m)]
        out.append((r - 1, c, m) if r > 0 else (0, c, 1 - m))
        return out
    changed = True
    while changed:
        changed = False
        for p in list(S):
            if ev[(p[0], p[1])] >= sum(q in S for q in nbrs(p)):
                S.discard(p); changed = True
    return S, nbrs

it = 0
while True:
    it += 1
    res = s.check()
    if res == z3.unsat:
        print(f"UNSAT after {it} rounds: (L) forced at generic arm cells (R={R}, C={C})")
        break
    if res != z3.sat:
        print("unknown", s.reason_unknown()); break
    mdl = s.model()
    F, nbrs = forbidden_in(mdl)
    if not F:
        print(f"SAT after {it} rounds: static counterexample with no forbidden set in the window")
        for r in reversed(rows):
            print("  a:", [mdl.eval(a[(r, c)]).as_long() for c in cols],
                  " e:", [mdl.eval(E[(r, c)]).as_long() if (r, c) in E else '.' for c in cols])
        print("  kx =", mdl.eval(kx))
        break
    # block: some cell of F must hold at least its F-degree
    s.add(z3.Or([E[(p[0], p[1])] >= sum(q in F for q in nbrs(p)) for p in F]))
    if it % 50 == 0:
        print(f"  {it} blocking rounds", flush=True)
