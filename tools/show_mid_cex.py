"""Print the counterexample for one midline target, given a list of extra facts (by name or index)."""
import sys, json, z3
import mid_closure as M
import invariant_engine as IE
tg = M.targets()
extra = json.loads(sys.argv[3]) if len(sys.argv) > 3 else []
cands = tg + extra
prof = eval(sys.argv[1]); target = int(sys.argv[2])
w = M.MidWindow(prof, cands, z3.Int)
W = None
# rebuild handles to T / prev / next for printing
import itertools
s = w.s
s.push(); s.add(z3.Not(w.goal[target])); r = s.check(*w.lit.values())
print(f"{cands[target]['name']} in {prof}: {r}")
if r == z3.sat:
    m = s.model()
    names = {str(d): m[d] for d in m.decls()}
    k = names.get('k'); y = names.get('a'); x = names.get('b')
    print(f"  k={k}  anchor=({y},{x})   [row -2 = k-3, row -1 = k-2, row 0 = k-1 (midline row)]")
    ww = IE.Window(M.GEOM, 'cell', prof)
    for lab, pre in (("prev", "P"), ("now ", ""), ("next", "N")):
        for a in (-2, -1, 0):
            row = []
            for b in range(-3, 4):
                kk = ww.key((a, b))
                if kk is None:
                    row.append("   ."); continue
                nm = pre + str(ww.var[kk])
                v = names.get(nm)
                row.append("   ?" if v is None else f"{v.as_long():4d}")
            print(f"  {lab} row {a:+d}:", "".join(row))
s.pop()
