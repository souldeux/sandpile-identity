"""Repair loop for Vd: repeatedly take Vd's counterexamples and add back every pool candidate
(true on all simulated data) that the counterexample violates; recheck until Vd is proven or
no pool candidate blocks the counterexample. New candidates must themselves be proven afterwards."""
import json, sys, itertools, z3
import fast_houdini as F, houdini_diag as H
pool = F.make_pool()
live = json.load(open("fast_live_partial.json"))
fx = F.fixed()
inv = fx[:2] + [c for c in live if c['name'] not in ('E*', 'Vd*')]
names = {(c['name'], c['a'], c['b'], c['thr']) for c in inv}
def key(c): return (c['name'], c['a'], c['b'], c['thr'])
PROFS = [(('ge', 3), ('ge', 3)), (('ge', 3), 1), (('ge', 3), 2)]
for it in range(1, 30):
    added = 0; open_ = 0
    for prof in PROFS:
        w, s, goals = F.build(prof, inv, set(range(len(inv))), z3.Int)
        s.set('timeout', 300000)
        s.push(); s.add(z3.Not(goals[1])); r = s.check()
        if r == z3.unsat:
            print(f"iter {it} {prof}: Vd proven", flush=True); s.pop(); continue
        if r != z3.sat:
            print(f"iter {it} {prof}: Vd unknown", flush=True); s.pop(); open_ += 1; continue
        open_ += 1
        m = s.model(); s.pop()
        kv, dv = m.eval(w.k).as_long(), m.eval(w.d).as_long()
        def Tv(o):
            return m.eval(w.T(o), model_completion=True).as_long() if o in w.group else (0 if o in H.OFFS else None)
        blockers = []
        for c in pool:
            if key(c) in names:
                continue
            for j in range(-2, 3):
                dd = dv + j
                kd = kv - dd
                if not (0 <= dd <= kv - 1) or kd < max(c['thr'], 1):
                    continue
                vals = [Tv((o[0] + j, o[1] + j)) for o, cf in c['t']]
                if any(v is None for v in vals):
                    continue
                if sum(cf * v for (o, cf), v in zip(c['t'], vals)) > c['a'] * kd + c['b']:
                    blockers.append(c); break
        for c in blockers:
            inv.append(c); names.add(key(c)); added += 1
        print(f"iter {it} {prof}: Vd cex k={kv} d={dv}; added {len(blockers)} blocking candidates", flush=True)
    if open_ == 0:
        print("Vd PROVEN in all three profiles; invariant set size", len(inv), flush=True)
        json.dump(inv, open("vd_repaired.json", "w")); break
    if added == 0:
        print("no pool candidate blocks the remaining counterexamples", flush=True)
        json.dump(inv, open("vd_repaired.json", "w")); break
