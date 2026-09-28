"""Final soundness check for the even-grid diagonal invariants.

The Houdini hypotheses always include the H/V families, which contain the Vd bound
(V1 at the pair just below the diagonal). So the surviving set S is a proof only if every
member of S AND the Vd bound are inductive under (S + H/V families + contents).
This script checks every member of S plus E and Vd in every diagonal window, over the
integers, with no timeout, and prints a counterexample for any failure.
"""
import itertools
import json
import sys
import time

import z3

import fast_houdini as F
import houdini_diag as H

live = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "fast_live.json"))
fx = F.fixed()
targets = [fx[0], fx[1]] + [c for c in live if c['name'] not in ('E*', 'Vd*')]
cands = fx[:2] + [c for c in live if c['name'] not in ('E*', 'Vd*')]
print(f"{len(live)} survivors; checking {len(targets)} targets (E, Vd first)", flush=True)
fails = 0
for prof in itertools.product(H.D_TOP, H.D_CEN):
    w, s, goals = F.build(prof, cands, set(range(len(cands))), z3.Int)
    if not w.ok:
        continue
    s.set('timeout', 300000)
    t0 = time.time()
    nfail = 0
    order = sorted(goals) if '--all' in sys.argv else [i for i in sorted(goals) if i < 2]
    for i in order:
        s.push(); s.add(z3.Not(goals[i])); r = s.check()
        if r != z3.unsat:
            nfail += 1
            fails += 1
            msg = f"  {prof} target {cands[i]['name']} <= {cands[i]['a']}(k-d)+{cands[i]['b']}: {r}"
            if r == z3.sat and i < 2:
                m = s.model()
                msg += f"  k,d=({m.eval(w.k)},{m.eval(w.d)})"
            print(msg, flush=True)
        s.pop()
    print(f"{prof}: {len(goals)} goals, {nfail} not proven ({time.time()-t0:.0f}s)", flush=True)
print("ALL PROVEN" if fails == 0 else f"{fails} goals not proven", flush=True)
