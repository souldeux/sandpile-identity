"""Finish the even-grid proof: shrink the candidate set until every member is proven.

Start: vd_repaired.json minus everything the saved fast_houdini2 results dropped.
Each round, every live candidate is checked (real-valued pre-check, then integers with a
2-minute limit) in every diagonal window, assuming all live candidates + H/V families
(which include the Vd bound) + nonnegative contents. Anything not proven is dropped
(sound). Stop when a round drops nothing. The result is a proof only if E* and Vd* are
still live at the end.
"""
import glob
import hashlib
import itertools
import json
import os
import sys
import time

import z3

import fast_houdini as F
import houdini_diag as H


def task(args):
    prof, sl, nsl, cands, live, tmo = args
    tag = "_".join(str(x).replace("'", "").replace(" ", "") for x in prof) + f"_s{sl}of{nsl}"
    lh = hashlib.sha1(",".join(map(str, sorted(live))).encode()).hexdigest()[:12]
    cache = f"ef_result_{lh}_{tag}.json"
    if os.path.exists(cache):
        return set(json.load(open(cache)))
    br = F.build(prof, cands, live, z3.Real)
    if br[1] is None:
        json.dump([], open(cache, "w")); return set()
    wi, si, gi = F.build(prof, cands, live, z3.Int)
    wr, sr, gr = br
    sr.set('timeout', 30000); si.set('timeout', tmo * 1000)
    mine = [i for n, i in enumerate(sorted(gi)) if n % nsl == sl]
    bad = set()
    log = open(f"ef_{tag}.log", "a"); t0 = time.time()
    for n, i in enumerate(mine):
        if i in bad:
            continue
        sr.push(); sr.add(z3.Not(gr[i])); r = sr.check(); sr.pop()
        if r == z3.unsat:
            continue
        si.push(); si.add(z3.Not(gi[i])); r = si.check()
        if r == z3.sat:
            m = si.model(); si.pop()
            bad |= {j for j in mine if j not in bad and z3.is_false(m.eval(gi[j], model_completion=True))} | {i}
        else:
            si.pop()
            if r != z3.unsat:
                bad.add(i)
        if n % 100 == 0:
            log.write(f"{time.time()-t0:6.0f}s {n}/{len(mine)} not proven {len(bad)}" + chr(10)); log.flush()
    log.write(f"{time.time()-t0:6.0f}s done, not proven {len(bad)}" + chr(10)); log.close()
    json.dump(sorted(bad), open(cache, "w"))
    return bad


def main():
    import multiprocessing as mp
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    cands = json.load(open("vd_repaired.json"))
    dropped = set()
    for f in glob.glob("fh2_result_*.json"):
        dropped |= set(json.load(open(f))[0])
    live = set(range(len(cands))) - dropped
    print(f"{len(cands)} candidates, starting with {len(live)} live; E*,Vd* live: {0 in live},{1 in live}", flush=True)
    profs = [p for p in itertools.product(H.D_TOP, H.D_CEN)]
    heavy = {(('ge', 3), ('ge', 3)): 10, (('ge', 3), 2): 4, (2, ('ge', 3)): 4, (1, ('ge', 3)): 3, (('ge', 3), 1): 3}
    rnd = 0
    with mp.Pool(workers) as pool:
        while True:
            rnd += 1
            tasks = [(p, s, heavy.get(p, 2), cands, live, 120) for p in profs for s in range(heavy.get(p, 2))]
            bad = set().union(*pool.map(task, tasks, chunksize=1))
            live -= bad
            print(f"round {rnd}: dropped {len(bad)}, {len(live)} live; E*,Vd* live: {0 in live},{1 in live}", flush=True)
            if not bad:
                break
    json.dump([cands[i] for i in sorted(live)], open("even_final.json", "w"))
    print("RESULT:", "E* and Vd* proven inductive with", len(live), "invariants" if (0 in live and 1 in live)
          else "E*/Vd* lost", flush=True)


if __name__ == "__main__":
    main()
