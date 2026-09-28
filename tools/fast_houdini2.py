"""Fast Houdini for the even-grid diagonal invariants.

Hypotheses always present: H/V families + nonnegative contents (proven separately / inductive).
Candidates: E and Vd (must survive), named-difference templates with 1-2 terms, and Q.
Each goal is first checked with real-valued toppling counts (sound: no real counterexample means
no integer counterexample); only goals that fail that are checked over the integers.
"""
import itertools
import json
import os
import sys
import time

import z3

import houdini_diag as H
import cegar_diag as C


def make_pool(cache="fast_pool.json"):
    if os.path.exists(cache):
        return json.load(open(cache))
    temps = [(combo, t) for combo, t in C.build_pool() if len(combo) <= 2]
    K, Dd, V = C.simulate_states(list(range(10, 81, 2)))
    pool = C.mine_pool(temps, K, Dd, V)
    out = [{'name': '+'.join(f"{'-' if sg < 0 else ''}{n}" for n, sg in c['combo']),
            't': [[list(o), cf] for o, cf in c['t']], 'a': c['a'], 'b': c['b'], 'thr': c['thr']} for c in pool]
    json.dump(out, open(cache, 'w'))
    return out


def fixed():
    E = {'name': 'E*', 't': [[[0, -1], -1], [[0, 0], 1]], 'a': 2, 'b': -1, 'thr': 0}
    Vd = {'name': 'Vd*', 't': [[[0, 0], 1], [[1, 0], -1]], 'a': 2, 'b': -2, 'thr': 0}
    Q = {'name': 'Q', 't': [[[0, -1], 2], [[1, -1], -1], [[1, 0], 2], [[2, 0], -1], [[0, 0], -1], [[1, 1], -1]],
         'a': 4, 'b': -9, 'thr': 4}
    return [E, Vd, Q]


def tmpl(c):
    return tuple((tuple(o), cf) for o, cf in c['t'])


def build(prof, cands, live, sort):
    H.TSORT = sort
    w = H.Window(prof)
    if not w.ok:
        return w, None, None
    s = z3.Solver()
    s.add(w.cons + w.hv_constraints() + w.content_constraints())
    anchors = w.diag_anchors()
    for i in live:
        c = cands[i]
        t = tmpl(c)
        for j in anchors:
            ex = w.template_expr(t, j)
            if ex is None:
                continue
            kd = w.k - (w.d + j)
            s.add(z3.Implies(kd >= max(c['thr'], 1), ex <= c['a'] * kd + c['b']))
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
        return None
    goals = {}
    for i in live:
        c = cands[i]
        t = tmpl(c)
        ns = [N(o) for o, _ in t]
        if any(x is None for x in ns):
            continue
        kd = w.k - w.d
        goals[i] = z3.Implies(kd >= max(c['thr'], 1), sum(cf * n for (o, cf), n in zip(t, ns)) <= c['a'] * kd + c['b'])
    return w, s, goals


def work(args):
    prof, sl, nsl, cands, live, timeout = args
    import hashlib
    tag = "_".join(str(x).replace("'", "").replace(" ", "") for x in prof) + f"_s{sl}of{nsl}"
    lh = hashlib.sha1(",".join(map(str, sorted(live))).encode()).hexdigest()[:12]
    cache = f"fh2_result_{lh}_{tag}.json"
    if os.path.exists(cache):
        r = json.load(open(cache))
        return set(r[0]), r[1], r[2]
    res = _work(prof, sl, nsl, cands, live, timeout)
    json.dump([sorted(res[0]), res[1], res[2]], open(cache, "w"))
    return res


def _work(prof, sl, nsl, cands, live, timeout):
    w_r, s_r, g_r = build(prof, cands, live, z3.Real)
    if not w_r.ok:
        return set(), 0, 0
    w_i, s_i, g_i = build(prof, cands, live, z3.Int)
    s_r.set('timeout', 30000)
    s_i.set('timeout', timeout * 1000)
    mine = [i for n_, i in enumerate(sorted(g_i)) if n_ % nsl == sl]
    dropped, proven, lra = set(), set(), 0
    unknown = set()
    tag = "_".join(str(x).replace("'", "").replace(" ", "") for x in prof) + f"_s{sl}"
    log = open(f"fh2_{tag}.log", "a")
    t0 = time.time()
    for n_done, i in enumerate(mine):
        if i in dropped:
            continue
        s_r.push(); s_r.add(z3.Not(g_r[i])); r = s_r.check(); s_r.pop()
        if r == z3.unsat:
            proven.add(i); lra += 1
        else:
            s_i.push(); s_i.add(z3.Not(g_i[i])); r = s_i.check()
            if r == z3.unsat:
                s_i.pop(); proven.add(i)
            elif r == z3.sat:
                m = s_i.model(); s_i.pop()
                killed = {j for j in mine if j not in dropped and j not in proven
                          and z3.is_false(m.eval(g_i[j], model_completion=True))}
                dropped |= killed | {i}
            else:
                s_i.pop(); unknown.add(i)
        if n_done % 100 == 0:
            log.write(f"{time.time()-t0:6.0f}s {n_done}/{len(mine)} proven {len(proven)} (lra {lra}) dropped {len(dropped)}" + chr(10)); log.flush()
    # recheck unknowns with a long timeout; still unknown -> reported, never dropped
    s_i.set('timeout', 600000)
    still = set()
    for i in sorted(unknown - dropped):
        s_i.push(); s_i.add(z3.Not(g_i[i])); r = s_i.check()
        if r == z3.unsat:
            proven.add(i)
        elif r == z3.sat:
            dropped.add(i)
        else:
            still.add(i)
        s_i.pop()
    log.write(f"{time.time()-t0:6.0f}s done proven {len(proven)} (lra {lra}) dropped {len(dropped)} unresolved {len(still)}" + chr(10)); log.close()
    json.dump(sorted(still), open(f"fh2_unresolved_{tag}.json", "w"))
    return dropped, len(proven), lra


def main():
    import multiprocessing as mp
    cands = json.load(open("vd_repaired.json"))
    print(f"{len(cands)} candidates", flush=True)
    profs = [p for p in itertools.product(H.D_TOP, H.D_CEN)]
    heavy = {(('ge', 3), ('ge', 3)): 8, (('ge', 3), 2): 6, (2, ('ge', 3)): 6, (1, ('ge', 3)): 4, (('ge', 3), 1): 3}
    slices = {p: heavy.get(p, 2) for p in profs}
    live = set(range(len(cands)))
    rnd = 0
    with mp.Pool(14) as pool:
        while True:
            rnd += 1
            tasks = [(p, s, slices[p], cands, live, 60) for p in profs for s in range(slices[p])]
            res = pool.map(work, tasks, chunksize=1)
            dropped = set().union(*[r[0] for r in res])
            live -= dropped
            fx = [cands[i]['name'] for i in range(2) if i in live]
            print(f"round {rnd}: dropped {len(dropped)}, {len(live)} remain; fixed alive: {fx}; "
                  f"proven by LP {sum(r[2] for r in res)} of {sum(r[1] for r in res)}", flush=True)
            if not dropped:
                break
    json.dump([cands[i] for i in sorted(live)], open("fast2_live.json", "w"))
    print("E* and Vd* survive:", 0 in live and 1 in live, flush=True)


if __name__ == "__main__":
    main()
