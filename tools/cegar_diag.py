"""Counterexample-guided strengthening of the diagonal invariants (even grid).

Invariant set = H/V families + nonnegative contents (always) + a growing list of diagonal
templates, starting with E and Vd. Each round: check every diagonal template in every diagonal
window profile with z3. For each counterexample, pick a pool candidate that holds on all simulated
data but is violated by the counterexample state, add it, repeat.

Pool: sums of up to 3 named 2-cell differences near the diagonal, coefficients +-1,
bound alpha*(k-d) + beta, optionally only imposed where k - d >= thr.
"""
import itertools
import json
import sys
import time

import numpy as np
import z3

import houdini_diag as H

NAMED = {
    'E0': ((0, 0), (0, -1)), 'E1': ((1, 1), (1, 0)), 'Em': ((-1, -1), (-1, -2)), 'E2': ((2, 2), (2, 1)),
    'Vd0': ((0, 0), (1, 0)), 'Vd1': ((1, 1), (2, 1)), 'Vdm': ((-1, -1), (0, -1)),
    'V1': ((0, -1), (1, -1)), 'V2': ((1, 0), (2, 0)), 'V4': ((1, -1), (2, -1)),
    'H1': ((0, -1), (0, -2)), 'H2': ((1, 0), (1, -1)), 'H3': ((1, -1), (1, -2)),
    'G1': ((0, 0), (1, 1)), 'G0': ((-1, -1), (0, 0)),
}
NAMES = sorted(NAMED)
ALPHAS = range(0, 5)
THRS = (0, 3)


def template_of(combo):
    """combo: tuple of (name, sign) -> dict offset -> coef."""
    t = {}
    for name, sg in combo:
        a, b = NAMED[name]
        t[a] = t.get(a, 0) + sg
        t[b] = t.get(b, 0) - sg
    return tuple(sorted((o, c) for o, c in t.items() if c != 0))


def build_pool():
    combos = []
    for n in (1, 2, 3):
        for names in itertools.combinations(NAMES, n):
            for signs in itertools.product((1, -1), repeat=n):
                combos.append(tuple(zip(names, signs)))
    seen, temps = set(), []
    for c in combos:
        t = template_of(c)
        if t and t not in seen:
            seen.add(t)
            temps.append((c, t))
    return temps


def simulate_states(sizes):
    """Rows: (k, d, values of the named differences) for every round and every diagonal index."""
    rows_k, rows_d, rows_v = [], [], []
    for m in sizes:
        k = m // 2
        y, x = np.indices((m, m))
        dep = np.minimum(np.minimum(y, x), np.minimum(m - 1 - y, m - 1 - x)) + 1
        D = H.lap(2 * k * dep - dep * dep + dep)
        # canonical index arrays for every (d, offset)
        cells = sorted({o for a, b in NAMED.values() for o in (a, b)})
        idx = {}
        for o in cells:
            ys, xs, valid = [], [], []
            for d in range(k):
                c = H.canon(k, d + o[0], d + o[1])
                if c is None:
                    ys.append(0); xs.append(0); valid.append(0)
                else:
                    ys.append(c[0]); xs.append(c[1]); valid.append(1)
            idx[o] = (np.array(ys), np.array(xs), np.array(valid))
        T = np.zeros_like(D)
        while True:
            vals = {o: T[idx[o][0], idx[o][1]] * idx[o][2] for o in cells}
            diffs = np.stack([vals[NAMED[n][0]] - vals[NAMED[n][1]] for n in NAMES], axis=1)
            rows_k.append(np.full(k, k)); rows_d.append(np.arange(k)); rows_v.append(diffs)
            P = np.pad(T, 1)
            N = P[:-2, 1:-1] + P[2:, 1:-1] + P[1:-1, :-2] + P[1:-1, 2:]
            T2 = (D + N) // 4
            if (T2 == T).all():
                break
            T = T2
    return np.concatenate(rows_k), np.concatenate(rows_d), np.concatenate(rows_v)


def mine_pool(temps, K, Dd, V):
    kd = K - Dd
    cands = []
    col = {n: i for i, n in enumerate(NAMES)}
    for combo, t in temps:
        val = sum(sg * V[:, col[n]] for n, sg in combo)
        for thr in THRS:
            mask = kd >= max(thr, 1)                  # d <= k-1 always
            if not mask.any():
                continue
            for a in ALPHAS:
                beta = int((val[mask] - a * kd[mask]).max())
                cands.append({'combo': combo, 't': t, 'a': a, 'b': beta, 'thr': thr})
    return cands


def cand_holds_on(c, kval, dval, Tget):
    """Evaluate candidate at anchor d on a concrete state (Tget(offset) -> int or None)."""
    kd = kval - dval
    if kd < max(c['thr'], 1):
        return True
    s = 0
    for o, cf in c['t']:
        v = Tget(o)
        if v is None:
            return True                               # outside the window: can't evaluate
        s += cf * v
    return s <= c['a'] * kd + c['b']


def check_all(inv, profiles):
    """Check every invariant (as target) in every diagonal window. Returns list of counterexamples."""
    cexs = []
    for prof in profiles:
        w = H.Window(prof)
        if not w.ok:
            continue
        s = z3.Solver()
        s.set('timeout', 60000)
        s.add(w.cons + w.hv_constraints() + w.content_constraints())
        anchors = w.diag_anchors()
        for c in inv:
            for j in anchors:
                ex = w.template_expr(c['t'], j)
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
        for ci, c in enumerate(inv):
            ns = [N(o) for o, _ in c['t']]
            if any(x is None for x in ns):
                continue
            kd = w.k - w.d
            goal = z3.Implies(kd >= max(c['thr'], 1), sum(cf * n for (o, cf), n in zip(c['t'], ns)) <= c['a'] * kd + c['b'])
            s.push(); s.add(z3.Not(goal)); r = s.check()
            if r == z3.sat:
                m = s.model()
                kval = m.eval(w.k).as_long(); dval = m.eval(w.d).as_long()
                state = {}
                for o in H.OFFS:
                    if o in w.group:
                        state[o] = m.eval(w.T(o), model_completion=True).as_long()
                    else:
                        state[o] = 0 if not any(True for _ in [0]) else 0
                # sink offsets are 0; offsets are all within the window radius
                cexs.append({'prof': prof, 'target': ci, 'k': kval, 'd': dval, 'state': state})
            elif r == z3.unknown:
                cexs.append({'prof': prof, 'target': ci, 'unknown': True})
            s.pop()
    return cexs


def main():
    t0 = time.time()
    temps = build_pool()
    print(f"{len(temps)} pool templates; simulating ...", flush=True)
    K, Dd, V = simulate_states(list(range(10, 81, 2)))
    pool = mine_pool(temps, K, Dd, V)
    print(f"{len(pool)} pool candidates from {len(K)} anchor-states ({time.time()-t0:.0f}s)", flush=True)
    E = {'combo': (('E0', 1),), 't': template_of((('E0', 1),)), 'a': 2, 'b': -1, 'thr': 0}
    Vd = {'combo': (('Vd0', 1),), 't': template_of((('Vd0', 1),)), 'a': 2, 'b': -2, 'thr': 0}
    inv = [E, Vd]
    profiles = [p for p in itertools.product(H.D_TOP, H.D_CEN)]
    for it in range(1, 200):
        cexs = check_all(inv, profiles)
        print(f"iter {it}: {len(inv)} invariants, {len(cexs)} failing checks  ({time.time()-t0:.0f}s)", flush=True)
        if not cexs:
            print("ALL INVARIANTS INDUCTIVE", flush=True)
            json.dump(inv, open("cegar_inv.json", "w"), default=list)
            return 0
        added = 0
        for cx in cexs:
            if cx.get('unknown'):
                print("  unknown result at", cx['prof'], "target", cx['target'], flush=True)
                continue
            st, kv, dv = cx['state'], cx['k'], cx['d']
            # a candidate blocks the cex if it is violated at some diagonal anchor j in the window
            best = None
            for c in pool:
                if c in inv:
                    continue
                for j in range(-2, 3):
                    if not (0 <= dv + j <= kv - 1):
                        continue
                    def Tget(o, j=j):
                        oo = (o[0] + j, o[1] + j)
                        return st.get(oo)
                    if not cand_holds_on(c, kv, dv + j, Tget):
                        key = (len(c['combo']), c['thr'], c['a'], abs(c['b']))
                        if best is None or key < best[0]:
                            best = (key, c)
                        break
            if best is None:
                print(f"  NO POOL CANDIDATE blocks cex at {cx['prof']} target {inv[cx['target']]['combo']}", flush=True)
                continue
            if best[1] not in inv:
                inv.append(best[1]); added += 1
                print(f"  + {best[1]['combo']} <= {best[1]['a']}(k-d) + {best[1]['b']}"
                      f"{'  [k-d>=' + str(best[1]['thr']) + ']' if best[1]['thr'] else ''}", flush=True)
        if added == 0:
            print("stuck: no new candidates could be added", flush=True)
            json.dump(inv, open("cegar_inv_stuck.json", "w"), default=list)
            return 1
    return 1


if __name__ == "__main__":
    sys.exit(main())
