"""Houdini search for an inductive invariant that proves the diagonal bounds
    E(d)  = T(d,d) - T(d,d-1)   <= 2(k-d) - 1
    Vd(d) = T(d,d) - T(d+1,d)   <= 2(k-d) - 2
for the parallel stabilization of the Le Borgne-Rossin pile (see check_invariants.py).

Candidates are linear inequalities  sum_o c_o * T(d + o) <= alpha*(k - d) + beta  over offsets o
around a diagonal cell (d, d), with beta mined from simulations (tightest value that holds at
every round). Houdini: assume all current candidates (plus the H/V families of
check_invariants.py) at round t, keep only candidates provable at round t+1, repeat.
"""
import itertools
import json
import os
import random
import sys

import numpy as np
import z3

K0 = 8
TSORT = z3.Int          # set to z3.Real for the linear-relaxation pre-check
R = 3                                   # window radius around the anchor (d, d)
OFFS = [(a, b) for a in range(-R, R + 1) for b in range(-R, R + 1)]
D_TOP = [0, 1, 2, ('ge', 3)]            # d
D_CEN = [0, 1, 2, ('ge', 3)]            # k - 1 - d
TEMPLATE_CELLS = [(0, 0), (0, -1), (0, -2), (1, 0), (1, -1), (-1, -1), (1, 1), (2, 0), (-1, -2)]


def lap(f):
    p = np.pad(f, 1)
    return 4 * f - p[:-2, 1:-1] - p[2:, 1:-1] - p[1:-1, :-2] - p[1:-1, 2:]


def canon(k, Y, X):
    if Y < 0 or X < 0 or Y > 2 * k - 1 or X > 2 * k - 1:
        return None
    if Y >= k:
        Y = 2 * k - 1 - Y
    if X >= k:
        X = 2 * k - 1 - X
    if X > Y:
        X, Y = Y, X
    return (Y, X)


def val(T, k, d, o):
    c = canon(k, d + o[0], d + o[1])
    return 0 if c is None else int(T[c])


# ---------------------------------------------------------------- templates and mining
def make_templates():
    cells = TEMPLATE_CELLS
    temps = set()
    for n in (2, 3):
        for sup in itertools.combinations(cells, n):
            for coefs in itertools.product((-2, -1, 1, 2), repeat=n):
                if sum(coefs) != 0 or max(abs(c) for c in coefs) == 2 and n == 2:
                    continue
                g = np.gcd.reduce([abs(c) for c in coefs])
                if g != 1:
                    continue
                temps.add(tuple(sorted(zip(sup, coefs))))
    return sorted(temps)


def mine(templates, sizes):
    """For each template and alpha in 0..4: beta = max over data of value - alpha (k - d)."""
    best = {t: {a: -10**9 for a in range(4)} for t in templates}
    for m in sizes:
        k = m // 2
        y, x = np.indices((m, m))
        dep = np.minimum(np.minimum(y, x), np.minimum(m - 1 - y, m - 1 - x)) + 1
        D = lap(2 * k * dep - dep * dep + dep)
        T = np.zeros_like(D)
        while True:
            for d in range(k):
                vals = {o: val(T, k, d, o) for o in TEMPLATE_CELLS}
                for t in templates:
                    v = sum(c * vals[o] for o, c in t)
                    b = best[t]
                    for a in range(4):
                        w = v - a * (k - d)
                        if w > b[a]:
                            b[a] = w
            P = np.pad(T, 1)
            N = P[:-2, 1:-1] + P[2:, 1:-1] + P[1:-1, :-2] + P[1:-1, 2:]
            T2 = (D + N) // 4
            if (T2 == T).all():
                break
            T = T2
    cands = []
    for t in templates:
        for a in range(4):
            cands.append((t, a, best[t][a]))
    return cands


# ---------------------------------------------------------------- symbolic window
def satisfies(v, spec):
    return v >= spec[1] if isinstance(spec, tuple) else v == spec


def samples(prof, n=8):
    rnd = random.Random(7)
    out = []
    for _ in range(50000):
        k = rnd.randint(K0, K0 + 60)
        d = rnd.randint(0, k - 1)
        if satisfies(d, prof[0]) and satisfies(k - 1 - d, prof[1]):
            out.append((k, d))
            if len(out) >= n:
                break
    return out


class Window:
    def __init__(self, prof):
        self.prof = prof
        self.smp = samples(prof)
        self.ok = len(self.smp) >= 4
        if not self.ok:
            return
        k, d = z3.Ints('k d')
        self.k, self.d = k, d
        self.base = [k >= K0, d >= 0, d <= k - 1]
        for var, spec in ((d, prof[0]), (k - 1 - d, prof[1])):
            self.base.append(var >= spec[1] if isinstance(spec, tuple) else var == spec)
        # group offsets by canonical cell (affine in k, d within a profile)
        self.group = {}
        reps = []
        for o in OFFS:
            cs = [canon(kk, dd + o[0], dd + o[1]) for kk, dd in self.smp]
            if cs[0] is None:
                assert all(c is None for c in cs), (prof, o)
                continue
            rel = [(c[0] - dd, c[1] - dd, c[0] - kk, c[1] - kk) for c, (kk, dd) in zip(cs, self.smp)]
            for r in reps:
                if [(canon(kk, dd + r[0], dd + r[1])) for kk, dd in self.smp] == cs:
                    self.group[o] = self.group[r]
                    break
            else:
                reps.append(o)
                self.group[o] = TSORT(f"T_{o[0]}_{o[1]}".replace('-', 'm'))
        # every sink/reflection/swap/diagonal decision must be the same on all samples
        for o in OFFS:
            sig = set()
            for kk, dd in self.smp:
                Y, X = dd + o[0], dd + o[1]
                sink = Y < 0 or X < 0
                Yr = 2 * kk - 1 - Y if Y >= kk else Y
                Xr = 2 * kk - 1 - X if X >= kk else X
                sig.add((sink, Y >= kk, X >= kk, Xr > Yr, Xr == Yr))
            assert len(sig) == 1, f"profile {prof} too coarse at offset {o}"
        # symbolic canonical coordinates of each representative (from sample-0 branch decisions)
        self.coord = {}
        kk, dd = self.smp[0]
        for o in OFFS:
            if o not in self.group:
                continue
            Y, X = d + o[0], d + o[1]
            Yn, Xn = dd + o[0], dd + o[1]
            if Yn >= kk:
                Y, Yn = 2 * k - 1 - Y, 2 * kk - 1 - Yn
            if Xn >= kk:
                X, Xn = 2 * k - 1 - X, 2 * kk - 1 - Xn
            if Xn > Yn:
                X, Y, Xn, Yn = Y, X, Yn, Xn
            self.coord[o] = (Y, X, Yn == Xn)
        self.cons = list(self.base) + [v >= 0 for v in set(self.group.values())]

    def T(self, o):
        return self.group.get(o, z3.IntVal(0))

    def nxt(self, o, name):
        Y, X, diag = self.coord[o]
        Dv = 4 * (self.k - Y) if diag else z3.IntVal(2)
        n = TSORT(name)
        S = Dv + sum(self.T((o[0] + a, o[1] + b)) for a, b in ((-1, 0), (1, 0), (0, -1), (0, 1)))
        return n, [4 * n <= S, S <= 4 * n + 3]

    def same(self, o1, o2):
        return all(canon(kk, dd + o1[0], dd + o1[1]) == canon(kk, dd + o2[0], dd + o2[1]) for kk, dd in self.smp)

    def canon_rel(self, o):
        return [canon(kk, dd + o[0], dd + o[1]) for kk, dd in self.smp]

    def hv_constraints(self):
        """H0/H1/V0/V1 on every pair inside the window, and T(y,0) <= 2k-1."""
        cons = []
        reps = {}
        for o in self.group:
            key = tuple(self.canon_rel(o))
            reps.setdefault(key, o)
        items = list(reps.items())
        for key1, o1 in items:
            c1 = key1
            Y, X, _ = self.coord[o1]
            if all(c[1] == 0 for c in c1):
                cons.append(self.T(o1) <= 2 * self.k - 1)
            for key2, o2 in items:
                c2 = key2
                if all(b == (a[0], a[1] + 1) for a, b in zip(c1, c2)):
                    h = self.T(o2) - self.T(o1)
                    cons += [h >= 0, h <= 2 * (self.k - X) - 3]
                if all(b == (a[0] - 1, a[1]) for a, b in zip(c1, c2)) and all(a[1] < a[0] for a in c1):
                    v = self.T(o2) - self.T(o1)
                    cons.append(v >= 0)
                    if not (os.environ.get('NO_VD') == '1' and all(b[0] == b[1] for b in c2)):
                        cons.append(v <= (2 * (self.k - Y) if os.environ.get('VFORM') == 'ky' else 2 * self.k - X - Y - 1))
        return cons

    def content_constraints(self):
        """Grains at every cell are >= 0 during stabilization: D + sum(nbr T) - 4T >= 0.
        Inductive because the one-round map F is monotone and this is T <= F(T)."""
        cons = []
        seen = set()
        for o in self.group:
            if max(abs(o[0]), abs(o[1])) > R - 1:
                continue
            key = tuple(self.canon_rel(o))
            if key in seen:
                continue
            seen.add(key)
            Y, X, diag = self.coord[o]
            Dv = 4 * (self.k - Y) if diag else z3.IntVal(2)
            S = Dv + sum(self.T((o[0] + a, o[1] + b)) for a, b in ((-1, 0), (1, 0), (0, -1), (0, 1)))
            cons.append(S - 4 * self.T(o) >= 0)
        return cons

    def diag_anchors(self):
        """Offsets (j, j) in the window that are diagonal cells (d + j, d + j), with their index."""
        out = []
        for j in range(-R, R + 1):
            if (j, j) in self.group and all(c == (dd + j, dd + j) for c, (kk, dd) in zip(self.canon_rel((j, j)), self.smp)):
                out.append(j)
        return out

    def template_expr(self, t, j):
        """Template t anchored at diagonal cell d + j, if all its cells lie in the window."""
        terms = []
        for (a, b), c in t:
            o = (a + j, b + j)
            if abs(o[0]) > R or abs(o[1]) > R:
                return None
            terms.append(c * self.T(o))
        return sum(terms)


def run():
    sizes = list(range(10, 81, 2))
    templates = make_templates()
    print(f"{len(templates)} templates; mining on {len(sizes)} sizes ...", flush=True)
    import os
    if os.path.exists("houdini_mined.json"):
        cands = [(tuple((tuple(o), c) for o, c in t), a, b) for t, a, b in json.load(open("houdini_mined.json"))]
    else:
        cands = mine(templates, sizes)
        json.dump([[[[list(o), c] for o, c in t], a, b] for t, a, b in cands], open("houdini_mined.json", "w"))
    # the two target bounds must be in the set, with their exact constants
    E = (((0, -1), -1), ((0, 0), 1))
    Vd = (((0, 0), 1), ((1, 0), -1))
    print(f"{len(cands)} mined candidates", flush=True)
    wins = {p: Window(p) for p in itertools.product(D_TOP, D_CEN)}
    wins = {p: w for p, w in wins.items() if w.ok}
    live = set(range(len(cands)))
    rnd = 0
    while True:
        rnd += 1
        dropped = set()
        for p, w in wins.items():
            base = w.cons + w.hv_constraints()
            anchors = w.diag_anchors()
            hyp = []
            for i in live:
                t, a, b = cands[i]
                for j in anchors:
                    ex = w.template_expr(t, j)
                    if ex is not None:
                        hyp.append(ex <= a * (w.k - (w.d + j)) + b)
            s = z3.Solver()
            s.set('timeout', 120000)
            s.add(base + hyp)
            # next-round values for all cells within radius 2 of the anchor
            nx = {}
            for o in w.group:
                if max(abs(o[0]), abs(o[1])) <= R - 1:
                    rep = o
                    if rep in nx:
                        continue
                    n, c = w.nxt(o, f"n_{o[0]}_{o[1]}".replace('-', 'm'))
                    s.add(c)
                    nx[o] = n
            def N(o):
                if o not in w.group:
                    return z3.IntVal(0)               # sink cell: always 0
                for o2, n in nx.items():
                    if w.same(o, o2):
                        return n
                return None
            for i in sorted(live - dropped):
                t, a, b = cands[i]
                ns = [N(o) for o, _ in t]
                if any(x is None for x in ns):
                    continue
                goal = sum(c * n for (o, c), n in zip(t, ns)) <= a * (w.k - w.d) + b
                s.push()
                s.add(z3.Not(goal))
                r = s.check()
                s.pop()
                if r != z3.unsat:
                    dropped.add(i)
        live -= dropped
        print(f"round {rnd}: dropped {len(dropped)}, {len(live)} candidates remain", flush=True)
        if not dropped:
            break
    # do the target bounds survive?
    def alive(t, a, b):
        return any(cands[i][0] == t and cands[i][1] == a and cands[i][2] <= b for i in live)
    ok_E = any(cands[i][0] == E and 2 * 1 >= 0 and cands[i][1] == 2 and cands[i][2] <= -1 for i in live)
    ok_V = any(cands[i][0] == Vd and cands[i][1] == 2 and cands[i][2] <= -2 for i in live)
    print("E(d) <= 2(k-d)-1 survives:", ok_E, "  Vd(d) <= 2(k-d)-2 survives:", ok_V)
    json.dump([[list(map(list, [list(o) + [c] for o, c in cands[i][0]])), cands[i][1], cands[i][2]] for i in sorted(live)],
              open("houdini_live.json", "w"))
    return 0 if (ok_E and ok_V) else 1




# ---------------------------------------------------------------- faster Houdini (parallel, model-based)
def _profile_round(args):
    prof, cands, live = args
    w = Window(prof)
    if not w.ok:
        return set()
    hyp = []
    anchors = w.diag_anchors()
    for i in live:
        t, a, b = cands[i]
        for j in anchors:
            ex = w.template_expr(t, j)
            if ex is not None:
                hyp.append(ex <= a * (w.k - (w.d + j)) + b)
    s = z3.Solver()
    s.set('timeout', 20000)
    s.add(w.cons + w.hv_constraints() + w.content_constraints() + hyp)
    nx = {}
    for o in w.group:
        if max(abs(o[0]), abs(o[1])) <= R - 1 and not any(w.same(o, o2) for o2 in nx):
            n, c = w.nxt(o, f"n_{o[0]}_{o[1]}".replace('-', 'm'))
            s.add(c)
            nx[o] = n
    def N(o):
        if o not in w.group:
            return z3.IntVal(0)
        for o2, n in nx.items():
            if w.same(o, o2):
                return n
        return None
    goals = {}
    for i in live:
        t, a, b = cands[i]
        ns = [N(o) for o, _ in t]
        if any(x is None for x in ns):
            continue
        goals[i] = sum(c * n for (o, c), n in zip(t, ns)) <= a * (w.k - w.d) + b
    dropped = set()
    proven = set()
    import time
    tag = "_".join(str(x).replace("'", "").replace(" ", "") for x in prof)
    log = open(f"houdini_prof_{tag}.log", "a")
    t0 = time.time()
    order = list(goals)
    for n_done, i in enumerate(order):
        if i in dropped:
            continue
        s.push()
        s.add(z3.Not(goals[i]))
        r = s.check()
        if r == z3.unsat:
            s.pop()
            proven.add(i)
        elif r == z3.sat:
            mdl = s.model()
            s.pop()
            killed = {j for j in order if j not in dropped and j not in proven
                      and z3.is_false(mdl.eval(goals[j], model_completion=True))}
            killed.add(i)
            dropped |= killed
        else:
            s.pop()
            dropped.add(i)                     # unknown: drop (safe)
        if n_done % 50 == 0:
            log.write(f"{time.time()-t0:7.0f}s  {n_done}/{len(order)} checked, proven {len(proven)}, dropped {len(dropped)}" + chr(10))
            log.flush()
    log.write(f"{time.time()-t0:7.0f}s  done: proven {len(proven)}, dropped {len(dropped)}" + chr(10))
    log.close()
    return dropped


def run_fast(workers=12):
    import multiprocessing as mp
    cands = [(tuple((tuple(o), c) for o, c in t), a, b) for t, a, b in json.load(open("houdini_mined.json"))]
    live = set(range(len(cands)))
    profs = [p for p in itertools.product(D_TOP, D_CEN)]
    rnd = 0
    with mp.Pool(workers) as pool:
        while True:
            rnd += 1
            res = pool.map(_profile_round, [(p, cands, live) for p in profs])
            dropped = set().union(*res)
            live -= dropped
            print(f"round {rnd}: dropped {len(dropped)}, {len(live)} candidates remain", flush=True)
            if not dropped:
                break
    E = (((0, -1), -1), ((0, 0), 1))
    Vd = (((0, 0), 1), ((1, 0), -1))
    ok_E = any(cands[i][0] == E and cands[i][1] == 2 and cands[i][2] <= -1 for i in live)
    ok_V = any(cands[i][0] == Vd and cands[i][1] == 2 and cands[i][2] <= -2 for i in live)
    print("E(d) <= 2(k-d)-1 survives:", ok_E, "  Vd(d) <= 2(k-d)-2 survives:", ok_V, flush=True)
    json.dump([[[[list(o), c] for o, c in cands[i][0]], cands[i][1], cands[i][2]] for i in sorted(live)],
              open("houdini_live.json", "w"))


if __name__ == "__main__":
    run_fast()
