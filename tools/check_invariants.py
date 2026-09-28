"""Symbolic check that the (H0, H1, V0, V1) invariant system is inductive for the
parallel stabilization of the Le Borgne-Rossin pile on the 2k x 2k grid, for every k >= K0.

Parallel rounds: T'(p) = floor((D(p) + sum of T over the 4 neighbours of p) / 4), from T = 0.
D = 4(k - d) on diagonal cells (d, d), 2 elsewhere. Sink cells have T = 0.
Fundamental triangle F = {0 <= x <= y <= k-1}; other cells map into F by symmetry.

Invariants, for cells (y, x) of F:
  H0: T(y, x+1) - T(y, x) >= 0                 for 0 <= x <= y-1
  H1: T(y, x+1) - T(y, x) <= 2(k - x) - 3      for -1 <= x <= y-1   (T(y, -1) = 0)
  V0: T(y-1, x) - T(y, x) >= 0                 for 0 <= x <= y-1, y >= 1
  V1: T(y-1, x) - T(y, x) <= 2k - x - y - 1    for the same range

For each target instance and each "profile" (how close the cell is to the top, the left
edge, the diagonal and the midline), z3 looks for integer values at round t satisfying every
invariant inside a window and making the round t+1 value violate the target. UNSAT for all
profiles means the step holds for every k >= K0.
"""
import itertools
import random
import os
import sys

import z3

K0 = 8
NO_VD = os.environ.get('NO_VD') == '1'
VKY = os.environ.get('VFORM') == 'ky'
A_RANGE = range(-2, 3)      # row offsets of the window
B_RANGE = range(-2, 4)      # column offsets of the window

# profile values: concrete small values, or ('ge', n) meaning ">= n"
Y_TOP = [0, 1, 2, 3, ('ge', 4)]
X_LEFT = [-1, 0, 1, 2, ('ge', 3)]
S_DIAG = [1, 2, 3, 4, 5, ('ge', 6)]       # s = y - x
R_MID = [0, 1, 2, 3, ('ge', 4)]           # r = k - 1 - y


def satisfies(val, spec):
    return val >= spec[1] if isinstance(spec, tuple) else val == spec


def samples(prof, n=8, tries=20000):
    """Random concrete instances (k, y, x) consistent with the profile, as generic as possible."""
    yt, xl, sd, rm = prof
    out = []
    rnd = random.Random(1)
    for _ in range(tries):
        k = rnd.randint(K0, K0 + 60)
        y = rnd.randint(0, k - 1)
        x = rnd.randint(-1, y)
        if not (satisfies(y, yt) and satisfies(x, xl) and satisfies(y - x, sd) and satisfies(k - 1 - y, rm)):
            continue
        out.append((k, y, x))
        if len(out) >= n:
            break
    return out


def canon(k, Y, X):
    """Map grid cell to (Y, X) in F, or None for the sink."""
    if Y < 0 or X < 0 or Y > 2 * k - 1 or X > 2 * k - 1:
        return None
    if Y >= k:
        Y = 2 * k - 1 - Y
    if X >= k:
        X = 2 * k - 1 - X
    if X > Y:
        X, Y = Y, X
    return (Y, X)


def symbolic_canon(k, y, x, a, b, sample):
    """Symbolic version of canon for window offset (a, b), with branch decisions taken
    from a concrete sample (valid because they are constant across the profile)."""
    ks, ys, xs = sample
    Y, X = y + a, x + b
    Yn, Xn = ys + a, xs + b
    if Yn < 0 or Xn < 0 or Yn > 2 * ks - 1 or Xn > 2 * ks - 1:
        return None
    if Yn >= ks:
        Y, Yn = 2 * k - 1 - Y, 2 * ks - 1 - Yn
    if Xn >= ks:
        X, Xn = 2 * k - 1 - X, 2 * ks - 1 - Xn
    if Xn > Yn:
        X, Y, Xn, Yn = Y, X, Yn, Xn
    return (Y, X)


def check_profile(prof, target):
    """target: 'H' (pair (y,x+1),(y,x)) or 'V' (pair (y-1,x),(y,x)). Returns list of failures."""
    smp = samples(prof)
    if len(smp) < 4:
        return []                                     # profile impossible for k >= K0
    yt, xl, sd, rm = prof
    if target == 'V' and (smp[0][2] < 0 or smp[0][1] < 1):
        return []                                     # V needs x >= 0, y >= 1
    offsets = list(itertools.product(A_RANGE, B_RANGE))
    # branch structure and identifications must agree on every sample
    keyed = []
    for s in smp:
        k, y, x = s
        cells = {}
        for (a, b) in offsets:
            c = canon(k, y + a, x + b)
            cells[(a, b)] = None if c is None else (c[0] - y, c[1] - x, c[0] - (k - 1), c[1] - (k - 1), c[0] == c[1])
        keyed.append(cells)
    # canonical identity: two offsets are the same cell iff their canonical coordinates agree
    # on every sample (coordinates are affine in k, y, x within a profile)
    def ident(o1, o2):
        for s in smp:
            k, y, x = s
            if canon(k, y + o1[0], x + o1[1]) != canon(k, y + o2[0], x + o2[1]):
                return False
        return True
    def consistent_branches(o):
        # same sink / reflection decisions on all samples
        sig = []
        for s in smp:
            k, y, x = s
            Y, X = y + o[0], x + o[1]
            sink = Y < 0 or X < 0 or Y > 2 * k - 1 or X > 2 * k - 1
            Xr = 2 * k - 1 - X if X >= k else X
            Yr = 2 * k - 1 - Y if Y >= k else Y
            sig.append((sink, Y >= k, X >= k, Xr > Yr, Xr == Yr))
        return all(t == sig[0] for t in sig)
    for o in offsets:
        if not consistent_branches(o):
            raise RuntimeError(f"profile {prof} too coarse at offset {o}")

    k, y, x = z3.Ints('k y x')
    base = [k >= K0, y >= 0, y <= k - 1, x >= -1, x <= y - 1]
    for var, spec in ((y, yt), (x, xl), (y - x, sd), (k - 1 - y, rm)):
        base.append(var >= spec[1] if isinstance(spec, tuple) else var == spec)

    # one z3 variable per distinct canonical cell
    groups = []
    for o in offsets:
        if canon(smp[0][0], smp[0][1] + o[0], smp[0][2] + o[1]) is None:
            continue
        for g in groups:
            if ident(g[0], o):
                g.append(o)
                break
        else:
            groups.append([o])
    var_of = {}
    cellsym = {}
    for gi, g in enumerate(groups):
        v = z3.Int(f"T{gi}")
        for o in g:
            var_of[o] = v
        cellsym[gi] = symbolic_canon(k, y, x, g[0][0], g[0][1], smp[0])
    def T(o):
        return var_of.get(o, z3.IntVal(0))            # sink -> 0

    cons = list(base)
    for v in set(var_of.values()):
        cons.append(v >= 0)
    # invariants at round t on every pair inside the window
    rep = {gi: g[0] for gi, g in enumerate(groups)}
    for gi, (Yc, Xc) in cellsym.items():
        # H pairs: (Yc, Xc) and (Yc, Xc+1) both in window and in F
        for gj, (Yd, Xd) in cellsym.items():
            if all((canon(s[0], s[1] + rep[gj][0], s[2] + rep[gj][1]) ==
                    (canon(s[0], s[1] + rep[gi][0], s[2] + rep[gi][1])[0],
                     canon(s[0], s[1] + rep[gi][0], s[2] + rep[gi][1])[1] + 1)) for s in smp):
                h = T(rep[gj]) - T(rep[gi])
                cons += [h >= 0, h <= 2 * (k - Xc) - 3]
            if all((canon(s[0], s[1] + rep[gj][0], s[2] + rep[gj][1]) ==
                    (canon(s[0], s[1] + rep[gi][0], s[2] + rep[gi][1])[0] - 1,
                     canon(s[0], s[1] + rep[gi][0], s[2] + rep[gi][1])[1])) for s in smp):
                # gj is the cell above gi, and gi is strictly below the diagonal
                if all(canon(s[0], s[1] + rep[gi][0], s[2] + rep[gi][1])[1] <
                       canon(s[0], s[1] + rep[gi][0], s[2] + rep[gi][1])[0] for s in smp):
                    v_ = T(rep[gj]) - T(rep[gi])
                    cons.append(v_ >= 0)
                    upper_is_diag = all(canon(s[0], s[1] + rep[gj][0], s[2] + rep[gj][1])[0] ==
                                        canon(s[0], s[1] + rep[gj][0], s[2] + rep[gj][1])[1] for s in smp)
                    if not (NO_VD and upper_is_diag):
                        cons.append(v_ <= (2 * (k - Yc) if VKY else 2 * k - Xc - Yc - 1))
        # H1 at x = -1: T(Yc, 0) <= 2k - 1
        if all(canon(s[0], s[1] + rep[gi][0], s[2] + rep[gi][1])[1] == 0 for s in smp):
            cons.append(T(rep[gi]) <= 2 * k - 1)

    def D(o):
        Yc, Xc = symbolic_canon(k, y, x, o[0], o[1], smp[0])
        diag = keyed[0][o][4]
        return 4 * (k - Yc) if diag else z3.IntVal(2)
    def nxt(o, name):
        n = z3.Int(name)
        S = D(o) + sum(T((o[0] + da, o[1] + db)) for da, db in ((-1, 0), (1, 0), (0, -1), (0, 1)))
        return n, [4 * n <= S, S <= 4 * n + 3]

    for gi, g in enumerate(groups):
        o = g[0]
        if o[0] - 1 < min(A_RANGE) or o[0] + 1 > max(A_RANGE) or o[1] - 1 < min(B_RANGE) or o[1] + 1 > max(B_RANGE):
            continue
        S = D(o) + sum(T((o[0] + da, o[1] + db)) for da, db in ((-1, 0), (1, 0), (0, -1), (0, 1)))
        cons.append(S - 4 * T(o) >= 0)

    failures = []
    if target == 'H':
        right, left = (0, 1), (0, 0)
        nr, cr = nxt(right, 'n_right')
        if smp[0][2] == -1:                           # x = -1: bound T'(y, 0) <= 2k - 1
            goals = [('H1(x=-1)', nr <= 2 * k - 1)]
            extra = cr
        else:
            nl, cl = nxt(left, 'n_left')
            extra = cr + cl
            goals = [('H0', nr - nl >= 0), ('H1', nr - nl <= 2 * (k - x) - 3)]
    else:
        up, here = (-1, 0), (0, 0)
        nu, cu = nxt(up, 'n_up')
        nh, ch = nxt(here, 'n_here')
        extra = cu + ch
        goals = [('V0', nu - nh >= 0)]
        if not (NO_VD and smp[0][1] - smp[0][2] == 1):
            goals.append(('V1', nu - nh <= (2 * (k - y) if VKY else 2 * k - x - y - 1)))
    if os.environ.get('ENCODE_TEST') == '1':
        import numpy as np
        def lapn(f):
            pp = np.pad(f, 1); return 4 * f - pp[:-2, 1:-1] - pp[2:, 1:-1] - pp[1:-1, :-2] - pp[1:-1, 2:]
        allgoals = [g for _, g in goals]
        nvars = {str(v): v for v in [z3.Int('n_right'), z3.Int('n_left'), z3.Int('n_up'), z3.Int('n_here')]}
        for (ks, ys, xs) in smp[:3]:
            m = 2 * ks
            yy, xx = np.indices((m, m))
            dep = np.minimum(np.minimum(yy, xx), np.minimum(m - 1 - yy, m - 1 - xx)) + 1
            Dn = lapn(2 * ks * dep - dep * dep + dep)
            Tn = np.zeros_like(Dn)
            hist = [Tn]
            while True:
                P = np.pad(Tn, 1)
                T2 = (Dn + P[:-2, 1:-1] + P[2:, 1:-1] + P[1:-1, :-2] + P[1:-1, 2:]) // 4
                if (T2 == Tn).all():
                    break
                Tn = T2; hist.append(Tn)
            hist.append(Tn)
            for t in sorted(set([0, 1, 2, len(hist) // 3, len(hist) // 2, len(hist) - 2])):
                if t + 1 >= len(hist):
                    continue
                Tt, Tt1 = hist[t], hist[t + 1]
                sub = [(k, z3.IntVal(ks)), (y, z3.IntVal(ys)), (x, z3.IntVal(xs))]
                for gi, g in enumerate(groups):
                    c = canon(ks, ys + g[0][0], xs + g[0][1])
                    sub.append((var_of[g[0]], z3.IntVal(int(Tt[c]))))
                def actual_next(o):
                    c = canon(ks, ys + o[0], xs + o[1])
                    return 0 if c is None else int(Tt1[c])
                if target == 'H':
                    names = [('n_right', (0, 1))] + ([] if smp[0][2] == -1 else [('n_left', (0, 0))])
                else:
                    names = [('n_up', (-1, 0)), ('n_here', (0, 0))]
                for nm, o in names:
                    sub.append((z3.Int(nm), z3.IntVal(actual_next(o))))
                F_ = z3.simplify(z3.substitute(z3.And(cons + extra + allgoals), *sub))
                if not z3.is_true(F_):
                    failures.append((prof, target, 'ENCODING', f"k={ks} y={ys} x={xs} t={t}", None))
                    return failures
        return failures
    if os.environ.get('VACUITY') == '1':
        s = z3.Solver(); s.set('timeout', 60000)
        s.add(cons + extra)
        r = s.check()
        if r != z3.sat:
            failures.append((prof, target, 'VACUOUS-HYPOTHESES', str(r), None))
        return failures
    for gname, goal in goals:
        s = z3.Solver()
        s.set('timeout', 60000)
        s.add(cons + extra + [z3.Not(goal)])
        r = s.check()
        if r != z3.unsat:
            failures.append((prof, target, gname, str(r), s.model() if r == z3.sat else None))
    return failures


def main():
    all_fail = []
    n = 0
    for prof in itertools.product(Y_TOP, X_LEFT, S_DIAG, R_MID):
        for target in ('H', 'V'):
            f = check_profile(prof, target)
            n += 1
            all_fail += f
    print(f"checked {n} (profile, target) pairs; failures: {len(all_fail)}")
    for prof, target, gname, r, model in all_fail[:25]:
        print("FAIL", target, gname, "profile(y_top, x_left, s, r) =", prof, r)
        if model is not None:
            print("   ", {str(d): model[d] for d in model.decls() if str(d) in ('k', 'y', 'x')})
    return 0 if not all_fail else 1


if __name__ == "__main__":
    sys.exit(main())
