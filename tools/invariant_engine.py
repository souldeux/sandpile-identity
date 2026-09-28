"""General engine for proving avalanche invariants inductive with z3.

Dynamics (parallel rounds, from T = 0):  T'(p) = floor((D(p) + sum_{q ~ p} T(q)) / 4).

Geometries (fundamental region F, other cells mapped in by symmetry, sink = 0):
  even: 2k x 2k grid, F = {0 <= x <= y <= k-1}; D = 4(k-d) on the diagonal (d,d), else 2
        (the Le Borgne-Rossin pile).
  odd:  (2k+1) x (2k+1) grid, F = {0 <= x <= y <= k}; the four quarters carry the even pile,
        the cross row y = k carries 2, the centre (k,k) carries 0.

An invariant is a linear inequality  sum_o c_o T(anchor + o) <= alpha*(k - idx) + beta*1 + gamma*...
attached to an anchor kind ('cell' below the diagonal, 'diag', or 'cross'). Checks are done in
symbolic windows around an anchor, one per "profile" (distances of the anchor to the edges,
diagonal, midline, centre), so a result holds for every k >= K0.
"""
import itertools
import random

import z3

K0 = 8


def satisfies(v, spec):
    return v >= spec[1] if isinstance(spec, tuple) else v == spec


class Geometry:
    def __init__(self, kind):
        assert kind in ('even', 'odd')
        self.kind = kind

    def size(self, k):
        return 2 * k if self.kind == 'even' else 2 * k + 1

    def canon(self, k, Y, X):
        n = self.size(k)
        if Y < 0 or X < 0 or Y > n - 1 or X > n - 1:
            return None
        lim = k - 1 if self.kind == 'even' else k
        if Y > lim:
            Y = n - 1 - Y
        if X > lim:
            X = n - 1 - X
        if X > Y:
            X, Y = Y, X
        return (Y, X)

    def D_concrete(self, k, c):
        Y, X = c
        if self.kind == 'odd' and Y == k:
            return 0 if X == k else 2
        return 4 * (k - Y) if X == Y else 2


# anchor kinds: symbolic coordinates of the anchor and the profile variables
# cell:  anchor (y, x) with x <= y-1; profile over (y, x, y-x, klim-y)
# diag:  anchor (d, d);             profile over (d, klim-d)      [klim = k-1 even, k-1 odd]
# cross: anchor (k, x) (odd only);  profile over (x, k-1-x)
PROFILE_VALUES = {
    'cell': [[0, 1, 2, 3, ('ge', 4)], [-1, 0, 1, 2, ('ge', 3)], [1, 2, 3, 4, 5, 6, ('ge', 7)], [0, 1, 2, 3, ('ge', 4)]],
    'diag': [[0, 1, 2, 3, ('ge', 4)], [0, 1, 2, 3, ('ge', 4)]],
    'cross': [[0, 1, 2, 3, ('ge', 4)], [0, 1, 2, 3, 4, 5, ('ge', 6)]],
}


def profile_vars(kind, k, a, b):
    """Profile quantities of an anchor given symbolic/concrete (k, a, b)."""
    if kind == 'cell':           # a = y, b = x
        return [a, b, a - b, k - 1 - a]
    if kind == 'diag':           # a = d
        return [a, k - 1 - a]
    return [b, k - 1 - b]        # cross: b = x


def anchor_coords(kind, k, a, b):
    if kind == 'cell':
        return a, b
    if kind == 'diag':
        return a, a
    return k, b


class Window:
    def __init__(self, geom, kind, prof, radius=3, nsamples=8):
        self.geom, self.kind, self.prof, self.R = geom, kind, prof, radius
        rnd = random.Random(hash((geom.kind, kind, str(prof))) & 0xffff)
        smp = []
        for _ in range(60000):
            k = rnd.randint(K0, K0 + 60)
            if kind == 'cell':
                a = rnd.randint(0, k - 1); b = rnd.randint(-1, a - 1) if a >= 0 else -1
            elif kind == 'diag':
                a = rnd.randint(0, k - 1); b = a
            else:
                if geom.kind != 'odd':
                    break
                a = k; b = rnd.randint(0, k - 1)
            if all(satisfies(v, s) for v, s in zip(profile_vars(kind, k, a, b), prof)):
                smp.append((k, a, b))
                if len(smp) >= nsamples:
                    break
        self.smp = smp
        self.ok = len(smp) >= 4
        if not self.ok:
            return
        R = radius
        self.offs = [(i, j) for i in range(-R, R + 1) for j in range(-R, R + 1)]
        k, a, b = z3.Ints('k a b')
        self.k, self.a, self.b = k, a, b
        ay, ax = anchor_coords(kind, k, a, b)
        self.ay, self.ax = ay, ax
        base = [k >= K0]
        if kind == 'cell':
            base += [a >= 0, a <= k - 1, b >= -1, b <= a - 1]
        elif kind == 'diag':
            base += [a >= 0, a <= k - 1, b == a]
        else:
            base += [a == k, b >= 0, b <= k - 1]
        for v, s in zip(profile_vars(kind, k, a, b), prof):
            base.append(v >= s[1] if isinstance(s, tuple) else v == s)
        self.base = base
        # canonical cells of each offset for every sample; decisions must be profile-constant
        self.cc = {}
        for o in self.offs:
            cs = []
            sig = set()
            for kk, aa, bb in smp:
                yy, xx = anchor_coords(kind, kk, aa, bb)
                Y, X = yy + o[0], xx + o[1]
                n = geom.size(kk)
                lim = kk - 1 if geom.kind == 'even' else kk
                sink = Y < 0 or X < 0 or Y > n - 1 or X > n - 1
                Yr = n - 1 - Y if Y > lim else Y
                Xr = n - 1 - X if X > lim else X
                cy = (Yr if Xr <= Yr else Xr)
                sig.add((sink, Y > lim, X > lim, Xr > Yr, Xr == Yr,
                         geom.kind == 'odd' and not sink and cy == kk))
                cs.append(geom.canon(kk, Y, X))
            assert len(sig) == 1, f"{geom.kind}/{kind} profile {prof} too coarse at offset {o}"
            self.cc[o] = cs
        # one z3 variable per distinct canonical cell
        self.var = {}
        self.rep = {}
        for o in self.offs:
            if self.cc[o][0] is None:
                continue
            key = tuple(self.cc[o])
            if key not in self.rep:
                self.rep[key] = o
                self.var[key] = z3.Int(f"T_{o[0]}_{o[1]}".replace('-', 'm'))
        # symbolic canonical coordinates (branch decisions from sample 0)
        self.sym = {}
        kk, aa, bb = smp[0]
        for key, o in self.rep.items():
            yy, xx = anchor_coords(kind, kk, aa, bb)
            Y, X = ay + o[0], ax + o[1]
            Yn, Xn = yy + o[0], xx + o[1]
            n = geom.size(kk)
            lim = kk - 1 if geom.kind == 'even' else kk
            Ns = 2 * k if geom.kind == 'even' else 2 * k + 1
            if Yn > lim:
                Y, Yn = Ns - 1 - Y, n - 1 - Yn
            if Xn > lim:
                X, Xn = Ns - 1 - X, n - 1 - Xn
            if Xn > Yn:
                X, Y, Xn, Yn = Y, X, Yn, Xn
            cross = geom.kind == 'odd' and Yn == kk
            self.sym[key] = (Y, X, Xn == Yn, cross)
        self.cons = list(base) + [v >= 0 for v in self.var.values()]

    # ---- access
    def key(self, o):
        return tuple(self.cc[o]) if o in self.cc and self.cc[o][0] is not None else None

    def T(self, o):
        kk = self.key(o)
        return z3.IntVal(0) if kk is None else self.var[kk]

    def D(self, key):
        Y, X, diag, cross = self.sym[key]
        if cross:
            return z3.IntVal(0) if diag else z3.IntVal(2)   # centre 0, arm 2
        return 4 * (self.k - Y) if diag else z3.IntVal(2)

    def next_vars(self, maxr):
        """Next-round variables (with floor constraints) for every cell within radius maxr."""
        nx, cons = {}, []
        for o in self.offs:
            if max(abs(o[0]), abs(o[1])) > maxr:
                continue
            kk = self.key(o)
            if kk is None or kk in nx:
                continue
            n = z3.Int("n" + str(self.var[kk]))
            S = self.D(kk) + sum(self.T((o[0] + i, o[1] + j)) for i, j in ((-1, 0), (1, 0), (0, -1), (0, 1)))
            cons += [4 * n <= S, S <= 4 * n + 3]
            nx[kk] = n
        return nx, cons

    def content_constraints(self, maxr=None):
        """Nonnegative grains during stabilization: D + sum(nbr T) - 4T >= 0 for every cell whose
        neighbours are in the window. Inductive: it says T <= F(T) for the monotone round map F."""
        maxr = self.R - 1 if maxr is None else maxr
        cons, seen = [], set()
        for o in self.offs:
            if max(abs(o[0]), abs(o[1])) > maxr:
                continue
            kk = self.key(o)
            if kk is None or kk in seen:
                continue
            seen.add(kk)
            S = self.D(kk) + sum(self.T((o[0] + i, o[1] + j)) for i, j in ((-1, 0), (1, 0), (0, -1), (0, 1)))
            cons.append(S - 4 * self.T(o) >= 0)
        return cons

    def NT(self, nx, o):
        kk = self.key(o)
        return z3.IntVal(0) if kk is None else nx.get(kk)

    # ---- structural queries on canonical cells (checked on every sample)
    def rel(self, o1, o2, dy, dx):
        """canonical(o2) == canonical(o1) + (dy, dx) on every sample."""
        c1, c2 = self.cc.get(o1), self.cc.get(o2)
        if c1 is None or c2 is None or c1[0] is None or c2[0] is None:
            return False
        return all(q == (p[0] + dy, p[1] + dx) for p, q in zip(c1, c2))

    def is_quarter(self, o):
        c = self.cc[o]
        if c[0] is None:
            return False
        if self.geom.kind == 'even':
            return True
        return all(p[0] <= kk - 1 for p, (kk, _, _) in zip(c, self.smp))

    def is_cross_arm(self, o):
        c = self.cc[o]
        return (self.geom.kind == 'odd' and c[0] is not None and
                all(p[0] == kk and p[1] <= kk - 1 for p, (kk, _, _) in zip(c, self.smp)))

    def is_centre(self, o):
        c = self.cc[o]
        return (self.geom.kind == 'odd' and c[0] is not None and
                all(p == (kk, kk) for p, (kk, _, _) in zip(c, self.smp)))

    def is_diag_quarter(self, o):
        c = self.cc[o]
        return c[0] is not None and self.is_quarter(o) and all(p[0] == p[1] for p in c)
