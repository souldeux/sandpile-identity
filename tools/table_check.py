"""Two-round induction with mined TABLE invariants on the midline row (even grid).

Quantities at a midline cell j = (k-1, j) (offsets from the anchor; T = round t, P = round t-1):
  z(o)  = grains at o = D(o) + sum of neighbours' T - 4 T(o)
  d(o)  = T(o + (-1,0)) - T(o)             (step down into o)
  A(o)  = T(o) - P(o)                      (topples of o in the last round)
Tables (tuples that occur in simulations, from the base pair (round 0, round 1) on, k <= KMAX):
  TA = (d(0,-1), z(0,0), d(0,0), A(0,0), d(0,1))      rescue structure
  TC = (z(0,0), d(0,0), A(0,0), A(-1,0))              vertical structure (contains VA)
Each table is mined separately per position class: 'L' (j = 0), 'R' (j = k-2), 'I' (otherwise).
Hypotheses: base families at both rounds, the exact step, contents >= 0, tables at every midline
anchor in the window, LA. Targets: the tables and LA at the anchor, one round later.
"""
import itertools
import json
import os
import sys
import multiprocessing as mp

import numpy as np
import z3

import invariant_engine as IE
from houdini_general import anchor_ok, start_pile
import even_check2 as EC

GEOM = IE.Geometry('even')
KMAX = int(os.environ.get('KMAX', 70))
TABLES = {
    'TA': [('d', (0, -1)), ('z', (0, 0)), ('d', (0, 0)), ('A', (0, 0)), ('d', (0, 1))],
    'TC': [('z', (0, 0)), ('d', (0, 0)), ('A', (0, 0)), ('A', (-1, 0))],
}


# V(y,x) - 2(k-y) <= BV[min(r,4)][min(s,7)-1], r = k-1-y, s = y-x  (max over all simulated rounds)
BV = [[0, 0, 0, 0, 0, 0, 0],
      [0, -1, -1, -1, -1, -1, -1],
      [-1, -1, -1, -2, -2, -2, -2],
      [-1, -2, -2, -2, -2, -3, -3],
      [-2, -2, -3, -3, -3, -4, -4]]


def cls(k, j):
    return 'L' if j == 0 else ('R' if j == k - 2 else 'I')


def mine(cache="tables.json"):
    if os.path.exists(cache):
        return {n: {c: set(map(tuple, v)) for c, v in d.items()} for n, d in json.load(open(cache)).items()}
    out = {n: {'L': set(), 'R': set(), 'I': set()} for n in TABLES}
    for k in range(3, KMAX + 1):
        D = start_pile('even', k)
        Tp = np.zeros_like(D)
        P = np.pad(Tp, 1)
        T = (D + P[:-2, 1:-1] + P[2:, 1:-1] + P[1:-1, :-2] + P[1:-1, 2:]) // 4
        def g(A, y, x):
            c = GEOM.canon(k, y, x)
            return 0 if c is None else int(A[c])
        def content(y, x):
            c = GEOM.canon(k, y, x)
            if c is None:
                return 0
            return int(D[c]) + g(T, y - 1, x) + g(T, y + 1, x) + g(T, y, x - 1) + g(T, y, x + 1) - 4 * int(T[c])
        while True:
            for j in range(0, k - 1):
                y0, x0 = k - 1, j
                def q(kind, o):
                    y, x = y0 + o[0], x0 + o[1]
                    if kind == 'z':
                        return content(y, x)
                    if kind == 'd':
                        return g(T, y - 1, x) - g(T, y, x)
                    return g(T, y, x) - g(Tp, y, x)
                for n, spec in TABLES.items():
                    out[n][cls(k, j)].add(tuple(q(kind, o) for kind, o in spec))
            P = np.pad(T, 1)
            T2 = (D + P[:-2, 1:-1] + P[2:, 1:-1] + P[1:-1, :-2] + P[1:-1, 2:]) // 4
            if (T2 == T).all():
                break
            Tp, T = T, T2
    json.dump({n: {c: sorted(v) for c, v in d.items()} for n, d in out.items()}, open(cache, 'w'))
    return out


def check_window(args):
    prof, tables, timeout = args
    w = IE.Window(GEOM, 'cell', prof)
    if not w.ok:
        return prof, [], [], 0
    k = w.k
    prev = {key: z3.Int("P" + str(v)) for key, v in w.var.items()}
    TP = lambda o: z3.IntVal(0) if w.key(o) is None else prev[w.key(o)]
    def unreflected(o):
        c = w.cc.get(o)
        if c is None or c[0] is None:
            return False
        return all(p == (aa + o[0], bb + o[1]) for (kk, aa, bb), p in zip(w.smp, c))
    def mid_class(o):
        """position class of window offset o if it is a midline anchor (same on every sample), else None"""
        if not unreflected(o):
            return None
        cs = set()
        for (kk, aa, bb), p in zip(w.smp, w.cc[o]):
            if not (p[0] == kk - 1 and 0 <= p[1] <= kk - 2):
                return None
            cs.add(cls(kk, p[1]))
        return cs.pop() if len(cs) == 1 else None
    def D_of(o):
        kk = w.key(o)
        return None if kk is None else w.D(kk)
    def qexpr(kind, o, Tn, Tb):
        """quantity at window offset o using Tn as 'current' and Tb as 'previous'"""
        if kind == 'd':
            a, b = Tn((o[0] - 1, o[1])), Tn(o)
            return None if a is None or b is None else a - b
        if kind == 'A':
            a, b = Tn(o), Tb(o)
            return None if a is None or b is None else a - b
        Dv = D_of(o)
        if Dv is None:
            return z3.IntVal(0)
        nb = [Tn((o[0] + a, o[1] + b)) for a, b in ((-1, 0), (1, 0), (0, -1), (0, 1))]
        c = Tn(o)
        if c is None or any(v is None for v in nb):
            return None
        return Dv + sum(nb) - 4 * c
    def in_window(o, spec):
        need = []
        for kind, off in spec:
            oo = (o[0] + off[0], o[1] + off[1])
            need.append(oo)
            if kind == 'd':
                need.append((oo[0] - 1, oo[1]))
            if kind == 'z':
                need += [(oo[0] + a, oo[1] + b) for a, b in ((-1, 0), (1, 0), (0, -1), (0, 1))]
        return all(q in w.cc for q in need)
    def table_expr(name, o, c, Tn, Tb):
        spec = TABLES[name]
        if not in_window(o, spec):
            return None
        vals = [qexpr(kind, (o[0] + off[0], o[1] + off[1]), Tn, Tb) for kind, off in spec]
        if any(v is None for v in vals):
            return None
        allowed = tables[name][c]
        return z3.Or([z3.And([v == t for v, t in zip(vals, tup)]) for tup in allowed])
    s = z3.Solver()
    s.set('timeout', timeout * 1000)
    s.add(w.cons); s.add([v >= 0 for v in prev.values()])
    def valid(kind, o):
        return unreflected(o) and all(anchor_ok(kind, 'even', kk, p[0], p[1]) for (kk, _, _), p in zip(w.smp, w.cc[o]))
    for c in EC.single_families():
        for o in w.offs:
            if valid(c['kind'], o):
                for Tf in (w.T, TP):
                    e = fexpr(c, o, Tf, w)
                    if e is not None:
                        s.add(e)
    seen = set()
    for o in w.offs:
        kk_ = w.key(o)
        if kk_ is None or kk_ in seen:
            continue
        seen.add(kk_)
        s.add(w.T(o) >= TP(o))
        if max(abs(o[0]), abs(o[1])) <= w.R - 1:
            nb = ((-1, 0), (1, 0), (0, -1), (0, 1))
            Sc = w.D(kk_) + sum(w.T((o[0] + a, o[1] + b)) for a, b in nb)
            Sp = w.D(kk_) + sum(TP((o[0] + a, o[1] + b)) for a, b in nb)
            s.add(Sc - 4 * w.T(o) >= 0, Sp - 4 * TP(o) >= 0, 4 * w.T(o) <= Sp, Sp <= 4 * w.T(o) + 3)
    nx, ncons = w.next_vars(w.R - 2)
    s.add(ncons)
    NT = lambda o: w.NT(nx, o)
    # class-indexed vertical envelope and H2, at both rounds, on every below-diagonal cell (y >= 1)
    def rs_class(o):
        if not unreflected(o):
            return None
        cl = set()
        for (kk, aa, bb), p in zip(w.smp, w.cc[o]):
            Y, X = p
            if not (1 <= Y <= kk - 1 and 0 <= X <= Y - 1):
                return None
            cl.add((min(kk - 1 - Y, 4), min(Y - X, 7)))
        return cl.pop() if len(cl) == 1 else None
    def venv(o, Tf):
        rc = rs_class(o)
        up = (o[0] - 1, o[1])
        if rc is None or up not in w.cc:
            return None
        a, b = Tf(up), Tf(o)
        if a is None or b is None:
            return None
        Y = w.ay + o[0]
        return a - b <= 2 * (k - Y) + BV[rc[0]][rc[1] - 1]
    def h2(o, Tf):
        if not unreflected(o) or not all(anchor_ok('hpair', 'even', kk, p[0], p[1]) for (kk, _, _), p in zip(w.smp, w.cc[o])):
            return None
        rt = (o[0], o[1] + 1)
        if rt not in w.cc:
            return None
        a, b = Tf(rt), Tf(o)
        if a is None or b is None:
            return None
        Y, X = w.ay + o[0], w.ax + o[1]
        return a - b <= 2 * k - X - Y - 2
    for o in w.offs:
        for Tf in (w.T, TP):
            for fn in (venv, h2):
                e = fn(o, Tf)
                if e is not None:
                    s.add(e)
    # hypotheses: tables and LA at every midline anchor
    def la(o, Tn, Tb):
        cells = [(o[0], o[1] - 1), o, (o[0], o[1] + 1)]
        vals = [Tn(q) for q in cells] + [Tb(o)]
        if any(q not in w.cc for q in cells) or any(v is None for v in vals):
            return None
        a, b, cc, bp = vals
        return a - 2 * b + cc + (b - bp) >= -1
    nh = 0
    for o in w.offs:
        c = mid_class(o)
        if c is None:
            continue
        for name in TABLES:
            e = table_expr(name, o, c, w.T, TP)
            if e is not None:
                s.add(e); nh += 1
        e = la(o, w.T, TP)
        if e is not None:
            s.add(e)
    goals = []
    for name, fn in (('Venv', venv), ('H2', h2)):
        g = fn((0, 0), NT)
        if g is not None:
            goals.append((name, g))
    c0 = mid_class((0, 0))
    if c0 is not None:
        for name in TABLES:
            g = table_expr(name, (0, 0), c0, NT, w.T)
            if g is not None:
                goals.append((name, g))
        g = la((0, 0), NT, w.T)
        if g is not None:
            goals.append(('LA', g))
    bad, unk, n = [], [], 0
    for name, g in goals:
        s.push(); s.add(z3.Not(g)); r = s.check(); s.pop()
        if r == z3.unsat:
            n += 1
        elif r == z3.sat:
            bad.append(name)
            if os.environ.get('SHOWCEX') == name:
                s.push(); s.add(z3.Not(g)); s.check(); m = s.model(); s.pop()
                ev = lambda e: m.eval(e, model_completion=True)
                print(f"CEX {name} in {prof}: k={ev(k)} anchor=({ev(w.ay)},{ev(w.ax)}) class {c0}")
                spec = TABLES[name]
                now = [ev(qexpr(kd, off, w.T, TP)) for kd, off in spec]
                nxt = [ev(qexpr(kd, off, NT, w.T)) for kd, off in spec]
                print(f"  {name} tuple now  = {tuple(str(v) for v in now)}")
                print(f"  {name} tuple next = {tuple(str(v) for v in nxt)}  (not in the table)")
                for lab, Tf in (("prev", TP), ("now ", w.T), ("next", NT)):
                    for a in range(-3, 2):
                        row = []
                        for b in range(-2, 3):
                            kk_ = w.key((a, b))
                            v = None if kk_ is None else Tf((a, b))
                            row.append("   ." if kk_ is None else ("   ?" if v is None else f"{ev(v).as_long():4d}"))
                        print(f"  {lab} row {a:+d}:", "".join(row))
        else:
            unk.append(name)
    return prof, bad, unk, n


def fexpr(c, o, Tf, w):
    terms = []
    for (dy, dx), cf in c['t']:
        q = (o[0] + dy, o[1] + dx)
        if q not in w.cc:
            return None
        v = Tf(q)
        if v is None:
            return None
        terms.append(cf * v)
    Y, X = w.ay + o[0], w.ax + o[1]
    ck, cy, cx, c0 = c['bound']
    return sum(terms) <= ck * w.k + cy * Y + cx * X + c0


def main():
    tables = mine()
    for n, d in tables.items():
        print(n, {c: len(v) for c, v in d.items()}, flush=True)
    profs = [p for p in itertools.product(*IE.PROFILE_VALUES['cell'])]
    if os.environ.get('MIDONLY') == '1':
        profs = [p for p in profs if p[3] == 0]
    profs = [p for p in profs if IE.Window(GEOM, 'cell', p).ok]
    print(f"{len(profs)} windows", flush=True)
    fails, total = [], 0
    with mp.Pool(int(sys.argv[1]) if len(sys.argv) > 1 else 14) as pool:
        for p, bad, unk, n in pool.imap_unordered(check_window, [(p, tables, 1800) for p in profs]):
            total += n
            if bad or unk:
                print(f"  {p}: proven {n}; NOT PROVEN {bad} unresolved {unk}", flush=True)
                fails.append((str(p), bad, unk))
    print(f"proven goals: {total}; windows with failures: {len(fails)}", flush=True)


if __name__ == "__main__":
    main()
