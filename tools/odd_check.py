"""One-pass check that the fixed invariant families are inductive on the odd grid.

Families (quarter cells, top-left, below the diagonal): H0, H1 (incl. EDGE), V0, V1' (V <= 2(k-y)),
E and Vd (special cases, kept for clarity); cross cells: C0 (sigma <= v), C1 (v - sigma <= 1),
Mstar; the centre: T(k,k) <= T(k,k-1). Background: nonnegative contents.
Every family instance is a hypothesis at round t; each is checked at round t+1 in every window.
"""
import itertools
import json
import sys
import multiprocessing as mp

import z3

import invariant_engine as IE
import odd_houdini as O


def fams():
    import os
    fx = O.fixed()
    for c in fx:
        if c['name'] == 'V1':
            c['bound'] = [2, -2, 0, 0]          # V(y,x) <= 2(k - y)
        if c['name'] == 'Vd':
            c['thr'] = 2                         # d <= k-2 only (at d = k-1 the cell below is a cross cell)
    drop = set(os.environ.get('DROP', '').split(',')) - {''}
    return [c for c in fx if c['name'] not in drop]


def one(args):
    wk, p = args
    fx = fams()
    live = set(range(len(fx)))
    d, u, n = O.work((wk, p, 0, 1, fx, live, 600))
    return wk, p, sorted(fx[i]['name'] for i in d), sorted(fx[i]['name'] for i in u), n


def main():
    windows = [('cell', p) for p in itertools.product(*IE.PROFILE_VALUES['cell'])]
    windows += [('diag', p) for p in itertools.product(*IE.PROFILE_VALUES['diag'])]
    windows += [('cross', p) for p in itertools.product(*IE.PROFILE_VALUES['cross'])]
    windows = [(wk, p) for wk, p in windows if IE.Window(O.GEOM, wk, p).ok]
    print(f"{len(windows)} windows", flush=True)
    bad = []
    total = 0
    with mp.Pool(int(sys.argv[1]) if len(sys.argv) > 1 else 14) as pool:
        for wk, p, d, u, n in pool.imap_unordered(one, windows):
            total += n
            if d or u:
                bad.append((wk, p, d, u))
                print(f"  {wk} {p}: NOT PROVEN {d} unresolved {u}", flush=True)
    print(f"proven goals: {total}; windows with failures: {len(bad)}", flush=True)
    json.dump([[wk, str(p), d, u] for wk, p, d, u in bad], open("odd_check_failures.json", "w"))


if __name__ == "__main__":
    main()
