"""Probe: how far from the midline does the square's LBR avalanche differ from a long rectangle's?

Square 2k x 2k and rectangle (2k + 2t) tall x 2k wide, both with the Le Borgne-Rossin pile
D = L W, W = 2kd - d^2 + d (d = depth, capped at k by the width). Rows 0..k-1 have the same D in
both. For each distance r = k-1-y from the square's midline row we report
  final: max_x |a_square - a_rect| at the end,
  any round: max over rounds t and x of |T_t square - T_t rect| (same parallel rounds),
  first round the rows differ.
If the difference vanishes beyond a bounded r, the square's far field is exactly the long-rectangle
avalanche, which Le Borgne-Rossin describe; a finite band invariant would then have known input.
"""
import sys
import numpy as np


def pile(H, Wd, k):
    y, x = np.indices((H, Wd))
    d = np.minimum(np.minimum(y, H - 1 - y), np.minimum(x, Wd - 1 - x)) + 1
    d = np.minimum(d, k)
    Wf = 2 * k * d - d * d + d
    p = np.pad(Wf, 1)
    return 4 * Wf - p[:-2, 1:-1] - p[2:, 1:-1] - p[1:-1, :-2] - p[1:-1, 2:]


def step(c, T):
    P = np.pad(T, 1)
    return (c + P[:-2, 1:-1] + P[2:, 1:-1] + P[1:-1, :-2] + P[1:-1, 2:]) // 4


def probe(k, t):
    m = 2 * k
    cs, cr = pile(m, m, k), pile(m + 2 * t, m, k)
    assert (cs[:k] == cr[:k]).all()
    Ts, Tr = np.zeros_like(cs), np.zeros_like(cr)
    worst = np.zeros(k, np.int64)            # per r, max diff over all rounds
    first = [None] * k
    rnd = 0
    done_s = done_r = False
    while not (done_s and done_r):
        rnd += 1
        if not done_s:
            N = step(cs, Ts); done_s = (N == Ts).all(); Ts = N
        if not done_r:
            N = step(cr, Tr); done_r = (N == Tr).all(); Tr = N
        diff = np.abs(Ts[:k] - Tr[:k]).max(axis=1)[::-1]   # index r = k-1-y
        worst = np.maximum(worst, diff)
        for r in range(k):
            if first[r] is None and diff[r] > 0:
                first[r] = rnd
    final = np.abs(Ts[:k] - Tr[:k]).max(axis=1)[::-1]
    return final, worst, first, rnd


if __name__ == "__main__":
    for k in map(int, sys.argv[1:] or ["16", "32", "64"]):
        final, worst, first, rnd = probe(k, k)
        reach_f = max((r for r in range(k) if final[r] > 0), default=-1)
        reach_w = max((r for r in range(k) if worst[r] > 0), default=-1)
        print(f"k={k} ({rnd} rounds): final differs up to r={reach_f} (of {k-1}); "
              f"some round differs up to r={reach_w}")
        print("   r:        ", list(range(min(k, 24))))
        print("   final diff:", final[:24].tolist())
        print("   any round: ", worst[:24].tolist())
        print("   first rnd: ", first[:24])
