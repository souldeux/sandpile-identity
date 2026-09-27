"""Abelian sandpile on an m x n grid (edges drain to a sink).

Reproduces every number quoted in README.md and on sandpile.html:

    python sand.py identity 256        # identity of the 256x256 grid -> images/id_256.png
    python sand.py source 16           # 2**16 grains on one cell     -> images/src_16.png
    python sand.py check               # group-order formula vs brute force on small grids

Needs numpy and Pillow.
"""
import itertools
import sys
import time

import numpy as np
from PIL import Image


def stab(z):
    """Topple until stable. Every unstable cell fires floor(z/4) times per sweep.
    Returns (stable pile, total topples); both are independent of toppling order."""
    z = z.astype(np.int64).copy()
    topples = 0
    while True:
        q = z >> 2
        if not q.any():
            return z, topples
        topples += int(q.sum())
        z -= 4 * q
        z[1:, :] += q[:-1, :]; z[:-1, :] += q[1:, :]
        z[:, 1:] += q[:, :-1]; z[:, :-1] += q[:, 1:]


def identity(h, w):
    """e = stab(6 - stab(6)): equivalent to the empty pile, and >= 3 everywhere
    before the final stabilization, so the result is recurrent."""
    six = np.full((h, w), 6)
    s, t1 = stab(six)
    e, t2 = stab(six - s)
    return e, t1 + t2


def single_source(k):
    """2**k grains dropped on the centre cell of a grid big enough to hold the pile."""
    n = 2 ** k
    r = int((n / 2.1 / np.pi) ** 0.5) + 6
    z = np.zeros((2 * r + 1, 2 * r + 1), int)
    z[r, r] = n
    return stab(z)


def group_order(w, h):
    """Size of the sandpile group = number of spanning trees with the border wired to the sink
    = product of the Dirichlet Laplacian eigenvalues."""
    return np.prod([4 - 2 * np.cos(j * np.pi / (w + 1)) - 2 * np.cos(k * np.pi / (h + 1))
                    for j in range(1, w + 1) for k in range(1, h + 1)])


def recurrent_count(w, h):
    """Brute force: every recurrent pile is stab(3 + x) for some 0 <= x <= 3."""
    seen = set()
    for c in itertools.product(range(4), repeat=w * h):
        s, _ = stab(np.array(c).reshape(h, w) + 3)
        seen.add(tuple(s.ravel()))
    return len(seen)


PAL = np.array([[20, 26, 51], [79, 121, 168], [217, 167, 65], [246, 239, 220]], dtype=np.uint8)


def save(z, path, size=512):
    scale = max(1, size // max(z.shape))
    img = Image.fromarray(PAL[z])
    img.resize((z.shape[1] * scale, z.shape[0] * scale), Image.NEAREST).save(path)


def main(argv):
    cmd = argv[1] if len(argv) > 1 else "identity"
    if cmd == "identity":
        n = int(argv[2]) if len(argv) > 2 else 128
        t = time.time()
        e, topples = identity(n, n)
        ee, _ = stab(e + e)
        print(f"{n}x{n}: {topples:,} topples, {time.time() - t:.1f}s, e+e==e: {(ee == e).all()}, "
              f"height counts {np.bincount(e.ravel(), minlength=4).tolist()}")
        save(e, f"images/id_{n}.png")
    elif cmd == "source":
        k = int(argv[2]) if len(argv) > 2 else 14
        s, topples = single_source(k)
        print(f"2^{k} grains: {topples:,} topples, grid {s.shape[0]}x{s.shape[1]}")
        save(s, f"images/src_{k}.png")
    elif cmd == "check":
        for w, h in [(1, 1), (2, 2), (3, 2), (3, 3)]:
            print(f"{w}x{h}: formula {round(group_order(w, h))}, brute force {recurrent_count(w, h)}")
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv)
