"""Numerical illustration of the theorem (not part of the proof).

For the square of the nine-cycle C_9^2 (i ~ j iff j - i = +-1, +-2 mod 9) we compute many orthogonal
representations by unit vectors in R^4 (x_i orthogonal to x_j for every edge ij), starting from random
points and adding a repulsion term that pushes the vectors apart.  For every representation found we
report, for each residue class {r, r+3, r+6}, how far its three vectors are from being parallel, and
the smallest distance between two of the nine vectors.

The theorem predicts that in every representation some class consists of three parallel unit vectors,
so that two of the nine vectors coincide.  As a control, the same procedure applied to C_8^2 (also
4-regular) finds injective representations with all distances bounded away from 0.

Usage: python numerical_check.py [number_of_starts]      (needs numpy and scipy)
"""
import sys

import numpy as np
from scipy.optimize import least_squares


def edges_of_square_cycle(n):
    return [(i, (i + s) % n) for i in range(n) for s in (1, 2)]


def residuals(flat, n, edges, rep):
    x = flat.reshape(n, 4)
    r = [x[i] @ x[j] for i, j in edges]
    r += [x[i] @ x[i] - 1.0 for i in range(n)]
    if rep > 0:  # soft repulsion between all pairs (pushes towards injective placements)
        for i in range(n):
            for j in range(i + 1, n):
                r.append(rep / (1e-3 + np.sum((x[i] - x[j]) ** 2)))
    return np.array(r)


def solve(n, rng, rep_schedule=(1e-2, 1e-3, 1e-4, 0.0)):
    edges = edges_of_square_cycle(n)
    flat = rng.normal(size=4 * n)
    for rep in rep_schedule:  # anneal the repulsion to zero, then solve the constraints exactly
        flat = least_squares(residuals, flat, args=(n, edges, rep), xtol=1e-15, ftol=1e-15, gtol=1e-15).x
    x = flat.reshape(n, 4)
    res = np.max(np.abs(residuals(flat, n, edges, 0.0)))
    return x, res


def collinearity(x, cls):
    """Largest sine of the angle between two vectors of the class (0 means the class is on one line)."""
    worst = 0.0
    for a in range(len(cls)):
        for b in range(a + 1, len(cls)):
            u, v = x[cls[a]], x[cls[b]]
            c = abs(u @ v) / (np.linalg.norm(u) * np.linalg.norm(v))
            worst = max(worst, np.sqrt(max(0.0, 1.0 - c * c)))
    return worst


def min_distance(x):
    n = len(x)
    return min(np.linalg.norm(x[i] - x[j]) for i in range(n) for j in range(i + 1, n))


def main():
    starts = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    rng = np.random.default_rng(20261001)

    print(f"C_9^2 in R^4: {starts} random starts")
    solved = collapsed = 0
    max_min_dist = 0.0
    hist = {0: 0, 1: 0, 2: 0, 3: 0}
    for _ in range(starts):
        x, res = solve(9, rng)
        if res > 1e-10:
            continue
        solved += 1
        col = [collinearity(x, [r, r + 3, r + 6]) for r in range(3)]
        md = min_distance(x)
        max_min_dist = max(max_min_dist, md)
        k = sum(c < 1e-6 for c in col)
        hist[k] += 1
        if k > 0:
            collapsed += 1
    print(f"  representations found (residual < 1e-10): {solved}")
    print(f"  with a residue class on one line (sine < 1e-6): {collapsed}")
    print(f"  number of such classes per representation (0/1/2/3): {hist[0]}/{hist[1]}/{hist[2]}/{hist[3]}")
    print(f"  largest smallest-distance between two of the nine vectors: {max_min_dist:.2e}")

    print(f"control C_8^2 in R^4: {min(starts, 50)} random starts")
    best = 0.0
    for _ in range(min(starts, 50)):
        x, res = solve(8, rng)
        if res < 1e-10:
            best = max(best, min_distance(x))
    print(f"  largest smallest-distance between two of the eight vectors: {best:.3f}")


if __name__ == "__main__":
    main()
