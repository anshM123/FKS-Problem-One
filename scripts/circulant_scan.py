"""Numerical scan of connected circulant graphs (not part of the proof).

For d = 4, 5, 6 and every connected circulant graph C_n(S) of degree d on n <= 18 vertices, search for an
injective orthogonal representation by unit vectors in R^d (unit vectors x_v with x_u orthogonal to x_v
for every edge uv, all x_v distinct).  A representation counts as injective if the constraints hold to
1e-10 and every two vectors are at distance at least 1e-3.  Graphs for which no start succeeds are
reported; the theorem says that C_9(1,2) = C_9^2 must be among them for d = 4.

Usage: python circulant_scan.py [max_n] [starts]      (needs numpy and scipy)
"""
import itertools
import math
import sys

import numpy as np
from scipy.optimize import least_squares


def circulant_edges(n, S):
    E = set()
    for i in range(n):
        for s in S:
            j = (i + s) % n
            E.add((min(i, j), max(i, j)))
    return sorted(E)


def degree(n, S):
    return sum(1 if 2 * s == n else 2 for s in S)


def connected(n, S):
    g = n
    for s in S:
        g = math.gcd(g, s)
    return g == 1


def residuals(flat, n, d, edges, rep):
    x = flat.reshape(n, d)
    r = [x[i] @ x[j] for i, j in edges]
    r += [x[i] @ x[i] - 1.0 for i in range(n)]
    if rep > 0:
        diff = x[:, None, :] - x[None, :, :]
        dist2 = np.sum(diff ** 2, axis=-1)
        iu = np.triu_indices(n, 1)
        r += list(rep / (1e-3 + dist2[iu]))
    return np.array(r)


def try_injective(n, d, edges, rng, starts):
    best = 0.0
    for _ in range(starts):
        flat = rng.normal(size=n * d)
        for rep in (1e-2, 1e-3, 1e-4, 0.0):
            flat = least_squares(residuals, flat, args=(n, d, edges, rep),
                                 xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=4000).x
        x = flat.reshape(n, d)
        if np.max(np.abs(residuals(flat, n, d, edges, 0.0))) > 1e-10:
            continue
        diff = x[:, None, :] - x[None, :, :]
        dist = np.sqrt(np.sum(diff ** 2, axis=-1))
        md = np.min(dist[np.triu_indices(n, 1)])
        best = max(best, md)
        if md > 1e-3:
            return True, md
    return False, best


def main():
    max_n = int(sys.argv[1]) if len(sys.argv) > 1 else 18
    starts = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    rng = np.random.default_rng(7)
    for d in (4, 5, 6):
        tested = 0
        failures = []
        for n in range(d + 2, max_n + 1):
            for k in range(1, n // 2 + 1):
                for S in itertools.combinations(range(1, n // 2 + 1), k):
                    if degree(n, S) != d or not connected(n, S):
                        continue
                    tested += 1
                    ok, md = try_injective(n, d, circulant_edges(n, S), rng, starts)
                    if not ok:
                        failures.append((n, S, md))
                        print(f"  d={d}: no injective representation found for C_{n}{S} (best min distance {md:.2e})", flush=True)
        print(f"d={d}: {tested} connected circulants with n <= {max_n} tested, {len(failures)} without an injective representation", flush=True)


if __name__ == "__main__":
    main()
