"""Numerical scan of small 4-regular graphs and a few other families (not part of the proof).

1. All connected 4-regular graphs on 9 and 10 vertices (16 and 59 isomorphism classes, OEIS A006820),
   collected from random samples until the known counts are reached.
2. C_9^2 minus the edge {0, 1} (edge_minimality.py also removes an edge of the other orbit).
3. The hypercubes Q_4, Q_5 in R^4, R^5.

For each graph, search for an injective orthogonal representation by unit vectors in R^d (d = maximum
degree), as in circulant_scan.py, and report the graphs for which none is found.

Usage: python small_graphs_scan.py [starts]      (needs numpy, scipy, networkx)
"""
import sys

import networkx as nx
import numpy as np

from circulant_scan import try_injective

KNOWN = {9: 16, 10: 59}


def classes_of_4_regular(n, rng, max_samples=200000):
    reps = []
    seen_hash = {}
    for t in range(max_samples):
        G = nx.random_regular_graph(4, n, seed=int(rng.integers(1 << 31)))
        if not nx.is_connected(G):
            continue
        h = nx.weisfeiler_lehman_graph_hash(G)
        bucket = seen_hash.setdefault(h, [])
        if any(nx.is_isomorphic(G, H) for H in bucket):
            continue
        bucket.append(G)
        reps.append(G)
        if len(reps) == KNOWN[n]:
            return reps, t + 1
    return reps, max_samples


def test(G, d, rng, starts):
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    edges = sorted((min(idx[u], idx[v]), max(idx[u], idx[v])) for u, v in G.edges())
    return try_injective(len(nodes), d, edges, rng, starts)


def main():
    starts = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    rng = np.random.default_rng(11)
    c9sq = nx.circulant_graph(9, [1, 2])
    for n in (9, 10):
        reps, samples = classes_of_4_regular(n, rng)
        print(f"n={n}: {len(reps)} connected 4-regular classes found in {samples} samples (known: {KNOWN[n]})", flush=True)
        bad = []
        for G in reps:
            ok, md = test(G, 4, rng, starts)
            if not ok:
                bad.append(G)
                tag = " (this is C_9^2)" if nx.is_isomorphic(G, c9sq) else ""
                print(f"  no injective representation in R^4 found: edges {sorted(G.edges())}{tag} (best min distance {md:.2e})", flush=True)
        print(f"n={n}: {len(bad)} of {len(reps)} without an injective representation in R^4", flush=True)
    G = c9sq.copy()
    G.remove_edge(0, 1)
    ok, md = test(G, 4, rng, starts)
    print(f"C_9^2 minus an edge: injective representation in R^4 found = {ok} (min distance {md:.3f})", flush=True)
    for d in (4, 5):
        ok, md = test(nx.hypercube_graph(d), d, rng, starts)
        print(f"Q_{d} in R^{d}: injective representation found = {ok} (min distance {md:.3f})", flush=True)


if __name__ == "__main__":
    main()
