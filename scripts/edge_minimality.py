"""Edge-minimality of C_9^2 (numerical, not part of the proof).

The automorphism group of C_9^2 is the dihedral group of order 18, so its edges form two orbits,
{i, i+1} and {i, i+2}.  Removing one edge of either orbit leaves a graph that has an injective
orthogonal representation by unit vectors in R^4 (found numerically, as in circulant_scan.py).

Usage: python edge_minimality.py      (needs numpy, scipy, networkx)
"""
import warnings

import networkx as nx
import numpy as np
from networkx.algorithms.isomorphism import GraphMatcher

from circulant_scan import try_injective

warnings.filterwarnings("ignore")


def main():
    G = nx.circulant_graph(9, [1, 2])
    auts = list(GraphMatcher(G, G).isomorphisms_iter())
    print("automorphisms of C_9^2:", len(auts))
    orbit = {frozenset((a[0], a[1])) for a in auts}
    print("size of the orbit of the edge {0,1}:", len(orbit), "of", G.number_of_edges(), "edges")
    rng = np.random.default_rng(5)
    for e in [(0, 1), (0, 2)]:
        H = G.copy()
        H.remove_edge(*e)
        edges = sorted((min(u, v), max(u, v)) for u, v in H.edges())
        ok, md = try_injective(9, 4, edges, rng, 12)
        print(f"C_9^2 minus edge {e}: injective representation in R^4 found = {ok} (min distance {md:.3f})")


if __name__ == "__main__":
    main()
