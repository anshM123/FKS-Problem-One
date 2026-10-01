# The square of the nine-cycle answers Problem 1 of Frankl, Kupavskii and Swanepoel (negatively)

**Authors:** Ansh Mishra, Aryan Senthilkumar. **License:** MIT. **Paper:** [`paper/main.pdf`](paper/main.pdf)

The *spherical dimension* of a graph `G` is the least `k` such that the vertices of `G` can be placed at
distinct points of the sphere of radius `1/√2` centred at the origin of `ℝ^k`, with every edge of length `1`
(non-edges may also have length `1`). On this sphere, an edge has length `1` exactly when its endpoints
are orthogonal.

Frankl, Kupavskii and Swanepoel, *Embedding graphs in Euclidean space*, J. Combin. Theory Ser. A 171 (2020),
105146 ([arXiv:1802.03092](https://arxiv.org/abs/1802.03092)), §5, ask:

> **Problem 1.** Is it true that for d > 3 any graph with maximum degree d, except K_{d+1}, has spherical
> dimension at most d?

Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) states this question as
`Arxiv.«1802.03092».problem_1`, together with its `d = 4` instance `problem_1.variants.dimension_four`. The statement
file is `FormalConjectures/Arxiv/1802.03092/EmbeddingGraphs.lean`, in pull request
[#6681](https://github.com/google-deepmind/formal-conjectures/pull/6681). Both statements are marked
`research open`. This repository answers both:

| Statement | Question | Answer |
|---|---|---|
| `problem_1` | For every `d > 3`, does every graph of maximum degree at most `d` with no component `K_{d+1}` have spherical dimension at most `d`? | **No** |
| `problem_1.variants.dimension_four` | The same for `d = 4`. | **No** |

## Result

**Theorem.** Let `x_0, …, x_8` be unit vectors in `ℝ⁴` with `x_i ⊥ x_j` whenever `j − i ≡ ±1, ±2 (mod 9)`.
Then for some `r` the three vectors `x_r, x_{r+3}, x_{r+6}` are parallel, so two of the nine vectors are equal.

So the square of the nine-cycle, `C_9²` (vertices `ℤ_9`, `i ~ j` iff `j − i ∈ {±1, ±2}`), has no spherical
representation in `ℝ⁴`. It is connected and 4-regular, and it is not `K_5`. Its spherical dimension is exactly `5`: FKS
Proposition 2 gives at most `5`.

- **Proof idea** (paper, §2). Each residue class `{r, r+3, r+6}` is independent, and `x_{i+1}, x_{i+2}` is an orthonormal
  basis of `span(x_i, x_{i+3})^⊥`.
  - If two vectors of the class `{0, 3, 6}` are parallel, a short plane-geometry argument puts the class
    `{1, 4, 7}` or `{2, 5, 8}` on a line.
  - Otherwise, a vector `u` orthogonal to `x_0, x_3, x_6` lies in three planes. The three remaining cross edges
    `2–4`, `5–7`, `8–1` then give three equations whose product forces a class onto a line.
- **Smallest order** (paper, §3). Every graph on at most `8` vertices with maximum degree at most `4` and no component
  `K_5` has spherical dimension at most `4`. The proof finds a perfect matching in the complement (Tutte's theorem) and
  applies the cross-polytope construction of FKS Lemma 13. So `C_9²` is a counterexample of the smallest possible
  order. For every `d ≥ 4`, the bound for graphs on at most `2d` vertices was proved in Lean by Dishant; see Prior work.
- **Larger `d`** remains open. A numerical search found injective representations for every connected circulant
  graph of degree 5 or 6 on at most 18 vertices (`scripts/circulant_scan.py`).

## Lean 4 verification (`lean/`)

- `DMSolutions/FKS_Problem1/EmbeddingGraphs.lean` is a byte-identical copy of the statement file of pull request
  #6681 (head `339f18ba`, git blob `b70e39b9`).
- `DMSolutions/FKS_Problem1/Core.lean` imports Mathlib only.
  - It contains verbatim copies of `HasSphericalDimAtMost` and `HasCompleteComponent`, and the graph `C9sq`.
  - `rep_not_injective` is the theorem above, for any real inner product space of dimension 4.
  - `not_hasSphericalDimAtMost_C9sq`.
- `DMSolutions/FKS_Problem1/Solution.lean` proves the exact statements with the answer filled in, using the statement
  file's own definitions:
  ```lean
  theorem problem_1_solved :
      answer(False) ↔ ∀ d : ℕ, 3 < d → ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        G.maxDegree ≤ d → ¬ HasCompleteComponent d G → HasSphericalDimAtMost d G
  theorem problem_1.variants.dimension_four_solved :
      answer(False) ↔ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        G.maxDegree ≤ 4 → ¬ HasCompleteComponent 4 G → HasSphericalDimAtMost 4 G
  ```
- `DMSolutions/FKS_Problem1/CheckAnswer.lean` has three checks:
  - `answer(False) = False` by `rfl`;
  - the copied definitions are the statement file's (`rfl`);
  - it prints the repository statements next to ours.

All theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. `Core.lean`, `Solution.lean` and `CheckAnswer.lean`
contain no `sorry`, `admit`, `native_decide` or `axiom`. The statement file keeps the repository's own `sorry` placeholders,
exactly as in the pull request.

To reproduce, you need:
- Lean v4.33.1;
- a formal-conjectures checkout, tested at `ab0addc45f699bdd0b7cc58efa5140a72f101a9e`;
- `lake exe cache get`, run in that checkout.

Then run:

```bash
bash lean/check.sh /path/to/formal-conjectures
```

The script copies the four files into `DMSolutions/FKS_Problem1/` of the checkout. Then it:
1. compiles `Core.lean`;
2. compiles the statement file with the repository's own `leanOptions`;
3. compiles `Solution.lean` and `CheckAnswer.lean`;
4. prints the axioms and runs a keyword scan.

Log: `logs/lean_check.log` (exit 0, 125 s).

## Numerical checks (`scripts/`, `logs/`)

These are illustrations, not part of the proof.

- `numerical_check.py` computes 200 orthogonal representations of `C_9²` in `ℝ⁴` from random starts, with a repulsion term.
  - In every one, a residue class lies on a line, and two of the nine vectors coincide.
  - Control: `C_8²` has injective representations.
  - Log: `logs/numerical_check.log`.
- `circulant_scan.py` covers every connected circulant graph of degree 4, 5 or 6 on at most 18 vertices (151, 78 and 245 graphs).
  - Only three have no injective representation in `ℝ^d`: `C_9(1,2)`, `C_9(1,4)` and `C_9(2,4)`. All three are isomorphic to `C_9²`.
  - Log: `logs/circulant_scan.log`.
- `small_graphs_scan.py` covers all connected 4-regular graphs on 9 and 10 vertices (16 and 59 classes), plus the hypercubes `Q_4` and `Q_5`.
  - Only `C_9²` fails.
  - Log: `logs/small_graphs_scan.log`.
- `edge_minimality.py` removes one edge from `C_9²`, for each of the two edge orbits of its automorphism group (dihedral, order 18).
  - Both resulting graphs have injective representations. So, numerically, `C_9²` is an edge-minimal counterexample.
  - Log: `logs/edge_minimality.log`.

## Prior work

- The question is Problem 1 of Frankl, Kupavskii and Swanepoel (2020). It is repeated as Problem 3.15 in N. Frankl's
  PhD thesis (LSE, 2020), where the authors say they suspect a positive answer. For `d = 3` the answer is negative
  (the cube, and the graphs listed after Problem 1).
- The case of graphs on at most `2d` vertices was proved in Lean by Dishant (GitHub user Dishah3241) in
  [FKSProblem1](https://github.com/Dishah3241/FKSProblem1). That README states that the full question remains open.
  `C_9²` has `2d + 1 = 9` vertices.
- Search date 2026-10-01. We found no answer to Problem 1 in:
  - the 17 works citing the paper (Semantic Scholar);
  - the Formal Conjectures issues and pull requests, including #6680 and #6681 (no comments) and the
    "open statements with known solutions" issues;
  - arXiv and web search.
