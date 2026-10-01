import DMSolutions.FKS_Problem1.EmbeddingGraphs
import DMSolutions.FKS_Problem1.Core

/-!
# Solution of FKS Problem 1 and of its `d = 4` variant

The statements are those of `FormalConjectures/Arxiv/1802.03092/EmbeddingGraphs.lean`
(formal-conjectures pull request 6681, head `339f18ba`; the file `EmbeddingGraphs.lean` in this
directory is a byte-identical copy, git blob `b70e39b9`), with the answer filled in and stated with
the statement file's own definitions `HasSphericalDimAtMost` and `HasCompleteComponent`.

Both answers are **False**. The square of the nine-cycle `FKSCore.C9sq` (vertices `Fin 9`,
`i ~ j` iff `j - i ≡ ±1, ±2 (mod 9)`) is connected, `4`-regular and not `K₅`, but it has no
injective placement on the sphere of radius `1/√2` in `ℝ⁴` with all edges of length `1`
(`FKSCore.not_hasSphericalDimAtMost_C9sq`).
-/

namespace Arxiv.«1802.03092»

open scoped Classical in
/-- `problem_1` with the answer `False`. -/
theorem problem_1_solved :
    answer(False) ↔ ∀ d : ℕ, 3 < d → ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.maxDegree ≤ d → ¬ HasCompleteComponent d G → HasSphericalDimAtMost d G :=
  ⟨False.elim, fun h => FKSCore.problem_1_false h⟩

open scoped Classical in
/-- `problem_1.variants.dimension_four` with the answer `False`. -/
theorem problem_1.variants.dimension_four_solved :
    answer(False) ↔ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.maxDegree ≤ 4 → ¬ HasCompleteComponent 4 G → HasSphericalDimAtMost 4 G :=
  ⟨False.elim, fun h => FKSCore.problem_1_dim4_false h⟩

end Arxiv.«1802.03092»

#print axioms Arxiv.«1802.03092».problem_1_solved
#print axioms Arxiv.«1802.03092».problem_1.variants.dimension_four_solved
