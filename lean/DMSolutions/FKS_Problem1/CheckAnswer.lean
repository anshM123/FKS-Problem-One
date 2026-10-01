import DMSolutions.FKS_Problem1.Solution

/-!
# Checks for the solution of FKS Problem 1

The answer `False` is the proposition `False`, the copied definitions agree with those of the
statement file, and the two solved statements have the same right-hand sides as the repository
statements `problem_1` and `problem_1.variants.dimension_four`.
-/

open Arxiv.«1802.03092»

-- The filled-in answer elaborates to the proposition `False` itself.
example : (answer(False) : Prop) = False := rfl

-- The definitions copied into `FKSCore` are the statement file's definitions.
example : @FKSCore.HasSphericalDimAtMost = @HasSphericalDimAtMost := rfl
example : @FKSCore.HasCompleteComponent = @HasCompleteComponent := rfl

-- Hence the solutions prove the negations of the two open questions.
open scoped Classical in
example : ¬ ∀ d : ℕ, 3 < d → ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.maxDegree ≤ d → ¬ HasCompleteComponent d G → HasSphericalDimAtMost d G :=
  fun h => problem_1_solved.mpr h

open scoped Classical in
example : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.maxDegree ≤ 4 → ¬ HasCompleteComponent 4 G → HasSphericalDimAtMost 4 G :=
  fun h => problem_1.variants.dimension_four_solved.mpr h

-- The counterexample: the square of the nine-cycle, of maximum degree at most `4`, with no
-- complete component, and with no spherical representation in `ℝ⁴`.
example : FKSCore.C9sq.Adj 0 1 ∧ FKSCore.C9sq.Adj 0 2 ∧ FKSCore.C9sq.Adj 0 7 ∧
    FKSCore.C9sq.Adj 0 8 ∧ ¬ FKSCore.C9sq.Adj 0 3 ∧ ¬ FKSCore.C9sq.Adj 0 4 := by decide
example : ¬ HasSphericalDimAtMost 4 FKSCore.C9sq := FKSCore.not_hasSphericalDimAtMost_C9sq
example : ¬ HasCompleteComponent 4 FKSCore.C9sq := FKSCore.not_hasCompleteComponent 4

-- Repository statements (with their answer placeholder) and ours, printed for comparison:
#check @problem_1
#check @problem_1_solved
#check @problem_1.variants.dimension_four
#check @problem_1.variants.dimension_four_solved
#print axioms problem_1_solved
#print axioms problem_1.variants.dimension_four_solved
