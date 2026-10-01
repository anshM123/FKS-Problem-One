import Mathlib

/-!
# The square of the nine-cycle has no spherical representation in `ℝ⁴`

`C9sq` is the graph on `Fin 9` in which `i ~ j` iff `j - i ≡ ±1, ±2 (mod 9)` (the square of the
nine-cycle). It is connected, `4`-regular and not `K₅`.

`HasSphericalDimAtMost` and `HasCompleteComponent` are verbatim copies of the definitions in
`FormalConjectures/Arxiv/1802.03092/EmbeddingGraphs.lean` (Frankl, Kupavskii and Swanepoel,
*Embedding graphs in Euclidean space*, Problem 1).

Main results:
* `rep_not_injective`: if `x : Fin 9 → E` with `finrank ℝ E = 4`, all `⟪x i, x i⟫` equal to the
  same `c > 0`, and `⟪x i, x j⟫ = 0` whenever `i ~ j`, then `x` is not injective.
* `not_hasSphericalDimAtMost_C9sq`: `C9sq` has no spherical representation in `ℝ⁴`.
* `problem_1_false`, `problem_1_dim4_false`: the two questions have a negative answer.

Proof of `rep_not_injective`. The classes `{r, r + 3, r + 6}` are independent sets, and each of
their vertices has two neighbours in each other class. Note that `x 1, x 2 ⊥ x 0, x 3`,
`x 4, x 5 ⊥ x 3, x 6` and `x 7, x 8 ⊥ x 6, x 0`.
* `caseI`: if `x 3 ∥ x 0` (by the rotation `i ↦ i + 3` this covers every parallel pair of the class
  `{0, 3, 6}`), then either two vectors coincide at once, or `x 3 = -x 0` and `x 0, x 6` span a
  plane `D` whose orthogonal complement is spanned by `x 4, x 5` and contains `x 7, x 8`. Then
  `x 7 ∥ x 4`, `x 8 ∥ x 5`, and `⟪x 1, x 2⟫ = 0` forces `x 1 ∥ x 4` or `x 2 ∥ x 5`.
* `caseIII`: otherwise pick `u ≠ 0` orthogonal to `x 0, x 3, x 6`. It lies in the planes spanned by
  `x 1, x 2`, by `x 4, x 5` and by `x 7, x 8`: `u = p₁ x₁ + p₂ x₂ = p₄ x₄ + p₅ x₅ = p₇ x₇ + p₈ x₈`.
  With `w₁ = p₂ x₁ - p₁ x₂` etc. and `g₁₄ = ⟪w₁, w₄⟫` etc., the edges `2-4`, `5-7`, `8-1` give
  `m p₂ p₄ = g₁₄ p₁ p₅`, `m p₅ p₇ = g₄₇ p₄ p₈`, `m p₈ p₁ = g₇₁ p₇ p₂` with `m = ⟪u, u⟫ ≥ |g|`.
  Either `g₁₄ g₄₇ g₇₁ = m³`, and then `w₄, w₇ = ±w₁` and `x 4, x 7 ∥ x 1`, or the product
  `p₁ p₂ p₄ p₅ p₇ p₈` vanishes and the three equations force `x 1, x 4, x 7 ∥ u` or
  `x 2, x 5, x 8 ∥ u`.
In every case three vectors of equal norm lie on one line, so two of them are equal.
-/

namespace FKSCore

open scoped RealInnerProductSpace
open Module

/-! ## Verbatim copies of the definitions of the statement file -/

/-- A graph has spherical dimension at most $d$ if it admits an injective placement in
$\mathbb{R}^d$ on the sphere of radius $1/\sqrt{2}$ centred at the origin, with every edge
of length $1$. Non-adjacent vertices may also be at distance $1$. -/
def HasSphericalDimAtMost (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective f ∧
    (∀ v, ‖f v‖ = 1 / √2) ∧ ∀ u v, G.Adj u v → dist (f u) (f v) = 1

/-- Some connected component is isomorphic to $K_{d+1}$: its reachability class has
$d+1$ vertices, and any two distinct vertices in that class are adjacent. -/
def HasCompleteComponent (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ v : Fin n, Nonempty ({w : Fin n // G.Reachable v w} ≃ Fin (d + 1)) ∧
    ∀ a b, G.Reachable v a → G.Reachable v b → a ≠ b → G.Adj a b

/-! ## The square of the nine-cycle -/

/-- Adjacency in the square of the nine-cycle: `j - i ≡ 1, 2, 7 or 8 (mod 9)`. -/
def adjB (i j : Fin 9) : Bool :=
  (j.val + 9 - i.val) % 9 == 1 || (j.val + 9 - i.val) % 9 == 2 ||
    (j.val + 9 - i.val) % 9 == 7 || (j.val + 9 - i.val) % 9 == 8

theorem adjB_symm : ∀ a b : Fin 9, adjB a b = true → adjB b a = true := by decide

theorem adjB_irrefl : ∀ a : Fin 9, ¬ adjB a a = true := by decide

/-- The square of the nine-cycle. -/
def C9sq : SimpleGraph (Fin 9) where
  Adj i j := adjB i j = true
  symm := ⟨adjB_symm⟩
  loopless := ⟨adjB_irrefl⟩

instance instDecRelC9sq : DecidableRel C9sq.Adj :=
  fun i j => inferInstanceAs (Decidable (adjB i j = true))

/-- Every vertex of `C9sq` has degree `4`, for any decidability instance. -/
theorem maxDegree_le (inst : DecidableRel C9sq.Adj) :
    @SimpleGraph.maxDegree (Fin 9) C9sq _ inst ≤ 4 := by
  obtain rfl : inst = instDecRelC9sq := Subsingleton.elim _ _
  exact C9sq.maxDegree_le_of_forall_degree_le 4 (by decide)

theorem adj_succ : ∀ v : Fin 9, C9sq.Adj v (v + 1) := by decide

theorem adj_succ_three : ∀ v : Fin 9, C9sq.Adj (v + 1) (v + 3) := by decide

theorem not_adj_three : ∀ v : Fin 9, ¬ C9sq.Adj v (v + 3) := by decide

theorem ne_add_three : ∀ v : Fin 9, v ≠ v + 3 := by decide

/-- `C9sq` has no complete component (of any size): `v` and `v + 3` are joined by a path but are
not adjacent. -/
theorem not_hasCompleteComponent (d : ℕ) : ¬ HasCompleteComponent d C9sq := by
  rintro ⟨v, -, h⟩
  have hr : C9sq.Reachable v (v + 3) := (adj_succ v).reachable.trans (adj_succ_three v).reachable
  exact not_adj_three v (h v (v + 3) (SimpleGraph.Reachable.refl v) hr (ne_add_three v))

/-- Adjacency is invariant under the rotations by `3` and by `6`. -/
theorem adj_add_three : ∀ i j : Fin 9, C9sq.Adj (i + 3) (j + 3) ↔ C9sq.Adj i j := by decide

theorem adj_add_six : ∀ i j : Fin 9, C9sq.Adj (i + 6) (j + 6) ↔ C9sq.Adj i j := by decide

/-! ## Linear algebra in a four-dimensional inner product space -/

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Expansion of a vector in an orthogonal basis of a four-dimensional space. -/
theorem expand4 (hE : finrank ℝ E = 4) (e : Fin 4 → E) (hne : ∀ i, e i ≠ 0)
    (ho : Pairwise fun i j => ⟪e i, e j⟫ = 0) (v : E) :
    v = ∑ i, (⟪e i, v⟫ / ⟪e i, e i⟫) • e i := by
  have hli : LinearIndependent ℝ e := linearIndependent_of_ne_zero_of_inner_eq_zero hne ho
  have htop : Submodule.span ℝ (Set.range e) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hE])
  have hv : v ∈ Submodule.span ℝ (Set.range e) := by rw [htop]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  have hcoef : ∀ j, c j = ⟪e j, v⟫ / ⟪e j, e j⟫ := by
    intro j
    have hjj : ⟪e j, e j⟫ ≠ 0 := fun h => hne j (inner_self_eq_zero.mp h)
    rw [eq_div_iff hjj, ← hc, inner_sum, Finset.sum_eq_single j]
    · rw [real_inner_smul_right]
    · intro i _ hij
      rw [real_inner_smul_right, ho (Ne.symm hij), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  calc v = ∑ i, c i • e i := hc.symm
    _ = ∑ i, (⟪e i, v⟫ / ⟪e i, e i⟫) • e i :=
      Finset.sum_congr rfl (fun i _ => by rw [hcoef i])

/-- Expansion in an orthogonal frame `a, z, p, q`. -/
theorem frame_expand (hE : finrank ℝ E = 4) {a z p q : E}
    (ha : a ≠ 0) (hz : z ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (haz : ⟪a, z⟫ = 0) (hap : ⟪a, p⟫ = 0) (haq : ⟪a, q⟫ = 0)
    (hzp : ⟪z, p⟫ = 0) (hzq : ⟪z, q⟫ = 0) (hpq : ⟪p, q⟫ = 0) (v : E) :
    v = (⟪a, v⟫ / ⟪a, a⟫) • a + (⟪z, v⟫ / ⟪z, z⟫) • z +
      (⟪p, v⟫ / ⟪p, p⟫) • p + (⟪q, v⟫ / ⟪q, q⟫) • q := by
  have hza : ⟪z, a⟫ = 0 := by rw [real_inner_comm]; exact haz
  have hpa : ⟪p, a⟫ = 0 := by rw [real_inner_comm]; exact hap
  have hqa : ⟪q, a⟫ = 0 := by rw [real_inner_comm]; exact haq
  have hpz : ⟪p, z⟫ = 0 := by rw [real_inner_comm]; exact hzp
  have hqz : ⟪q, z⟫ = 0 := by rw [real_inner_comm]; exact hzq
  have hqp : ⟪q, p⟫ = 0 := by rw [real_inner_comm]; exact hpq
  have h := expand4 hE ![a, z, p, q] (by intro i; fin_cases i <;> simp [ha, hz, hp, hq]) (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all) v
  rw [Fin.sum_univ_four] at h
  simpa using h

/-- In a four-dimensional space, three vectors have a common nonzero orthogonal vector. -/
theorem exists_orth3 (hE : finrank ℝ E = 4) (a b e : E) :
    ∃ u : E, u ≠ 0 ∧ ⟪a, u⟫ = 0 ∧ ⟪b, u⟫ = 0 ∧ ⟪e, u⟫ = 0 := by
  have hK : finrank ℝ (Submodule.span ℝ (Set.range ![a, b, e])) ≤ 3 := by
    have := finrank_range_le_card (R := ℝ) ![a, b, e]
    rw [Fintype.card_fin] at this
    exact this
  set K := Submodule.span ℝ (Set.range ![a, b, e]) with hKdef
  have hsum := Submodule.finrank_add_finrank_orthogonal K
  have hKo : Kᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKo
  have hmem : ∀ i, ![a, b, e] i ∈ K := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨u, hu0, ?_, ?_, ?_⟩
  · simpa using Submodule.inner_right_of_mem_orthogonal (hmem 0) hu
  · simpa using Submodule.inner_right_of_mem_orthogonal (hmem 1) hu
  · simpa using Submodule.inner_right_of_mem_orthogonal (hmem 2) hu

end Geometry

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem sq_eq_one_of_smul {v a : E} {s c : ℝ} (hc : c ≠ 0) (ha : a = s • v)
    (hvv : ⟪v, v⟫ = c) (haa : ⟪a, a⟫ = c) : s ^ 2 = 1 := by
  rw [ha, real_inner_smul_left, real_inner_smul_right, hvv] at haa
  have h : (s ^ 2 - 1) * c = 0 := by linear_combination haa
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · exact absurd h hc

theorem eq_one_or_neg_one {s : ℝ} (hs : s ^ 2 = 1) : s = 1 ∨ s = -1 := by
  have h : (s - 1) * (s + 1) = 0 := by linear_combination hs
  rcases mul_eq_zero.mp h with h | h
  · left; linarith
  · right; linarith

/-- Three vectors of the same norm on one line: two of them coincide. -/
theorem three_on_line {v a b : E} {s t : ℝ} (ha : a = s • v) (hb : b = t • v)
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) : a = v ∨ b = v ∨ a = b := by
  rcases eq_one_or_neg_one hs with rfl | rfl
  · left; rw [ha, one_smul]
  rcases eq_one_or_neg_one ht with rfl | rfl
  · right; left; rw [hb, one_smul]
  · right; right; rw [ha, hb]

/-- If `k • a = r • u` and `k • b = s • u` with `k, r ≠ 0`, then `b = (s / r) • a`. -/
theorem smul_eq_of_smul_eq {u a b : E} {k r s : ℝ} (hk : k ≠ 0) (hr : r ≠ 0)
    (ha : k • a = r • u) (hb : k • b = s • u) : b = (s / r) • a := by
  apply smul_right_injective E hk
  show k • b = k • ((s / r) • a)
  rw [hb, smul_comm k (s / r) a, ha, smul_smul, div_mul_cancel₀ _ hr]

/-- The hypotheses: equal squared norms `c > 0`, and adjacent vertices orthogonal. -/
structure Rep (x : Fin 9 → E) (c : ℝ) : Prop where
  pos : 0 < c
  norm : ∀ i, ⟪x i, x i⟫ = c
  orth : ∀ i j, C9sq.Adj i j → ⟪x i, x j⟫ = 0

theorem Rep.ne_zero {x : Fin 9 → E} {c : ℝ} (hx : Rep x c) (i : Fin 9) : x i ≠ 0 := by
  intro h
  have := hx.norm i
  rw [h, inner_zero_left] at this
  exact hx.pos.ne this

/-- Rotating the indices by `3` preserves the hypotheses. -/
theorem Rep.shift3 {x : Fin 9 → E} {c : ℝ} (hx : Rep x c) : Rep (fun i => x (i + 3)) c :=
  ⟨hx.pos, fun _ => hx.norm _, fun i j h => hx.orth _ _ ((adj_add_three i j).mpr h)⟩

/-- Rotating the indices by `6` preserves the hypotheses. -/
theorem Rep.shift6 {x : Fin 9 → E} {c : ℝ} (hx : Rep x c) : Rep (fun i => x (i + 6)) c :=
  ⟨hx.pos, fun _ => hx.norm _, fun i j h => hx.orth _ _ ((adj_add_six i j).mpr h)⟩

end Basic

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Case I: `x 3` is a multiple of `x 0`. -/
theorem caseI (hE : finrank ℝ E = 4) {x : Fin 9 → E} {c : ℝ} (hx : Rep x c)
    (h03 : x 3 - (⟪x 0, x 3⟫ / c) • x 0 = 0) : ∃ i j, i ≠ j ∧ x i = x j := by
  have hc0 : c ≠ 0 := hx.pos.ne'
  have o := hx.orth
  have n := hx.norm
  have nz := hx.ne_zero
  have h3 : x 3 = (⟪x 0, x 3⟫ / c) • x 0 := sub_eq_zero.mp h03
  rcases eq_one_or_neg_one (sq_eq_one_of_smul hc0 h3 (n 0) (n 3)) with ht | ht
  · exact ⟨3, 0, by decide, by rw [h3, ht, one_smul]⟩
  have h3' : x 3 = -x 0 := by rw [h3, ht, neg_one_smul]
  by_cases hz : x 6 - (⟪x 0, x 6⟫ / c) • x 0 = 0
  · have h6 : x 6 = (⟪x 0, x 6⟫ / c) • x 0 := sub_eq_zero.mp hz
    rcases eq_one_or_neg_one (sq_eq_one_of_smul hc0 h6 (n 0) (n 6)) with hs | hs
    · exact ⟨6, 0, by decide, by rw [h6, hs, one_smul]⟩
    · exact ⟨6, 3, by decide, by rw [h6, hs, neg_one_smul, h3']⟩
  generalize hzdef : x 6 - (⟪x 0, x 6⟫ / c) • x 0 = z at hz
  have h04 : ⟪x 0, x 4⟫ = 0 := by
    have h := o 3 4 (by decide)
    rw [h3', inner_neg_left] at h
    linarith
  have h05 : ⟪x 0, x 5⟫ = 0 := by
    have h := o 3 5 (by decide)
    rw [h3', inner_neg_left] at h
    linarith
  have h0z : ⟪x 0, z⟫ = 0 := by
    rw [← hzdef, inner_sub_right, real_inner_smul_right, n 0, div_mul_cancel₀ _ hc0, sub_self]
  have hzx : ∀ j, ⟪x 6, x j⟫ = 0 → ⟪x 0, x j⟫ = 0 → ⟪z, x j⟫ = 0 := by
    intro j h6 h0
    rw [← hzdef, inner_sub_left, real_inner_smul_left, h6, h0]
    ring
  have hz4 : ⟪z, x 4⟫ = 0 := hzx 4 (o 6 4 (by decide)) h04
  have hz5 : ⟪z, x 5⟫ = 0 := hzx 5 (o 6 5 (by decide)) h05
  have h45 : ⟪x 4, x 5⟫ = 0 := o 4 5 (by decide)
  have F := frame_expand hE (nz 0) hz (nz 4) (nz 5) h0z h04 h05 hz4 hz5 h45
  -- `x 7` and `x 8`
  have h07 : ⟪x 0, x 7⟫ = 0 := o 0 7 (by decide)
  have h08 : ⟪x 0, x 8⟫ = 0 := o 0 8 (by decide)
  obtain ⟨α, e7⟩ : ∃ α : ℝ, x 7 = α • x 4 := by
    have h := F (x 7)
    rw [h07, hzx 7 (o 6 7 (by decide)) h07, o 5 7 (by decide)] at h
    exact ⟨⟪x 4, x 7⟫ / ⟪x 4, x 4⟫, by simpa using h⟩
  have hα : α ^ 2 = 1 := sq_eq_one_of_smul hc0 e7 (n 4) (n 7)
  have hα0 : α ≠ 0 := by rintro rfl; norm_num at hα
  have h48 : ⟪x 4, x 8⟫ = 0 := by
    have h := o 7 8 (by decide)
    rw [e7, real_inner_smul_left] at h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hα0
    · exact h
  obtain ⟨β, e8⟩ : ∃ β : ℝ, x 8 = β • x 5 := by
    have h := F (x 8)
    rw [h08, hzx 8 (o 6 8 (by decide)) h08, h48] at h
    exact ⟨⟪x 5, x 8⟫ / ⟪x 5, x 5⟫, by simpa using h⟩
  have hβ : β ^ 2 = 1 := sq_eq_one_of_smul hc0 e8 (n 5) (n 8)
  have hβ0 : β ≠ 0 := by rintro rfl; norm_num at hβ
  -- `x 1` and `x 2`
  have h51 : ⟪x 5, x 1⟫ = 0 := by
    have h := o 8 1 (by decide)
    rw [e8, real_inner_smul_left] at h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hβ0
    · exact h
  obtain ⟨μ₁, a₁, e1⟩ : ∃ μ₁ a₁ : ℝ, x 1 = μ₁ • z + a₁ • x 4 := by
    have h := F (x 1)
    rw [o 0 1 (by decide), h51] at h
    exact ⟨⟪z, x 1⟫ / ⟪z, z⟫, ⟪x 4, x 1⟫ / ⟪x 4, x 4⟫, by simpa using h⟩
  obtain ⟨μ₂, b₂, e2⟩ : ∃ μ₂ b₂ : ℝ, x 2 = μ₂ • z + b₂ • x 5 := by
    have h := F (x 2)
    rw [o 0 2 (by decide), o 4 2 (by decide)] at h
    exact ⟨⟪z, x 2⟫ / ⟪z, z⟫, ⟪x 5, x 2⟫ / ⟪x 5, x 5⟫, by simpa using h⟩
  have hzz : ⟪z, z⟫ ≠ 0 := fun h => hz (inner_self_eq_zero.mp h)
  have h4z : ⟪x 4, z⟫ = 0 := by rw [real_inner_comm]; exact hz4
  have key : μ₁ * μ₂ = 0 := by
    have h := o 1 2 (by decide)
    rw [e1, e2] at h
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hz5, h4z, h45, mul_zero, add_zero] at h
    have h' : (μ₁ * μ₂) * ⟪z, z⟫ = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h' | h'
    · exact h'
    · exact absurd h' hzz
  rcases mul_eq_zero.mp key with hμ | hμ
  · have e1' : x 1 = a₁ • x 4 := by rw [e1, hμ, zero_smul, zero_add]
    have ha₁ : a₁ ^ 2 = 1 := sq_eq_one_of_smul hc0 e1' (n 4) (n 1)
    rcases three_on_line e1' e7 ha₁ hα with h | h | h
    · exact ⟨1, 4, by decide, h⟩
    · exact ⟨7, 4, by decide, h⟩
    · exact ⟨1, 7, by decide, h⟩
  · have e2' : x 2 = b₂ • x 5 := by rw [e2, hμ, zero_smul, zero_add]
    have hb₂ : b₂ ^ 2 = 1 := sq_eq_one_of_smul hc0 e2' (n 5) (n 2)
    rcases three_on_line e2' e8 hb₂ hβ with h | h | h
    · exact ⟨2, 5, by decide, h⟩
    · exact ⟨8, 5, by decide, h⟩
    · exact ⟨2, 8, by decide, h⟩

/-- The propagation of a vanishing coefficient in case III. -/
theorem chase {p₁ p₂ p₄ p₅ p₇ p₈ m k g₁₄ g₄₇ g₇₁ : ℝ} (hm : 0 < m) (hk : 0 < k)
    (k₁ : p₁ ^ 2 + p₂ ^ 2 = k) (k₄ : p₄ ^ 2 + p₅ ^ 2 = k) (k₇ : p₇ ^ 2 + p₈ ^ 2 = k)
    (E₁ : p₂ * p₄ * m = p₁ * p₅ * g₁₄) (E₂ : p₅ * p₇ * m = p₄ * p₈ * g₄₇)
    (E₃ : p₈ * p₁ * m = p₇ * p₂ * g₇₁) (hP : p₁ * p₂ * p₄ * p₅ * p₇ * p₈ = 0) :
    (p₁ = 0 ∧ p₄ = 0 ∧ p₇ = 0) ∨ (p₂ = 0 ∧ p₅ = 0 ∧ p₈ = 0) := by
  have hm0 : m ≠ 0 := hm.ne'
  -- if one coordinate of a pair vanishes, the other does not
  have nz : ∀ a b : ℝ, a ^ 2 + b ^ 2 = k → a = 0 → b ≠ 0 := by
    intro a b h ha hb
    rw [ha, hb] at h
    linarith
  -- `a * b * m = 0` with `a ≠ 0` gives `b = 0`
  have cancel : ∀ a b : ℝ, a ≠ 0 → a * b * m = 0 → b = 0 := by
    intro a b ha h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h ha
      · exact h
    · exact absurd h hm0
  have A : p₁ = 0 → p₄ = 0 := fun h =>
    cancel p₂ p₄ (nz p₁ p₂ k₁ h) (by rw [E₁, h]; ring)
  have B : p₄ = 0 → p₇ = 0 := fun h =>
    cancel p₅ p₇ (nz p₄ p₅ k₄ h) (by rw [E₂, h]; ring)
  have C : p₇ = 0 → p₁ = 0 := fun h =>
    cancel p₈ p₁ (nz p₇ p₈ k₇ h) (by rw [E₃, h]; ring)
  have D : p₂ = 0 → p₈ = 0 := fun h => by
    have hp₁ : p₁ ≠ 0 := nz p₂ p₁ (by linarith) h
    exact cancel p₁ p₈ hp₁ (by rw [show p₁ * p₈ * m = p₈ * p₁ * m by ring, E₃, h]; ring)
  have E' : p₈ = 0 → p₅ = 0 := fun h => by
    have hp₇ : p₇ ≠ 0 := nz p₈ p₇ (by linarith) h
    exact cancel p₇ p₅ hp₇ (by rw [show p₇ * p₅ * m = p₅ * p₇ * m by ring, E₂, h]; ring)
  have F : p₅ = 0 → p₂ = 0 := fun h => by
    have hp₄ : p₄ ≠ 0 := nz p₅ p₄ (by linarith) h
    exact cancel p₄ p₂ hp₄ (by rw [show p₄ * p₂ * m = p₂ * p₄ * m by ring, E₁, h]; ring)
  simp only [mul_eq_zero] at hP
  rcases hP with ((((h | h) | h) | h) | h) | h
  · exact Or.inl ⟨h, A h, B (A h)⟩
  · exact Or.inr ⟨h, E' (D h), D h⟩
  · exact Or.inl ⟨C (B h), h, B h⟩
  · exact Or.inr ⟨F h, h, D (F h)⟩
  · exact Or.inl ⟨C h, A (C h), h⟩
  · exact Or.inr ⟨F (E' h), E' h, h⟩

/-- `g ^ 2 ≤ m ^ 2`, `g' ^ 2 ≤ m ^ 2`, `g'' ^ 2 ≤ m ^ 2` and `g g' g'' = m ^ 3` give
`g ^ 2 = m ^ 2`. -/
theorem sq_eq_of_prod {m g g' g'' : ℝ} (hm : 0 < m) (h : g ^ 2 ≤ m ^ 2) (h' : g' ^ 2 ≤ m ^ 2)
    (h'' : g'' ^ 2 ≤ m ^ 2) (hp : g * g' * g'' = m ^ 3) : g ^ 2 = m ^ 2 := by
  have h1 : g' ^ 2 * g'' ^ 2 ≤ m ^ 2 * m ^ 2 :=
    mul_le_mul h' h'' (sq_nonneg _) (sq_nonneg _)
  have h2 : m ^ 2 * (m ^ 2 * m ^ 2) = g ^ 2 * (g' ^ 2 * g'' ^ 2) := by
    rw [show g ^ 2 * (g' ^ 2 * g'' ^ 2) = (g * g' * g'') ^ 2 by ring, hp]
    ring
  have h3 : m ^ 2 * (m ^ 2 * m ^ 2) ≤ g ^ 2 * (m ^ 2 * m ^ 2) := by
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hm4 : 0 < m ^ 2 * m ^ 2 := by positivity
  have h4 : m ^ 2 ≤ g ^ 2 := le_of_mul_le_mul_right h3 hm4
  linarith

/-- Case III: no two vectors of the class `{0, 3, 6}` are parallel. -/
theorem caseIII (hE : finrank ℝ E = 4) {x : Fin 9 → E} {c : ℝ} (hx : Rep x c)
    (h03 : x 3 - (⟪x 0, x 3⟫ / c) • x 0 ≠ 0)
    (h36 : x 6 - (⟪x 3, x 6⟫ / c) • x 3 ≠ 0)
    (h60 : x 0 - (⟪x 6, x 0⟫ / c) • x 6 ≠ 0) : ∃ i j, i ≠ j ∧ x i = x j := by
  have hc0 : c ≠ 0 := hx.pos.ne'
  have o := hx.orth
  have n := hx.norm
  have nz := hx.ne_zero
  obtain ⟨u, hu, hu0, hu3, hu6⟩ := exists_orth3 hE (x 0) (x 3) (x 6)
  -- residual of `x j` against `x i`, and its orthogonality properties
  have res : ∀ i j : Fin 9, ∀ w : E, ⟪x i, w⟫ = 0 → ⟪x j, w⟫ = 0 →
      ⟪x j - (⟪x i, x j⟫ / c) • x i, w⟫ = 0 := by
    intro i j w hi hj
    rw [inner_sub_left, real_inner_smul_left, hi, hj]
    ring
  have res0 : ∀ i j : Fin 9, ⟪x i, x j - (⟪x i, x j⟫ / c) • x i⟫ = 0 := by
    intro i j
    rw [inner_sub_right, real_inner_smul_right, n i, div_mul_cancel₀ _ hc0, sub_self]
  -- the three expansions of `u`
  obtain ⟨p₁, p₂, f₁⟩ : ∃ p₁ p₂ : ℝ, u = p₁ • x 1 + p₂ • x 2 := by
    have h := frame_expand hE (nz 0) h03 (nz 1) (nz 2) (res0 0 3) (o 0 1 (by decide))
      (o 0 2 (by decide)) (res 0 3 (x 1) (o 0 1 (by decide)) (o 3 1 (by decide)))
      (res 0 3 (x 2) (o 0 2 (by decide)) (o 3 2 (by decide))) (o 1 2 (by decide)) u
    rw [hu0, res 0 3 u hu0 hu3] at h
    exact ⟨⟪x 1, u⟫ / ⟪x 1, x 1⟫, ⟪x 2, u⟫ / ⟪x 2, x 2⟫, by simpa using h⟩
  obtain ⟨p₄, p₅, f₄⟩ : ∃ p₄ p₅ : ℝ, u = p₄ • x 4 + p₅ • x 5 := by
    have h := frame_expand hE (nz 3) h36 (nz 4) (nz 5) (res0 3 6) (o 3 4 (by decide))
      (o 3 5 (by decide)) (res 3 6 (x 4) (o 3 4 (by decide)) (o 6 4 (by decide)))
      (res 3 6 (x 5) (o 3 5 (by decide)) (o 6 5 (by decide))) (o 4 5 (by decide)) u
    rw [hu3, res 3 6 u hu3 hu6] at h
    exact ⟨⟪x 4, u⟫ / ⟪x 4, x 4⟫, ⟪x 5, u⟫ / ⟪x 5, x 5⟫, by simpa using h⟩
  obtain ⟨p₇, p₈, f₇⟩ : ∃ p₇ p₈ : ℝ, u = p₇ • x 7 + p₈ • x 8 := by
    have h := frame_expand hE (nz 6) h60 (nz 7) (nz 8) (res0 6 0) (o 6 7 (by decide))
      (o 6 8 (by decide)) (res 6 0 (x 7) (o 6 7 (by decide)) (o 0 7 (by decide)))
      (res 6 0 (x 8) (o 6 8 (by decide)) (o 0 8 (by decide))) (o 7 8 (by decide)) u
    rw [hu6, res 6 0 u hu6 hu0] at h
    exact ⟨⟪x 7, u⟫ / ⟪x 7, x 7⟫, ⟪x 8, u⟫ / ⟪x 8, x 8⟫, by simpa using h⟩
  -- squared norms
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = ⟪u, u⟫ := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hmdef]; exact real_inner_self_pos.mpr hu
  have hm0 : m ≠ 0 := hm.ne'
  have pair_norm : ∀ (a b : Fin 9) (s t : ℝ), C9sq.Adj a b → u = s • x a + t • x b →
      m = c * (s ^ 2 + t ^ 2) := by
    intro a b s t hab hf
    have hba : ⟪x b, x a⟫ = 0 := o b a hab.symm
    rw [hmdef, hf]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      n a, n b, o a b hab, hba]
    ring
  have m₁ := pair_norm 1 2 p₁ p₂ (by decide) f₁
  have m₄ := pair_norm 4 5 p₄ p₅ (by decide) f₄
  have m₇ := pair_norm 7 8 p₇ p₈ (by decide) f₇
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = p₁ ^ 2 + p₂ ^ 2 := ⟨_, rfl⟩
  have hk : 0 < k := by
    have : 0 < c * k := by rw [hkdef, ← m₁]; exact hm
    exact pos_of_mul_pos_right this hx.pos.le
  have hk0 : k ≠ 0 := hk.ne'
  have k₄ : p₄ ^ 2 + p₅ ^ 2 = k := by
    have h : c * (p₄ ^ 2 + p₅ ^ 2) = c * k := by rw [← m₄, hkdef, ← m₁]
    exact mul_left_cancel₀ hc0 h
  have k₇ : p₇ ^ 2 + p₈ ^ 2 = k := by
    have h : c * (p₇ ^ 2 + p₈ ^ 2) = c * k := by rw [← m₇, hkdef, ← m₁]
    exact mul_left_cancel₀ hc0 h
  -- the vectors `w`
  have uw : ∀ (a b : Fin 9) (s t : ℝ), C9sq.Adj a b → u = s • x a + t • x b →
      ⟪u, t • x a - s • x b⟫ = 0 := by
    intro a b s t hab hf
    have hba : ⟪x b, x a⟫ = 0 := o b a hab.symm
    rw [hf]
    simp only [inner_add_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      n a, n b, o a b hab, hba]
    ring
  have ww : ∀ (a b : Fin 9) (s t : ℝ), C9sq.Adj a b →
      ⟪t • x a - s • x b, t • x a - s • x b⟫ = c * (s ^ 2 + t ^ 2) := by
    intro a b s t hab
    have hba : ⟪x b, x a⟫ = 0 := o b a hab.symm
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      n a, n b, o a b hab, hba]
    ring
  obtain ⟨w₁, hw₁⟩ : ∃ w : E, w = p₂ • x 1 - p₁ • x 2 := ⟨_, rfl⟩
  obtain ⟨w₄, hw₄⟩ : ∃ w : E, w = p₅ • x 4 - p₄ • x 5 := ⟨_, rfl⟩
  obtain ⟨w₇, hw₇⟩ : ∃ w : E, w = p₈ • x 7 - p₇ • x 8 := ⟨_, rfl⟩
  have uw₁ : ⟪u, w₁⟫ = 0 := by rw [hw₁]; exact uw 1 2 p₁ p₂ (by decide) f₁
  have uw₄ : ⟪u, w₄⟫ = 0 := by rw [hw₄]; exact uw 4 5 p₄ p₅ (by decide) f₄
  have uw₇ : ⟪u, w₇⟫ = 0 := by rw [hw₇]; exact uw 7 8 p₇ p₈ (by decide) f₇
  have w₁u : ⟪w₁, u⟫ = 0 := by rw [real_inner_comm]; exact uw₁
  have w₄u : ⟪w₄, u⟫ = 0 := by rw [real_inner_comm]; exact uw₄
  have w₇u : ⟪w₇, u⟫ = 0 := by rw [real_inner_comm]; exact uw₇
  have ww₁ : ⟪w₁, w₁⟫ = m := by rw [m₁, hw₁]; exact ww 1 2 p₁ p₂ (by decide)
  have ww₄ : ⟪w₄, w₄⟫ = m := by rw [m₄, hw₄]; exact ww 4 5 p₄ p₅ (by decide)
  have ww₇ : ⟪w₇, w₇⟫ = m := by rw [m₇, hw₇]; exact ww 7 8 p₇ p₈ (by decide)
  -- the vectors `x` in terms of `u` and `w`
  have v₁ : k • x 1 = p₁ • u + p₂ • w₁ := by rw [hkdef, hw₁, f₁]; module
  have v₂ : k • x 2 = p₂ • u - p₁ • w₁ := by rw [hkdef, hw₁, f₁]; module
  have v₄ : k • x 4 = p₄ • u + p₅ • w₄ := by rw [← k₄, hw₄, f₄]; module
  have v₅ : k • x 5 = p₅ • u - p₄ • w₄ := by rw [← k₄, hw₄, f₄]; module
  have v₇ : k • x 7 = p₇ • u + p₈ • w₇ := by rw [← k₇, hw₇, f₇]; module
  have v₈ : k • x 8 = p₈ • u - p₇ • w₇ := by rw [← k₇, hw₇, f₇]; module
  -- the three remaining edges
  have edge : ∀ (a b : Fin 9), C9sq.Adj a b → ⟪k • x a, k • x b⟫ = 0 := by
    intro a b hab
    rw [real_inner_smul_left, real_inner_smul_right, o a b hab]
    ring
  have E₁ : p₂ * p₄ * m = p₁ * p₅ * ⟪w₁, w₄⟫ := by
    have h := edge 2 4 (by decide)
    rw [v₂, v₄] at h
    simp only [inner_sub_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      uw₄, w₁u, ← hmdef] at h
    linear_combination h
  have E₂ : p₅ * p₇ * m = p₄ * p₈ * ⟪w₄, w₇⟫ := by
    have h := edge 5 7 (by decide)
    rw [v₅, v₇] at h
    simp only [inner_sub_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      uw₇, w₄u, ← hmdef] at h
    linear_combination h
  have E₃ : p₈ * p₁ * m = p₇ * p₂ * ⟪w₇, w₁⟫ := by
    have h := edge 8 1 (by decide)
    rw [v₈, v₁] at h
    simp only [inner_sub_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      uw₁, w₇u, ← hmdef] at h
    linear_combination h
  -- Cauchy-Schwarz for the `w`
  have cs : ∀ w w' : E, ⟪w, w⟫ = m → ⟪w', w'⟫ = m → ⟪w, w'⟫ ^ 2 ≤ m ^ 2 := by
    intro w w' hw hw'
    have h1 := real_inner_self_nonneg (x := w - w')
    have h2 := real_inner_self_nonneg (x := w + w')
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, hw, hw',
      real_inner_comm w w'] at h1 h2
    nlinarith
  have cs₁₄ := cs w₁ w₄ ww₁ ww₄
  have cs₄₇ := cs w₄ w₇ ww₄ ww₇
  have cs₇₁ := cs w₇ w₁ ww₇ ww₁
  -- if `⟪w, w'⟫ ^ 2 = m ^ 2` then `w' = (⟪w, w'⟫ / m) • w`
  have par : ∀ w w' : E, ⟪w, w⟫ = m → ⟪w', w'⟫ = m → ⟪w, w'⟫ ^ 2 = m ^ 2 →
      w' = (⟪w, w'⟫ / m) • w := by
    intro w w' hw hw' hg
    have hεm : ⟪w, w'⟫ / m * m = ⟪w, w'⟫ := div_mul_cancel₀ _ hm0
    have hεg : ⟪w, w'⟫ / m * ⟪w, w'⟫ = m := by
      rw [div_mul_eq_mul_div, ← sq, hg, sq, mul_div_assoc, div_self hm0, mul_one]
    have h : ⟪w' - (⟪w, w'⟫ / m) • w, w' - (⟪w, w'⟫ / m) • w⟫ = 0 := by
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        hw, hw', real_inner_comm w w']
      linear_combination (⟪w, w'⟫ / m) * hεm - hεg
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h)
  by_cases hG : ⟪w₁, w₄⟫ * ⟪w₄, w₇⟫ * ⟪w₇, w₁⟫ = m ^ 3
  · -- equality case: `w₄` and `w₇` are multiples of `w₁`
    have g₁₄ : ⟪w₁, w₄⟫ ^ 2 = m ^ 2 := sq_eq_of_prod hm cs₁₄ cs₄₇ cs₇₁ hG
    have g₇₁ : ⟪w₇, w₁⟫ ^ 2 = m ^ 2 :=
      sq_eq_of_prod hm cs₇₁ cs₁₄ cs₄₇ (by rw [← hG]; ring)
    have g₁₇ : ⟪w₁, w₇⟫ ^ 2 = m ^ 2 := by rw [real_inner_comm]; exact g₇₁
    have hw₄₁ : w₄ = (⟪w₁, w₄⟫ / m) • w₁ := par w₁ w₄ ww₁ ww₄ g₁₄
    have hw₇₁ : w₇ = (⟪w₁, w₇⟫ / m) • w₁ := par w₁ w₇ ww₁ ww₇ g₁₇
    obtain ⟨ε₄, hε₄⟩ : ∃ ε : ℝ, ε = ⟪w₁, w₄⟫ / m := ⟨_, rfl⟩
    obtain ⟨ε₇, hε₇⟩ : ∃ ε : ℝ, ε = ⟪w₁, w₇⟫ / m := ⟨_, rfl⟩
    rw [← hε₄] at hw₄₁
    rw [← hε₇] at hw₇₁
    have hε₇sq : ε₇ ^ 2 = 1 := by rw [hε₇, div_pow, g₁₇, div_self (pow_ne_zero 2 hm0)]
    have g14e : ⟪w₁, w₄⟫ = ε₄ * m := by rw [hε₄, div_mul_cancel₀ _ hm0]
    have g71e : ⟪w₇, w₁⟫ = ε₇ * m := by rw [real_inner_comm, hε₇, div_mul_cancel₀ _ hm0]
    have E₁' : p₂ * p₄ = ε₄ * p₁ * p₅ := by
      have h : p₂ * p₄ * m = (ε₄ * p₁ * p₅) * m := by rw [E₁, g14e]; ring
      exact mul_right_cancel₀ hm0 h
    have E₃' : p₈ * p₁ = ε₇ * p₇ * p₂ := by
      have h : p₈ * p₁ * m = (ε₇ * p₇ * p₂) * m := by rw [E₃, g71e]; ring
      exact mul_right_cancel₀ hm0 h
    -- `x 4 = λ • x 1` and `x 7 = λ' • x 1`
    have l₁ : (p₁ * p₄ + ε₄ * p₂ * p₅) / k * p₁ = p₄ := by
      rw [div_mul_eq_mul_div, div_eq_iff hk0]
      linear_combination (-p₂) * E₁' - p₄ * hkdef
    have l₂ : (p₁ * p₄ + ε₄ * p₂ * p₅) / k * p₂ = p₅ * ε₄ := by
      rw [div_mul_eq_mul_div, div_eq_iff hk0]
      linear_combination p₁ * E₁' - p₅ * ε₄ * hkdef
    have l₃ : (p₁ * p₇ + ε₇ * p₂ * p₈) / k * p₁ = p₇ := by
      rw [div_mul_eq_mul_div, div_eq_iff hk0]
      linear_combination (ε₇ * p₂) * E₃' + (p₇ * p₂ ^ 2) * hε₇sq - p₇ * hkdef
    have l₄ : (p₁ * p₇ + ε₇ * p₂ * p₈) / k * p₂ = p₈ * ε₇ := by
      rw [div_mul_eq_mul_div, div_eq_iff hk0]
      linear_combination (-ε₇ * p₁) * E₃' - (p₁ * p₂ * p₇) * hε₇sq - p₈ * ε₇ * hkdef
    have e4 : x 4 = ((p₁ * p₄ + ε₄ * p₂ * p₅) / k) • x 1 := by
      apply smul_right_injective E hk0
      show k • x 4 = k • (((p₁ * p₄ + ε₄ * p₂ * p₅) / k) • x 1)
      rw [smul_comm k ((p₁ * p₄ + ε₄ * p₂ * p₅) / k) (x 1), v₁, v₄, hw₄₁]
      simp only [smul_add, smul_smul]
      rw [l₁, l₂]
    have e7 : x 7 = ((p₁ * p₇ + ε₇ * p₂ * p₈) / k) • x 1 := by
      apply smul_right_injective E hk0
      show k • x 7 = k • (((p₁ * p₇ + ε₇ * p₂ * p₈) / k) • x 1)
      rw [smul_comm k ((p₁ * p₇ + ε₇ * p₂ * p₈) / k) (x 1), v₁, v₇, hw₇₁]
      simp only [smul_add, smul_smul]
      rw [l₃, l₄]
    have s4 := sq_eq_one_of_smul hc0 e4 (n 1) (n 4)
    have s7 := sq_eq_one_of_smul hc0 e7 (n 1) (n 7)
    rcases three_on_line e4 e7 s4 s7 with h | h | h
    · exact ⟨4, 1, by decide, h⟩
    · exact ⟨7, 1, by decide, h⟩
    · exact ⟨4, 7, by decide, h⟩
  · -- otherwise one of the coefficients vanishes
    have hP : p₁ * p₂ * p₄ * p₅ * p₇ * p₈ = 0 := by
      have h : (m ^ 3 - ⟪w₁, w₄⟫ * ⟪w₄, w₇⟫ * ⟪w₇, w₁⟫) * (p₁ * p₂ * p₄ * p₅ * p₇ * p₈) = 0 := by
        linear_combination (p₅ * p₇ * m * (p₈ * p₁ * m)) * E₁ +
          (p₁ * p₅ * ⟪w₁, w₄⟫ * (p₈ * p₁ * m)) * E₂ +
          (p₁ * p₅ * ⟪w₁, w₄⟫ * (p₄ * p₈ * ⟪w₄, w₇⟫)) * E₃
      rcases mul_eq_zero.mp h with h | h
      · exact absurd (by linarith) hG
      · exact h
    rcases chase hm hk hkdef.symm k₄ k₇ E₁ E₂ E₃ hP with ⟨h1, h4, h7⟩ | ⟨h2, h5, h8⟩
    · have a2 : k • x 2 = p₂ • u := by rw [v₂, h1, zero_smul, sub_zero]
      have a5 : k • x 5 = p₅ • u := by rw [v₅, h4, zero_smul, sub_zero]
      have a8 : k • x 8 = p₈ • u := by rw [v₈, h7, zero_smul, sub_zero]
      have hp₂ : p₂ ≠ 0 := by
        intro h
        have : k = 0 := by rw [hkdef, h1, h]; ring
        exact hk0 this
      have e5 := smul_eq_of_smul_eq hk0 hp₂ a2 a5
      have e8 := smul_eq_of_smul_eq hk0 hp₂ a2 a8
      have s5 := sq_eq_one_of_smul hc0 e5 (n 2) (n 5)
      have s8 := sq_eq_one_of_smul hc0 e8 (n 2) (n 8)
      rcases three_on_line e5 e8 s5 s8 with h | h | h
      · exact ⟨5, 2, by decide, h⟩
      · exact ⟨8, 2, by decide, h⟩
      · exact ⟨5, 8, by decide, h⟩
    · have a1 : k • x 1 = p₁ • u := by rw [v₁, h2, zero_smul, add_zero]
      have a4 : k • x 4 = p₄ • u := by rw [v₄, h5, zero_smul, add_zero]
      have a7 : k • x 7 = p₇ • u := by rw [v₇, h8, zero_smul, add_zero]
      have hp₁ : p₁ ≠ 0 := by
        intro h
        have : k = 0 := by rw [hkdef, h2, h]; ring
        exact hk0 this
      have e4 := smul_eq_of_smul_eq hk0 hp₁ a1 a4
      have e7 := smul_eq_of_smul_eq hk0 hp₁ a1 a7
      have s4 := sq_eq_one_of_smul hc0 e4 (n 1) (n 4)
      have s7 := sq_eq_one_of_smul hc0 e7 (n 1) (n 7)
      rcases three_on_line e4 e7 s4 s7 with h | h | h
      · exact ⟨4, 1, by decide, h⟩
      · exact ⟨7, 1, by decide, h⟩
      · exact ⟨4, 7, by decide, h⟩

/-- **Main lemma.** An orthogonal representation of `C9sq` by vectors of equal positive norm in a
four-dimensional space is never injective. -/
theorem rep_not_injective (hE : finrank ℝ E = 4) {x : Fin 9 → E} {c : ℝ} (hx : Rep x c) :
    ∃ i j, i ≠ j ∧ x i = x j := by
  by_cases h03 : x 3 - (⟪x 0, x 3⟫ / c) • x 0 = 0
  · exact caseI hE hx h03
  by_cases h36 : x 6 - (⟪x 3, x 6⟫ / c) • x 3 = 0
  · obtain ⟨i, j, hij, h⟩ := caseI hE hx.shift3 (by
      show x (3 + 3) - (⟪x (0 + 3), x (3 + 3)⟫ / c) • x (0 + 3) = 0
      rw [show (3 : Fin 9) + 3 = 6 by decide, show (0 : Fin 9) + 3 = 3 by decide]
      exact h36)
    exact ⟨i + 3, j + 3, fun h' => hij (add_right_cancel h'), h⟩
  by_cases h60 : x 0 - (⟪x 6, x 0⟫ / c) • x 6 = 0
  · obtain ⟨i, j, hij, h⟩ := caseI hE hx.shift6 (by
      show x (3 + 6) - (⟪x (0 + 6), x (3 + 6)⟫ / c) • x (0 + 6) = 0
      rw [show (3 : Fin 9) + 6 = 0 by decide, show (0 : Fin 9) + 6 = 6 by decide]
      exact h60)
    exact ⟨i + 6, j + 6, fun h' => hij (add_right_cancel h'), h⟩
  exact caseIII hE hx h03 h36 h60

end Main

/-! ## Spherical representations -/

/-- `C9sq` has no spherical representation in `ℝ⁴`. -/
theorem not_hasSphericalDimAtMost_C9sq : ¬ HasSphericalDimAtMost 4 C9sq := by
  rintro ⟨f, hinj, hnorm, hdist⟩
  have hn : ∀ i, ⟪f i, f i⟫ = 1 / 2 := by
    intro i
    rw [real_inner_self_eq_norm_sq, hnorm i, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have ho : ∀ i j, C9sq.Adj i j → ⟪f i, f j⟫ = 0 := by
    intro i j h
    have h1 := hdist i j h
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_sq_real (f i) (f j)
    rw [h1, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hn i, hn j] at h2
    norm_num at h2
    linarith
  obtain ⟨i, j, hij, h⟩ := rep_not_injective finrank_euclideanSpace_fin
    (⟨by norm_num, hn, ho⟩ : Rep f (1 / 2))
  exact hij (hinj h)

open scoped Classical in
/-- FKS Problem 1 has a negative answer: `C9sq` is a counterexample for `d = 4`. -/
theorem problem_1_false :
    ¬ ∀ d : ℕ, 3 < d → ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.maxDegree ≤ d → ¬ HasCompleteComponent d G → HasSphericalDimAtMost d G :=
  fun h => not_hasSphericalDimAtMost_C9sq
    (h 4 (by norm_num) 9 C9sq (maxDegree_le _) (not_hasCompleteComponent 4))

open scoped Classical in
/-- The `d = 4` instance of FKS Problem 1 has a negative answer. -/
theorem problem_1_dim4_false :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.maxDegree ≤ 4 → ¬ HasCompleteComponent 4 G → HasSphericalDimAtMost 4 G :=
  fun h => not_hasSphericalDimAtMost_C9sq (h 9 C9sq (maxDegree_le _) (not_hasCompleteComponent 4))

end FKSCore

#print axioms FKSCore.problem_1_false
#print axioms FKSCore.problem_1_dim4_false
