import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-37»
/-
For a cone K subseteq ℝ^n, its dual cone is K* = {y ∈ ℝ^n | xᵀ y > = 0 for all x in K}.
-/
def dualCone {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  { y | ∀ x, x ∈ K → 0 ≤ dotProduct x y }

/-
A cone C subseteq ℝ^n is pointed if for every y in C, the condition - y in C implies y = 0.
-/
def IsPointed {n : ℕ} (C : Set (Fin n → ℝ)) : Prop :=
  ∀ y, y ∈ C → -y ∈ C → y = 0

/-- A vector in both a dual cone and its negation annihilates every vector in the primal cone. -/
lemma dualCone_dotProduct_eq_zero_of_mem_and_neg_mem {n : ℕ} {K : Set (Fin n → ℝ)}
    {y x : Fin n → ℝ} (hy : y ∈ dualCone K) (hyneg : -y ∈ dualCone K) (hx : x ∈ K) :
    dotProduct x y = 0 := by
  -- Unpack both dual-cone memberships into the corresponding nonnegativity statements.
  have hy' : ∀ z, z ∈ K → 0 ≤ dotProduct z y := by
    simpa [dualCone] using hy
  have hyneg' : ∀ z, z ∈ K → 0 ≤ dotProduct z (-y) := by
    simpa [dualCone] using hyneg
  have hxy_nonneg : 0 ≤ dotProduct x y := hy' x hx
  -- Rewriting the dot product against `-y` gives the complementary upper bound.
  have hxy_nonpos : dotProduct x y ≤ 0 := by
    simpa [dotProduct_neg] using hyneg' x hx
  linarith

/-- A nonempty interior contains a point of the set together with a metric ball around it. -/
lemma exists_ball_subset_of_interior_nonempty {n : ℕ} {K : Set (Fin n → ℝ)}
    (hinter : (interior K).Nonempty) :
    ∃ z ε, 0 < ε ∧ z ∈ K ∧ Metric.ball z ε ⊆ K := by
  -- Choose an interior point and convert interior membership into a neighborhood ball.
  rcases hinter with ⟨z, hz⟩
  have hK_nhds : K ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
  rcases Metric.mem_nhds_iff.mp hK_nhds with ⟨ε, hεpos, hball⟩
  exact ⟨z, ε, hεpos, interior_subset hz, hball⟩

/-- The perturbation `ε / (2 * ‖y‖)` of a nonzero vector has positive scale and stays inside radius `ε`. -/
lemma small_smul_norm_lt_radius {n : ℕ} {y : Fin n → ℝ} {ε : ℝ}
    (hy : y ≠ 0) (hε : 0 < ε) :
    let t : ℝ := ε / (2 * ‖y‖)
    0 < t ∧ ‖t • y‖ < ε := by
  -- Positivity of the denominator comes from the nonzero vector norm.
  dsimp
  have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hdenom_pos : 0 < 2 * ‖y‖ := by positivity
  have hy_norm_ne : ‖y‖ ≠ 0 := ne_of_gt hy_norm_pos
  constructor
  · exact div_pos hε hdenom_pos
  · -- Compute the norm exactly and reduce the strict inequality to `ε / 2 < ε`.
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hε.le hdenom_pos.le)]
    have hcalc : (ε / (2 * ‖y‖)) * ‖y‖ = ε / 2 := by
      field_simp [hy_norm_ne]
    rw [hcalc]
    linarith

/-
Let K subseteq ℝ^n be a convex cone, and define its dual cone by K* = {y ∈ ℝ^n | xᵀ y > = 0 for all
x in K}. A cone C subseteq ℝ^n is pointed if whenever y in C and - y in C, then y = 0. Prove that if
K has nonempty interior, then K* is pointed.
-/
theorem dualCone_isPointed_of_interior_nonempty {n : ℕ} (K : Set (Fin n → ℝ))
    (hconv : Convex ℝ K)
    (hcone_add : ∀ ⦃x y : Fin n → ℝ⦄, x ∈ K → y ∈ K → x + y ∈ K)
    (hcone_smul : ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → a • x ∈ K)
    (hinter : (interior K).Nonempty) :
    IsPointed (dualCone K) := by
  rw [IsPointed]
  intro y hy hyneg
  -- Route correction: pointedness follows from an interior-ball perturbation, not from the cone axioms.
  have hzero_on_K : ∀ x, x ∈ K → dotProduct x y = 0 := by
    intro x hx
    exact dualCone_dotProduct_eq_zero_of_mem_and_neg_mem hy hyneg hx
  -- Extract an interior point together with a ball contained in `K`.
  rcases exists_ball_subset_of_interior_nonempty hinter with ⟨z, ε, hεpos, hzK, hball⟩
  have hz_zero : dotProduct z y = 0 := hzero_on_K z hzK
  -- If `y` were nonzero, a small move in the `y`-direction would stay inside `K`.
  by_contra hy_ne
  set t : ℝ := ε / (2 * ‖y‖) with ht
  have ht_data : 0 < t ∧ ‖t • y‖ < ε := by
    simpa [ht] using small_smul_norm_lt_radius (y := y) (ε := ε) hy_ne hεpos
  have ht_pos : 0 < t := ht_data.1
  have hty_norm_lt : ‖t • y‖ < ε := ht_data.2
  have hzty_ball : z + t • y ∈ Metric.ball z ε := by
    rwa [add_mem_ball_iff_norm]
  have hztyK : z + t • y ∈ K := hball hzty_ball
  have hzty_zero : dotProduct (z + t • y) y = 0 := hzero_on_K (z + t • y) hztyK
  -- Expanding the dot product isolates `t * (y ⬝ᵥ y)`.
  have hmul_zero : t * dotProduct y y = 0 := by
    calc
      t * dotProduct y y = dotProduct (z + t • y) y := by
        rw [add_dotProduct, smul_dotProduct]
        simp [hz_zero, smul_eq_mul]
      _ = 0 := hzty_zero
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hyy_zero : dotProduct y y = 0 := (mul_eq_zero.mp hmul_zero).resolve_left ht_ne
  exact hy_ne (dotProduct_self_eq_zero.mp hyy_zero)

end «problem-37»
