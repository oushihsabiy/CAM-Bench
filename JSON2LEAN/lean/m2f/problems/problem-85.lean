import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-85»
/-
The second - order cone in ℝ^(n + 1) is the set K: = {(x, t) ∈ ℝ^(n + 1) | t ≥ ‖x‖_2}.
-/
def secondOrderCone (n : ℕ) : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  {p | ‖p.1‖ ≤ p.2}


/-
Let the second - order cone be K: = {(x, t)∈ ℝ^(n + 1) | t ≥ ‖x‖_2}, where x∈ ℝ^n, t∈ ℝ, and ‖x‖_2
is
the Euclidean norm. Its dual cone is defined by K^*: = {(y, s)∈ ℝ^(n + 1) | ⟨ x, y⟩ + ts ≥ 0, ∀ (x,
t)∈ K}, where ⟨ x, y⟩ is the standard inner product in ℝ^n. Prove that the second - order cone K is
self - dual.
-/
open scoped RealInnerProductSpace

theorem secondOrderCone_isSelfDual (n : ℕ) :
    {q : EuclideanSpace ℝ (Fin n) × ℝ |
      ∀ p ∈ secondOrderCone n, 0 ≤ ⟪p.1, q.1⟫ + p.2 * q.2} = secondOrderCone n := by
  ext q
  constructor
  · intro hq
    -- Unpack the dual-cone condition and prove the norm bound by contradiction.
    change (∀ p, p ∈ secondOrderCone n → 0 ≤ ⟪p.1, q.1⟫ + p.2 * q.2) at hq
    change ‖q.1‖ ≤ q.2
    by_contra hq_not
    have hq_lt : q.2 < ‖q.1‖ := lt_of_not_ge hq_not
    by_cases hq_zero : q.1 = 0
    · -- In the zero case, testing against `(0, 1)` forces `q.2 ≥ 0`, contradicting `q.2 < 0`.
      have hp_mem : ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) ∈ secondOrderCone n := by
        simp [secondOrderCone]
      have htest :
          0 ≤
            ⟪(0 : EuclideanSpace ℝ (Fin n)), q.1⟫ + (1 : ℝ) * q.2 :=
        hq ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) hp_mem
      have hq_nonneg : 0 ≤ q.2 := by
        simpa [hq_zero] using htest
      have hq_neg : q.2 < 0 := by
        simpa [hq_zero] using hq_lt
      linarith
    · -- Route correction: the separating witness must depend on `q.1`; use `(-q.1, ‖q.1‖)`.
      have hp_mem : (-q.1, ‖q.1‖) ∈ secondOrderCone n := by
        simp [secondOrderCone]
      have htest : 0 ≤ ⟪-q.1, q.1⟫ + ‖q.1‖ * q.2 := hq (-q.1, ‖q.1‖) hp_mem
      have hpair : 0 ≤ ‖q.1‖ * q.2 - ‖q.1‖ ^ 2 := by
        simpa [sub_eq_add_neg, real_inner_self_eq_norm_sq] using htest
      have hnorm_pos : 0 < ‖q.1‖ := norm_pos_iff.mpr hq_zero
      nlinarith
  · intro hq
    -- Unpack cone membership and prove every cone element pairs nonnegatively with `q`.
    change ‖q.1‖ ≤ q.2 at hq
    change ∀ p, p ∈ secondOrderCone n → 0 ≤ ⟪p.1, q.1⟫ + p.2 * q.2
    intro p hp
    simp [secondOrderCone] at hp
    have hp_nonneg : 0 ≤ p.2 := le_trans (norm_nonneg p.1) hp
    have hq_nonneg : 0 ≤ q.2 := le_trans (norm_nonneg q.1) hq
    -- Cauchy-Schwarz on `(-p.1, q.1)` gives the lower bound on the inner product.
    have hinner_aux : -⟪p.1, q.1⟫ ≤ ‖p.1‖ * ‖q.1‖ := by
      simpa [norm_neg] using (real_inner_le_norm (-p.1) q.1)
    have hinner : -(‖p.1‖ * ‖q.1‖) ≤ ⟪p.1, q.1⟫ := by
      nlinarith
    -- The cone inequalities control the product of the scalar components.
    have hmul : ‖p.1‖ * ‖q.1‖ ≤ p.2 * q.2 := by
      exact mul_le_mul_of_nonneg hp hq (norm_nonneg _) hq_nonneg
    nlinarith


end «problem-85»
