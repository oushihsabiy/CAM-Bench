import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-192»

/- [BLOCK Exercise 1.6-(c) | 7 | defn]
For a set C ⊆ ℝ^n, its polar is
C^{circ} = {y ∈ ℝ^n | yᵀ x ≤ 1 for all x ∈ C}.
-/
def polar (C : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ C, dotProduct y x ≤ 1}

/- [BLOCK Exercise 1.6-(c) | 8 | defn]
Given a norm ‖·‖ on ℝ^n, its dual norm is defined by
‖y‖_* = yᵀ x | ‖x‖ ≤ 1, y ∈ ℝ^n.
-/
def dualNorm (norm : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : Fin n → ℝ, norm x ≤ 1 ∧ r = dotProduct y x}

/- [BLOCK Exercise 1.6-(c) | 9 | thm]
Let ‖·‖ be a norm on ℝ^n, and let its unit ball be B = {x ∈ ℝ^n | ‖x‖ ≤ 1}. For any set C ⊆ ℝ^n,
define its polar by C^{circ} = {y ∈ ℝ^n | yᵀ x ≤ 1 for all x ∈ C}, where yᵀ x is the standard
Euclidean inner product on ℝ^n. Define the dual norm ‖·‖_* by ‖y‖_* = yᵀ x | ‖x‖ ≤ 1. Prove that
B^{circ} = {y ∈ ℝ^n | ‖y‖_* ≤ 1}.
-/
theorem polar_unitBall_eq_dualNorm_le_one
    (norm : (Fin n → ℝ) → ℝ)
    (hnorm_nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm x)
    (hnorm_zero : norm 0 = 0)
    (hnorm_smul : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x)
    (hnorm_add : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y)
    (hnorm_pos : ∀ x : Fin n → ℝ, norm x = 0 → x = 0) :
    polar {x : Fin n → ℝ | norm x ≤ 1} = {y : Fin n → ℝ | dualNorm norm y ≤ 1} := by
  sorry

end «problem-192»
