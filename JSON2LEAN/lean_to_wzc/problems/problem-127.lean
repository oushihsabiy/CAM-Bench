import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-127»
/-
For a cone K ⊆ ℝ^n, its dual cone is K* = {y ∈ ℝ^n | yᵀ x ≥ 0 for all x ∈ K}.
-/
open scoped RealInnerProductSpace

def dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ K, 0 ≤ ⟪y, x⟫}

/-
Let A ∈ ℝ^{m \times n}, and let V = {x ∈ ℝ^n | Ax succeq 0}, where Ax succeq 0 means that every
component of Ax ∈ ℝ^m is nonnegative. For a cone K ⊆ ℝ^n, define its dual cone by K* = {y ∈ ℝ^n | yᵀ
x ≥ 0 ext{for all} x ∈ K}. Show that V* = {Aᵀ v | v succeq 0}, where v succeq 0 means that every
component of v ∈ ℝ^m is nonnegative.
-/
theorem dualCone_of_nonnegative_preimage_eq_range_transpose_nonnegative
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    dualCone {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, 0 ≤ (A.mulVec x) i} =
      {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  sorry
end «problem-127»