import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-153»

def conicHull {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℝ)) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | ∀ C : Set (Matrix (Fin n) (Fin n) ℝ),
    S ⊆ C →
    (0 : Matrix (Fin n) (Fin n) ℝ) ∈ C →
    (∀ X Y : Matrix (Fin n) (Fin n) ℝ, X ∈ C → Y ∈ C → X + Y ∈ C) →
    (∀ X : Matrix (Fin n) (Fin n) ℝ, ∀ t : ℝ, 0 ≤ t → X ∈ C → t • X ∈ C) →
    A ∈ C}

/-
Let 1 ≤ k ≤ n, and let S be the set of matrices X Xᵀ where X ∈ ℝ^{n × k} has rank k. Prove that the
conic hull of S is the union of {0} with the set of positive semidefinite n × n matrices of rank at
least k.
-/
theorem cone_eq_posSemidef_rank_ge_k_union_zero
    (n k : ℕ) (hk₁ : 1 ≤ k) (hk₂ : k ≤ n) :
    conicHull
      {A : Matrix (Fin n) (Fin n) ℝ |
        ∃ X : Matrix (Fin n) (Fin k) ℝ, Matrix.rank X = k ∧ A = X * X.transpose} =
      ({A : Matrix (Fin n) (Fin n) ℝ |
          A.PosSemidef ∧ k ≤ Matrix.rank A} ∪ {0}) := by
  sorry

end «problem-153»
