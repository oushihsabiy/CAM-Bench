import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-104»

/- [BLOCK Exercise 8.7 | 6 | thm]
Let n ∈ ℕ, let x₁,x₂ ∈ ℝ^n, and let P₁,P₂ ∈ S_{++}^n, where S_{++}^n is the set of real symmetric
positive definite n × n matrices. For i=1,2, let Pᵢ^{1/2} denote the unique symmetric positive
definite square root of Pᵢ, and define
E₁={x∈ ℝ^n | (x-x₁)ᵀ P₁^{-1}(x-x₁)≤ 1},
E₂={x∈ ℝ^n | (x-x₂)ᵀ P₂^{-1}(x-x₂)≤ 1}.
Let ‖·‖_2 be the Euclidean norm on ℝ^n. Show that E_1cap E₂=emptyset if and only if there exists a∈
ℝ^n such that ‖P₂^{1/2}a‖_2+‖P₁^{1/2}a‖_2< aᵀ(x₁-x₂).
-/
open scoped Matrix

theorem ellipsoids_disjoint_iff_exists_separating_vector
    (n : ℕ) (x₁ x₂ : Fin n → ℝ) (P₁ P₂ : Matrix (Fin n) (Fin n) ℝ)
    (hP₁_symm : P₁.IsSymm) (hP₂_symm : P₂.IsSymm)
    (hP₁_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₁.mulVec v))
    (hP₂_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₂.mulVec v))
    (hP₁_inv : Nonempty (Invertible P₁)) (hP₂_inv : Nonempty (Invertible P₂))
    (P₁sqrt P₂sqrt : Matrix (Fin n) (Fin n) ℝ)
    (hP₁sqrt_sq : P₁sqrt * P₁sqrt = P₁) (hP₂sqrt_sq : P₂sqrt * P₂sqrt = P₂)
    (hP₁sqrt_symm : P₁sqrt.IsSymm) (hP₂sqrt_symm : P₂sqrt.IsSymm)
    (hP₁sqrt_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₁sqrt.mulVec v))
    (hP₂sqrt_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₂sqrt.mulVec v)) :
    ({x : Fin n → ℝ |
        dotProduct (x - x₁) (P₁⁻¹.mulVec (x - x₁)) ≤ 1} ∩
      {x : Fin n → ℝ |
        dotProduct (x - x₂) (P₂⁻¹.mulVec (x - x₂)) ≤ 1} = (∅ : Set (Fin n → ℝ))) ↔
      ∃ a : Fin n → ℝ,
        Real.sqrt (dotProduct (P₂sqrt.mulVec a) (P₂sqrt.mulVec a)) +
            Real.sqrt (dotProduct (P₁sqrt.mulVec a) (P₁sqrt.mulVec a)) <
          dotProduct a (x₁ - x₂) := by
  sorry

end «problem-104»
