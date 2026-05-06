import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-135»
/-
Let x ∈ ℝ^k be a random vector taking values in the finite set {α_1, ..., α_n} ⊂ ℝ^k with
probabilities pᵢ = prob(x = α_i), where pᵢ ≥ 0 for i = 1, ..., n and \sum_{i = 1}^n pᵢ = 1. Its
expectation is Ex = \sum_{i = 1}^n pᵢ α_i, and its covariance matrix is Eigl((x - Ex)(x -
Ex)ᵀigr). Let
S ∈ ℝ^{k \times k} be a given symmetric matrix, and let A preceq B mean that B - A is positive
semidefinite. Show that the constraint S preceq Eigl((x - Ex)(x - Ex)ᵀigr) on the covariance
matrix of
x is a convex constraint in p = (p₁, ..., pₙ).
-/
open scoped BigOperators

theorem covariance_lower_bound_constraint_is_convex
    {n k : ℕ} (α : Fin n → Fin k → ℝ) (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.IsSymm) :
    Convex ℝ
      {p : Fin n → ℝ |
        (∀ i, 0 ≤ p i) ∧
        (∑ i, p i = 1) ∧
        Matrix.PosSemidef
          ((∑ i, p i •
              Matrix.vecMulVec
                (fun a => α i a - ∑ l, p l * α l a)
                (fun b => α i b - ∑ l, p l * α l b)) - S)} := by
  sorry

end «problem-135»