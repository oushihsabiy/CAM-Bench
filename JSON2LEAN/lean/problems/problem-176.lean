import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-176»
/-
Let m and n be natural numbers with n > = 1. Let A ∈ ℝ^(m x n) and b ∈ ℝ^m. For x ∈ ℝ^n, write x > 0
if every component of x is strictly positive. For y ∈ ℝ^n, write y > = 0 if every component of y is
nonnegative. Show that there exists x ∈ ℝ^n such that x > 0 and Ax = b if and only if there does not
exist λ ∈ ℝ^m such that Aᵀ λ > = 0, Aᵀ λ ! = 0, and bᵀ λ < = 0.
-/
theorem exists_strictly_positive_solution_iff_no_dual_certificate
    {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ A.mulVec x = b) ↔
      ¬ ∃ lam : Fin m → ℝ,
        (∀ i, 0 ≤ (A.transpose.mulVec lam) i) ∧
        A.transpose.mulVec lam ≠ 0 ∧
        dotProduct b lam ≤ 0 := by
  sorry

end «problem-176»