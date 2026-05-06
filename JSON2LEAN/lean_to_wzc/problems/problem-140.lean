import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-140»

-- Exercise_2_19

/- [BLOCK Exercise 2.19 | 12 | thm]
Let n be a natural number, and let λ_1, ..., λ_n be positive real numbers.
Define R_++^n = {x ∈ ℝ^n | xᵢ > 0 for all i = 1, ..., n}.
Define f : R_++^n → ℝ by
f(x) = product_{i=1}^n (1 - e^(-xᵢ))^(lambda_i), where x = (x₁, ..., xₙ).
Show that f is concave on
dom f = {x ∈ ℝ_++^n | sum_{i=1}^n lambda_i e^(-xᵢ) <= 1}.
-/
open scoped BigOperators

theorem concaveOn_prod_one_sub_exp_neg_rpow
    {n : ℕ} (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i) :
    ConcaveOn ℝ
      {x : Fin n → ℝ | (∀ i, 0 < x i) ∧ ∑ i, lam i * Real.exp (-x i) ≤ 1}
      (fun x => ∏ i, Real.rpow (1 - Real.exp (-x i)) (lam i)) := by
  sorry

end «problem-140»