import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-105»
/-
Let p < 1 with p ≠ 0, and define f(x) = (∑_{i = 1}^n xᵢ^p)^(1/p) on ℝ_{+ +}^n. Prove that f is
concave on ℝ_{+ +}^n.
-/
theorem power_sum_root_concave_on_positive_orthant
    {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp_ne : p ≠ 0) (hp_lt : p < 1) :
    ConcaveOn ℝ
      {x : Fin n → ℝ | ∀ i, 0 < x i}
      (fun x => Real.rpow (∑ i : Fin n, Real.rpow (x i) p) (1 / p)) := by
  sorry

end «problem-105»