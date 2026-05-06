import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-149»
/-
Let the function f: ℝ^n → ℝ be defined by f(x) = ln(\sum_{k = 1}^n e^{xₖ}), x = (x₁, ..., xₙ)^→p ∈
ℝ^n. Compute the Hessian matrix abla^2 f(x) of f.
-/
open scoped BigOperators

theorem hessian_log_sum_exp
    (n : ℕ)
    (hn : 0 < n)
    (x : Fin n → ℝ) :
    ∀ i j : Fin n,
      (fderiv ℝ
        (fun y : Fin n → ℝ =>
          (fderiv ℝ
            (fun z : Fin n → ℝ => Real.log (∑ k : Fin n, Real.exp (z k))) y)
            (Pi.single j (1 : ℝ))) x)
        (Pi.single i (1 : ℝ))
      =
      (Real.exp (x i) / (∑ k : Fin n, Real.exp (x k))) *
        ((if i = j then (1 : ℝ) else 0) -
          Real.exp (x j) / (∑ k : Fin n, Real.exp (x k))) := by
  sorry

/-
Let the function f: ℝ^n → ℝ be defined by f(x) = ln(\sum_{k = 1}^n e^{xₖ}), x = (x₁, ..., xₙ)^→p ∈
ℝ^n. Prove that for any x∈ ℝ^n, the matrix abla^2 f(x) is positive semidefinite.
-/
theorem hessian_log_sum_exp_posSemidef
    (n : ℕ)
    (hn : 0 < n)
    (x v : Fin n → ℝ) :
    0 ≤
      ∑ i : Fin n, ∑ j : Fin n,
        v i *
          ((fderiv ℝ
            (fun y : Fin n → ℝ =>
              (fderiv ℝ
                (fun z : Fin n → ℝ => Real.log (∑ k : Fin n, Real.exp (z k))) y)
                (Pi.single j (1 : ℝ))) x)
            (Pi.single i (1 : ℝ))) * v j := by
  sorry

/-
Let the function f: ℝ^n → ℝ be defined by f(x) = ln(\sum_{k = 1}^n e^{xₖ}), x = (x₁, ..., xₙ)^→p ∈
ℝ^n. Deduce that f is convex on ℝ^n.
-/
theorem log_sum_exp_convex
    (n : ℕ)
    (hn : 0 < n) :
    ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => Real.log (∑ k : Fin n, Real.exp (x k))) := by
  sorry
end «problem-149»
