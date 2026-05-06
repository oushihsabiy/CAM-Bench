import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-40»
/-
Let n ∈ ℕ, and define ℝ_{+ +}^n = {x = (x₁, ..., xₙ)∈ ℝ^n: xₖ > 0, k = 1, ..., n}. Given the
function
f: ℝ_{+ +}^n o ℝ, f(x) = (prod_{k = 1}^n xₖ ight)^{1/n}. Prove that f is twice differentiable on
ℝ_{+ +}^n.
-/
theorem geometricMean_twiceDifferentiableOn_positiveOrthant (n : ℕ) (hn : 0 < n) :
    ContDiffOn ℝ 2
      (fun x : Fin n → ℝ => Real.rpow (∏ k, x k) (1 / (n : ℝ)))
      {x : Fin n → ℝ | ∀ k, 0 < x k} := by
  sorry

/-
Let n ∈ ℕ, and define ℝ_{+ +}^n = {x = (x₁, ..., xₙ)∈ ℝ^n: xₖ > 0, k = 1, ..., n}. Given the
function
f: ℝ_{+ +}^n o ℝ, f(x) = (prod_{k = 1}^n xₖ ight)^{1/n}. Prove that for any x ∈ ℝ_{+ +}^n, the
Hessian
matrix abla^2 f(x) is negative semidefinite.
-/
theorem geometricMean_hessian_nonpos (n : ℕ) (hn : 0 < n) :
    ∀ x : Fin n → ℝ,
      (∀ k, 0 < x k) →
      Matrix.PosSemidef
        (-fun i j =>
          (fderiv ℝ
            (fun y : Fin n → ℝ =>
              (fderiv ℝ
                (fun z : Fin n → ℝ => Real.rpow (∏ k, z k) (1 / (n : ℝ))) y)
                (Pi.single j (1 : ℝ))) x)
            (Pi.single i (1 : ℝ))) := by
  sorry

/-
Let n ∈ ℕ, and define ℝ_{+ +}^n = {x = (x₁, ..., xₙ)∈ ℝ^n: xₖ > 0, k = 1, ..., n}. Given the
function
f: ℝ_{+ +}^n o ℝ, f(x) = (prod_{k = 1}^n xₖ ight)^{1/n}. Prove that f is a concave function on
ℝ_{+ +}^n.
-/
theorem geometricMean_concaveOn_positiveOrthant (n : ℕ) (hn : 0 < n) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ k, 0 < x k}
      (fun x : Fin n → ℝ => Real.rpow (∏ k, x k) (1 / (n : ℝ))) := by
  sorry

end «problem-40»