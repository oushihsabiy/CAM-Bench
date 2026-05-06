import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-146»

def l2Norm {m : ℕ} (y : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, (y i) ^ 2)

/-
Let A ∈ ℝ^{m × n}, b ∈ ℝ^m, c ∈ ℝ^n, and d ∈ ℝ. Define f: {x ∈ ℝ^n | cᵀ x + d > 0} → ℝ, f(x) =
(‖Ax + b‖_2^2)/(cᵀ x + d), where ‖y‖_2 = (\sum_{i = 1}^m yᵢ^2)^{1/2} is the Euclidean norm on ℝ^m.
Show
that f is convex on {x ∈ ℝ^n | cᵀ x + d > 0}.
-/
theorem quadratic_over_affine_isConvexOn
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ) :
    ConvexOn ℝ
      {x : Fin n → ℝ | dotProduct c x + d > 0}
      (fun x => l2Norm (A.mulVec x + b) ^ 2 / (dotProduct c x + d)) := by
  sorry
end «problem-146»
