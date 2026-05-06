import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-145»

def l2Norm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-
Let A ∈ ℝ^{m \times n} and b ∈ ℝ^m be fixed. Define D = {x ∈ ℝ^n | ‖x‖_2 < 1} and, for x ∈ D, f(x) =
\frac{‖Ax - b‖_2^2}{1 - xᵀ x}. Show that the function f: D o ℝ is convex on D.
-/
theorem ratio_squared_norm_affine_over_one_sub_normSq_convexOn
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (b : m → ℝ) :
    ConvexOn ℝ {x : n → ℝ | l2Norm x < 1}
      (fun x : n → ℝ => l2Norm (A.mulVec x - b) ^ 2 / (1 - l2Norm x ^ 2)) := by
  sorry

end «problem-145»
