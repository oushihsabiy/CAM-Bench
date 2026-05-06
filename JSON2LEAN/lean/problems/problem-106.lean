import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-106»
/-
Let S_{+ +}^n be the set of real symmetric positive - definite n×n matrices. Define f(X) = tr(X^{-
1}).
Prove that f is convex on S_{+ +}^n.
-/
theorem trace_inv_convexOn_posDef
    (n : Type) [Fintype n] [DecidableEq n] :
    ConvexOn ℝ
      {X : Matrix n n ℝ | X.IsSymm ∧ X.PosDef}
      (fun X => Matrix.trace X⁻¹) := by
  sorry

end «problem-106»