import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-50»
/- [BLOCK Exercise 2.26-(a) | 30 | thm]
Let Y and Z be real symmetric matrices of the same size. For symmetric matrices A and B, A preceq B
means that B-A is positive semidefinite, and A prec B means that B-A is positive definite. Prove the
following auxiliary claim: if 0 prec Y preceq Z, then det Y ≤ det Z.
-/
open Matrix

theorem det_le_of_posDef_and_loewner
    {n : Type*} [Fintype n] [DecidableEq n]
    (Y Z : Matrix n n ℝ)
    (hYsymm : Y.IsSymm)
    (hZsymm : Z.IsSymm)
    (hpos : Y.PosDef)
    (hYZ : (Z - Y).PosSemidef) :
    Y.det ≤ Z.det := by
  sorry

end «problem-50»
