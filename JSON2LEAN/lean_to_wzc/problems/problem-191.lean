import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-191»

/- [BLOCK Exercise 14.3-(a) | 18 | thm]
Let m,n ∈ ℕ. For i=1,ldots,m, let Kᵢ ∈ ℝ^{n×n} be given symmetric positive semidefinite matrices, Kᵢ
= K_iᵀ succeq 0, and define, for x=(x₁,ldots,xₘ) ∈ ℝ^m, K(x)=sum_{i=1}^m xᵢ Kᵢ. Let f ∈ ℝ^n be
fixed, and define E(x,f)=(1)/(2) fᵀ K(x)^{-1} f for all x ∈ ℝ^m such that K(x) succ 0. Show that
E(x,f) is a convex function of x on the set {x ∈ ℝ^m | K(x) succ 0}.
-/
open scoped BigOperators

theorem complianceEnergy_convexOn
    {m n : ℕ}
    (K : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hKsymm : ∀ i, (K i).IsSymm)
    (hKpsd : ∀ i, Matrix.PosSemidef (K i))
    (f : Fin n → ℝ) :
    ConvexOn ℝ
      {x : Fin m → ℝ | Matrix.PosDef (∑ i, x i • K i)}
      (fun x => (1 / 2 : ℝ) * dotProduct f (((∑ i, x i • K i)⁻¹).mulVec f)) := by
  sorry

end «problem-191»
