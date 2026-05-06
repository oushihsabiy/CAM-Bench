import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-64»
/-
For a set E subseteq ℝ^n, its support function is the map S_E: ℝ^n → ℝ - bar defined by S_E(y) = sup
{yᵀ x | x in E} for all y ∈ ℝ^n.
-/
open scoped RealInnerProductSpace

def supportFunction {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EReal :=
  fun y => sSup (((fun x : EuclideanSpace ℝ (Fin n) => ((⟪y, x⟫ : ℝ) : EReal)) '' E))

/-
Let C and D be closed convex subsets of ℝ^n. For each E subseteq ℝ^n, define the support function
S_E: ℝ^n → ℝ - bar by S_E(y) = sup {yᵀ x | x in E}, for y ∈ ℝ^n. The supremum is in the extended -
real
sense, and the supremum of the empty set is - infinity. Show that C = D if and only if S_C = S_D,
meaning S_C(y) = S_D(y) for every y ∈ ℝ^n.
-/
theorem closed_convex_eq_iff_supportFunction_eq
    {n : ℕ} {C D : Set (EuclideanSpace ℝ (Fin n))}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    C = D ↔ supportFunction C = supportFunction D := by
  sorry
end «problem-64»