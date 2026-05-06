import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-120»
/-
Let f: ℝ^n → ℝ be convex and piecewise linear. Suppose regions X₁, …, X_L cover ℝ^n, their interiors
are pairwise disjoint, and on each Xᵢ one has f(x) = a_iᵀx + bᵢ. Prove that f(x) = max{a₁ᵀx + b₁, …,
a_Lᵀx + b_L} for all x∈ℝ^n.
-/
theorem convex_piecewiseLinear_eq_iSup_affine
    {n L : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (X : Fin L → Set (Fin n → ℝ))
    (a : Fin L → (Fin n → ℝ))
    (b : Fin L → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hcover : Set.univ = ⋃ i, X i)
    (hinterior_disjoint :
      ∀ i j : Fin L, i ≠ j → Disjoint (interior (X i)) (interior (X j)))
    (hlinear : ∀ i : Fin L, ∀ x ∈ X i, f x = dotProduct (a i) x + b i)
    (haffine_le : ∀ i : Fin L, ∀ x : Fin n → ℝ, dotProduct (a i) x + b i ≤ f x) :
    ∀ x : Fin n → ℝ, f x = ⨆ i : Fin L, (dotProduct (a i) x + b i) := by
  sorry

end «problem-120»
