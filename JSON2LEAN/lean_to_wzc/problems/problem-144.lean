import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-144»
/-
Let f: ℝ^n → ℝ be convex and g: ℝ^n → ℝ be concave, with g(x) ≤ f(x) for all x ∈ ℝ^n. Prove that
there exists an affine function h(x) = aᵀx + b such that g(x) ≤ h(x) ≤ f(x) for all x ∈ ℝ^n.
-/
theorem exists_affine_between_convex_and_concave
    {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hg : ConcaveOn ℝ Set.univ g)
    (hgf : ∀ x : Fin n → ℝ, g x ≤ f x) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ, ∀ x : Fin n → ℝ, g x ≤ ∑ i, a i * x i + b ∧ ∑ i, a i * x i + b ≤ f x := by
  sorry
end «problem-144»