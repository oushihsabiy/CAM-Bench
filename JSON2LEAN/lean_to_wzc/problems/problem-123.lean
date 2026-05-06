import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-123»
/-
With g(x) = \inf_{α > 0} f(αx)/α, prove that g is the largest homogeneous underestimator of f: if h
is homogeneous and h ≤ f, then h ≤ g.
-/
theorem homogeneous_underestimator_le_infScaled
    {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → WithBot ℝ)
    (h : (Fin n → ℝ) → ℝ)
    (hg : ∀ x, g x = sInf {r : WithBot ℝ | ∃ α : ℝ, α > 0 ∧ r = ((f (α • x) / α : ℝ) : WithBot ℝ)})
    (hhom : ∀ (x : Fin n → ℝ) (α : ℝ), α > 0 → h (α • x) = α * h x)
    (hunder : ∀ x, h x ≤ f x) :
    ∀ x, ((h x : ℝ) : WithBot ℝ) ≤ g x := by
  sorry
end «problem-123»