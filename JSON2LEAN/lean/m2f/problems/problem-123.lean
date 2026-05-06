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
  intro x
  -- Rewrite `g x` as the infimum over positive scalings so we can prove a lower-bound property.
  rw [hg x]
  -- `WithBot ℝ` is only conditionally complete here, so we prove the set is nonempty and then use `le_csInf`.
  refine le_csInf ?_ ?_
  · refine ⟨((f ((1 : ℝ) • x) / (1 : ℝ) : ℝ) : WithBot ℝ), ?_⟩
    refine ⟨(1 : ℝ), ?_, ?_⟩
    · positivity
    · rfl
  · intro r hr
    rcases hr with ⟨α, hα, rfl⟩
    -- Compare in `ℝ`: the underestimator bound at `α • x` and homogeneity give a scaled inequality.
    apply WithBot.coe_le_coe.2
    apply (le_div_iff₀ hα).2
    -- Rewrite the homogeneous value and then use the pointwise underestimate of `f`.
    calc
      h x * α = α * h x := by ring
      _ = h (α • x) := by rw [hhom x α hα]
      _ ≤ f (α • x) := hunder (α • x)
end «problem-123»
