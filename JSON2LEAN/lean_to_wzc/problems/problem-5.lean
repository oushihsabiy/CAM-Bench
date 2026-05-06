import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-5»

/- [BLOCK Exercise 6.3-(a) | 14 | thm]
Let n ∈ ℕ. For θ ∈ ℝ^n, define p_{θ}(x)=a(θ)exp(θ^{T}x), x ∈ ℝ_{+}^{n}, where
a(θ)=≤ft(∈t_{ℝ_{+}^{n}} exp(θ^{T}x)dx)^{-1} whenever the integral is finite. Here dx is Lebesgue
measure, θ^{T}x=sum_{i=1}^{n}θ_i xᵢ, and ℝ_{+}^{n}={x=(x₁,dots,xₙ)∈ ℝ^{n}: xᵢ ≥ 0 for i=1,dots,n}.
Prove that ∈t_{ℝ_{+}^{n}} exp(θ^{T}x)dx < ∞ quad if and only if quad θ_i < 0 for all i=1,dots,n,
and, in this case, a(θ)=prod_{i=1}^{n}(-θ_i), p_{θ}(x)=≤ft(prod_{i=1}^{n}(-θ_i))exp(θ^{T}x) quad for
all x∈ ℝ_{+}^{n}.
-/
theorem exp_integral_on_nonnegative_orthant_finite_iff
    (n : ℕ) (θ : Fin n → ℝ) :
    let orthant : Set (Fin n → ℝ) := {x | ∀ i, 0 ≤ x i}
    let kernel : (Fin n → ℝ) → ℝ :=
      fun x => Real.exp (∑ i, θ i * x i)
    let integral : ℝ := ∫ x : Fin n → ℝ in orthant, kernel x
    let normalizer : ℝ := integral⁻¹
    -- Finiteness iff all components are negative
    -- `IntegrableOn` uses the norm, but `kernel x = exp _` is positive, so
    -- this is the right formal version of finiteness of the nonnegative integral.
    ((MeasureTheory.IntegrableOn kernel orthant) ↔ (∀ i, θ i < 0)) ∧
    -- When all negative, the integral, normalizer a(θ), and density p_θ
    -- have the expected product forms. Empty products cover the n = 0 case.
    ((∀ i, θ i < 0) →
      integral = ∏ i : Fin n, (-θ i)⁻¹ ∧
      normalizer = ∏ i : Fin n, (-θ i) ∧
      ∀ x ∈ orthant,
        normalizer * kernel x = (∏ i : Fin n, (-θ i)) * kernel x) := by
  sorry

end «problem-5»
