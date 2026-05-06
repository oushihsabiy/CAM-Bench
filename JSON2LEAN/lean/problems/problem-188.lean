import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-188»

/- [BLOCK Exercise 14.17 | 21 | thm]
Let x^{min},x^{max} ∈ ℝ satisfy x^{min} ≤ 0 ≤ x^{max}, and let φ:[x^{min},x^{max}] → ℝ be
differentiable. Assume φ(x) ≥ 0 quad for all x ∈ [0,x^{max}], φ(x) ≤ 0 quad for all x ∈ [x^{min},0].
Define E:[x^{min},x^{max}] → ℝ, E(x)=∈t₀^x φ(t)dt. Show that E is quasiconvex on [x^{min},x^{max}].
-/
theorem integral_sign_split_quasiconvex
    {xMin xMax : ℝ}
    (hord : xMin ≤ 0 ∧ 0 ≤ xMax)
    {φ : ℝ → ℝ}
    (hφ_diff : DifferentiableOn ℝ φ (Set.Icc xMin xMax))
    (hφ_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) xMax, 0 ≤ φ x)
    (hφ_nonpos : ∀ x ∈ Set.Icc xMin (0 : ℝ), φ x ≤ 0) :
    QuasiconvexOn ℝ (Set.Icc xMin xMax) (fun x => ∫ t in 0..x, φ t) := by
  sorry

/- [BLOCK Exercise 14.17 | 22 | thm]
Let x^{min},x^{max} ∈ ℝ satisfy x^{min} ≤ 0 ≤ x^{max}, and let φ:[x^{min},x^{max}] → ℝ be
differentiable. Assume φ(x) ≥ 0 quad for all x ∈ [0,x^{max}], φ(x) ≤ 0 quad for all x ∈ [x^{min},0].
Define E:[x^{min},x^{max}] → ℝ, E(x)=∈t₀^x φ(t)dt. A spring is called monotonic if φ is
nondecreasing on [x^{min},x^{max}], meaning that for all x₁,x₂ ∈ [x^{min},x^{max}], x₁ ≤ x₂ implies
φ(x₁) ≤ φ(x₂). Show that E is convex on [x^{min},x^{max}] if and only if the spring is monotonic.
-/
theorem integral_energy_convex_iff_monotone
    {xMin xMax : ℝ}
    (hord : xMin ≤ 0 ∧ 0 ≤ xMax)
    {φ : ℝ → ℝ}
    (hφ_diff : DifferentiableOn ℝ φ (Set.Icc xMin xMax))
    (hφ_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) xMax, 0 ≤ φ x)
    (hφ_nonpos : ∀ x ∈ Set.Icc xMin (0 : ℝ), φ x ≤ 0) :
    ConvexOn ℝ (Set.Icc xMin xMax) (fun x => ∫ t in 0..x, φ t) ↔
      MonotoneOn φ (Set.Icc xMin xMax) := by
  sorry

end «problem-188»
