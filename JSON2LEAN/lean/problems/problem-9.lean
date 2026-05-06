import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-9»
/- [BLOCK Exercise 3.31 | 71 | defn]
Random variables ω_1,ldots,ω_N are independent if for every collection of measurable sets
A₁,ldots,A_N,
P(ω_1 ∈ A₁,ldots,ω_N ∈ A_N) = prod_{i=1}^N P(ω_i ∈ Aᵢ).
-/
def IndependentRandomVariables
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) {N : ℕ} {α : Type*}
    (ω : Fin N → Ω → α)
    [MeasurableSpace α] : Prop :=
  (∀ i, Measurable (ω i)) ∧
  ∀ s : Fin N → Set α,
    (∀ i, MeasurableSet (s i)) →
      P (⋂ i, ω i ⁻¹' s i) = ∏ i, P (ω i ⁻¹' s i)

/- [BLOCK Exercise 3.31 | 72 | defn]
Two random variables xi and eta have the same distribution if for every measurable set A,
P(xi ∈ A) = P(eta ∈ A).
-/
def SameDistribution
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    {α : Type*} [MeasurableSpace α] (ξ η : Ω → α) : Prop :=
  ∀ s : Set α, MeasurableSet s → P (ξ ⁻¹' s) = P (η ⁻¹' s)

/- [BLOCK Exercise 3.31 | 73 | thm]
Let (ω,F,P) be a probability space, and let f:ℝ^n × ω → ℝ satisfy that, for each ω ∈ ω, the function
x mapsto f(x,ω) is convex on ℝ^n. Assume that for every x ∈ ℝ^n, the expectation F(x)=E[f(x,ω)] is
well defined and finite, and let p^star=∈f_{x∈ℝ^n} F(x), where p^star is finite. Let N ∈ ℕ with N ≥
1, and let ω_1,ldots,ω_N be independent random samples with the same distribution as ω. Define hat
F(x)=(1)/(N)sum_{i=1}^N f(x,ω_i), x ∈ ℝ^n, and define hat p^star=∈f_{x∈ℝ^n}hat F(x). Show that E[hat
p^star] ≤ p^star.
-/
open scoped BigOperators

theorem expected_empirical_optimum_le_optimum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (n N : ℕ)
    (hN : 1 ≤ N)
    (f : (Fin n → ℝ) → Ω → ℝ)
    (F : (Fin n → ℝ) → ℝ)
    (ωSamples : Fin N → Ω → Ω)
    (pStar : ℝ)
    (pHatStar : Ω → ℝ)
    (hf_convex : ∀ ω0 : Ω, ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => f x ω0))
    (hf_measurable : ∀ x : Fin n → ℝ, Measurable (f x))
    (hf_integrable : ∀ x : Fin n → ℝ, MeasureTheory.Integrable (f x) P)
    (hF : ∀ x : Fin n → ℝ, F x = ∫ ω0, f x ω0 ∂P)
    (hω_indep : IndependentRandomVariables P ωSamples)
    (hω_same_dist : ∀ i : Fin N, SameDistribution P (ωSamples i) (fun ω0 : Ω => ω0))
    (hpStar : IsGLB (Set.range F) pStar)
    (hpHatStar_measurable : Measurable pHatStar)
    (hpHatStar_integrable : MeasureTheory.Integrable pHatStar P)
    (hpHatStar : ∀ ω0 : Ω,
      IsGLB
        (Set.range (fun x : Fin n → ℝ => (1 / (N : ℝ)) * ∑ i, f x (ωSamples i ω0)))
        (pHatStar ω0)) :
    ∫ ω0, pHatStar ω0 ∂P ≤ pStar := by
  sorry

end «problem-9»
