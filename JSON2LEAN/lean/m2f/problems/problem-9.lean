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
  have hN_pos : 0 < N := lt_of_lt_of_le (by decide : 0 < 1) hN
  have hN_real_ne_zero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN_pos)
  -- Each sample map preserves the base measure because it has the same distribution as the identity.
  have h_sample_map : ∀ i : Fin N, MeasureTheory.Measure.map (ωSamples i) P = P := by
    intro i
    ext s hs
    rw [MeasureTheory.Measure.map_apply (hω_indep.1 i) hs]
    simpa using hω_same_dist i s hs
  -- Composing an integrable loss with a sample map preserves integrability.
  have h_sampled_integrable :
      ∀ x : Fin n → ℝ, ∀ i : Fin N, MeasureTheory.Integrable (fun ω0 => f x (ωSamples i ω0)) P := by
    intro x i
    have h_integrable_map : MeasureTheory.Integrable (f x) (MeasureTheory.Measure.map (ωSamples i) P) := by
      simpa [h_sample_map i] using hf_integrable x
    simpa using h_integrable_map.comp_measurable (hω_indep.1 i)
  -- Each sampled loss has the same expectation as the original loss at the same decision vector.
  have h_sampled_integral_eq_F :
      ∀ x : Fin n → ℝ, ∀ i : Fin N, ∫ ω0, f x (ωSamples i ω0) ∂P = F x := by
    intro x i
    have h_integrable_map : MeasureTheory.Integrable (f x) (MeasureTheory.Measure.map (ωSamples i) P) := by
      simpa [h_sample_map i] using hf_integrable x
    calc
      ∫ ω0, f x (ωSamples i ω0) ∂P
          = ∫ y, f x y ∂MeasureTheory.Measure.map (ωSamples i) P := by
              symm
              exact MeasureTheory.integral_map (hω_indep.1 i).aemeasurable
                h_integrable_map.aestronglyMeasurable
      _ = ∫ y, f x y ∂P := by simp [h_sample_map i]
      _ = F x := by rw [hF x]
  -- Averaging the sampled expectations recovers the same objective value `F x`.
  have h_empirical_integral_eq_F :
      ∀ x : Fin n → ℝ,
        ∫ ω0, (1 / (N : ℝ)) * ∑ i, f x (ωSamples i ω0) ∂P = F x := by
    intro x
    calc
      ∫ ω0, (1 / (N : ℝ)) * ∑ i, f x (ωSamples i ω0) ∂P
          = (1 / (N : ℝ)) * ∫ ω0, ∑ i, f x (ωSamples i ω0) ∂P := by
              rw [MeasureTheory.integral_const_mul]
      _ = (1 / (N : ℝ)) * ∑ i, ∫ ω0, f x (ωSamples i ω0) ∂P := by
            congr 1
            simpa using
              (MeasureTheory.integral_finset_sum Finset.univ
                (fun i _ => h_sampled_integrable x i))
      _ = (1 / (N : ℝ)) * ∑ i : Fin N, F x := by
            simp [h_sampled_integral_eq_F x]
      _ = F x := by
            simp [Finset.sum_const, nsmul_eq_mul, hN_real_ne_zero]
  -- The pointwise GLB property makes `pHatStar` a lower bound of every empirical objective value.
  have h_expected_lower_bound : (∫ ω0, pHatStar ω0 ∂P) ∈ lowerBounds (Set.range F) := by
    rw [mem_lowerBounds]
    intro y hy
    rcases hy with ⟨x, rfl⟩
    have h_empirical_integrable :
        MeasureTheory.Integrable (fun ω0 => (1 / (N : ℝ)) * ∑ i, f x (ωSamples i ω0)) P := by
      apply MeasureTheory.Integrable.const_mul
      simpa using
        (MeasureTheory.integrable_finset_sum Finset.univ
          (fun i _ => h_sampled_integrable x i))
    -- Integrating the pointwise lower bound yields an expectation bound for each fixed decision vector.
    have h_integral_le :
        ∫ ω0, pHatStar ω0 ∂P ≤
          ∫ ω0, (1 / (N : ℝ)) * ∑ i, f x (ωSamples i ω0) ∂P := by
      refine MeasureTheory.integral_mono_ae hpHatStar_integrable h_empirical_integrable ?_
      exact Filter.Eventually.of_forall fun ω0 => (hpHatStar ω0).1 ⟨x, rfl⟩
    exact h_integral_le.trans_eq (h_empirical_integral_eq_F x)
  -- The expected empirical optimum is therefore below the GLB of the range of `F`.
  exact (le_isGLB_iff hpStar).2 h_expected_lower_bound

end «problem-9»
