import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators


namespace «problem-197»
/- [BLOCK Exercise 3.53 | 42 | defn]
A function f : ℝ^n → [0,∞) is log-concave if, for all u,v ∈ ℝ^n and all θ ∈ [0,1],
f(θ u+(1-θ)v) ≥ f(u)^θ f(v)^{1-θ}.
-/
def LogConcave {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ) : Prop :=
  (∀ x : E, 0 ≤ f x) ∧
  ∀ ⦃u v : E⦄ ⦃θ : ℝ⦄,
    0 ≤ θ →
    θ ≤ 1 →
    f (θ • u + (1 - θ) • v) ≥
      Real.rpow (f u) θ * Real.rpow (f v) (1 - θ)

def ProbabilityDensity
    {E : Type*} [MeasurableSpace E]
    (μ : MeasureTheory.Measure E)
    (f : E → ℝ) : Prop :=
  Measurable f ∧
  (∀ x : E, 0 ≤ f x) ∧
  MeasureTheory.Integrable f μ ∧
  ∫ x, f x ∂μ = 1

/- [BLOCK Exercise 3.53 | 43 | defn]
Random vectors X and Y are independent if, for all measurable sets A,B ⊆ ℝ^n,
P(X ∈ A, Y ∈ B)=P(X ∈ A)P(Y ∈ B).
-/
def IndependentRandomVectors {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    (P : MeasureTheory.Measure Ω) (X : Ω → E) (Y : Ω → F) : Prop :=
  ∀ ⦃A : Set E⦄ ⦃B : Set F⦄,
    MeasurableSet A →
    MeasurableSet B →
    P {ω | X ω ∈ A ∧ Y ω ∈ B} =
      P {ω | X ω ∈ A} * P {ω | Y ω ∈ B}

/- [BLOCK Exercise 3.53 | 44 | thm]
Let f and g be log-concave probability densities on ℝ^n. Define their convolution
h(z)=∫_{ℝ^n} f(z-t)g(t)dt, and assume each convolution integrand is integrable. Prove that h is a
probability density and is log-concave on ℝ^n.
-/
theorem convolution_logConcave
    {n : ℕ}
    (f g h : (Fin n → ℝ) → ℝ)
    (hf_density : ProbabilityDensity MeasureTheory.volume f)
    (hg_density : ProbabilityDensity MeasureTheory.volume g)
    (hf_logConcave : LogConcave f)
    (hg_logConcave : LogConcave g)
    (h_integrable :
      ∀ z : Fin n → ℝ,
        MeasureTheory.Integrable
          (fun t : Fin n → ℝ => f (z - t) * g t)
          MeasureTheory.volume)
    (hh_conv : ∀ z : Fin n → ℝ,
      h z = ∫ t, f (z - t) * g t ∂(MeasureTheory.volume)) :
    ProbabilityDensity MeasureTheory.volume h ∧ LogConcave h := by
  sorry

end «problem-197»
