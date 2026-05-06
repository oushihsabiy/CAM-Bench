import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-11»
/- [BLOCK Exercise 2.27-(b) | 12 | defn]
A function f : ℝ^n → [0,∞) is log-concave if, for all x,y ∈ ℝ^n and all λ ∈ [0,1],
f(λ x+(1-λ)y) ≥ f(x)^λ f(y)^{1-λ}.
-/
def LogConcave {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ g : (Fin n → ℝ) → NNReal,
    (f = fun x => (g x : ℝ)) ∧
      ∀ x y : Fin n → ℝ, ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
        g (lam • x + (1 - lam) • y) ≥
          (if g x = 0 then
             if lam = 0 then 1 else 0
           else
             Real.toNNReal (Real.rpow (g x : ℝ) lam)) *
          (if g y = 0 then
             if lam = 1 then 1 else 0
           else
             Real.toNNReal (Real.rpow (g y : ℝ) (1 - lam)))

/- [BLOCK Exercise 2.27-(b) | 13 | defn]
A nonnegative measurable function f : ℝ^n → [0,∞) is a probability density of an ℝ^n-valued random
variable X if, for every measurable set A ⊆ ℝ^n,
prob(X ∈ A)=∈t_A f(x)dx,
and
∈t_{ℝ^n} f(x)dx = 1.
-/
def IsProbabilityDensity {Ω : Type*} {n : ℕ} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : Ω → (Fin n → ℝ)) (f : (Fin n → ℝ) → ENNReal) : Prop :=
  Measurable X ∧
  Measurable f ∧
  (∀ A : Set (Fin n → ℝ), MeasurableSet A →
    P (X ⁻¹' A) =
      ∫⁻ x in A, f x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))) ∧
  (∫⁻ x, f x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) = 1)

/- [BLOCK Exercise 2.27-(b) | 14 | thm]
Let X be an ℝ^n-valued random variable with density f:ℝ^n → [0,∞), where f is log-concave, meaning
that for all x,y ∈ ℝ^n and all λ ∈ [0,1], f(λ x+(1-λ)y) ≥ f(x)^λ f(y)^{1-λ}. Let g:ℝ^n → ℝ be a
convex function, and define the real-valued random variable Y=g(X). Define F(a)=prob(Y ≤
a)=prob(g(X)≤ a), a ∈ ℝ. Prove that F is a log-concave function of a; that is, for all a,b ∈ ℝ and
all λ ∈ [0,1], F(λ a+(1-λ)b) ≥ F(a)^λ F(b)^{1-λ}.
-/
theorem sublevel_distribution_logConcave
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → ℝ)
    (hX_meas : Measurable X)
    (hg_meas : Measurable g)
    (hgX_meas : Measurable fun ω => g (X ω))
    (hg_convex : ConvexOn ℝ Set.univ g)
    (hf_log : LogConcave f)
    (h_density : IsProbabilityDensity P X (fun x => ENNReal.ofReal (f x))) :
    ∀ a b lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      (P {ω | g (X ω) ≤ lam * a + (1 - lam) * b}).toReal ≥
        ((P {ω | g (X ω) ≤ a}).toReal) ^ lam *
          ((P {ω | g (X ω) ≤ b}).toReal) ^ (1 - lam) := by
  sorry

end «problem-11»
