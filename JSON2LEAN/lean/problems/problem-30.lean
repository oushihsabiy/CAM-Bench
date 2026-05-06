import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-30»
/- [BLOCK Exercise 2.27-(c) | 15 | defn]
A density function f : ℝ^n → [0,∞) is log-concave if for all x,y ∈ ℝ^n and all θ ∈ [0,1],
f(θ x + (1-θ)y) ≥ f(x)^θ f(y)^{1-θ}.
Equivalently, log f is concave on {x : f(x)>0}.
-/
def IsLogConcaveDensity {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ g : (Fin n → ℝ) → NNReal,
    (f = fun x => (g x : ℝ)) ∧
      ∀ x y : Fin n → ℝ, ∀ θ : ℝ,
        0 ≤ θ →
          θ ≤ 1 →
            (g (θ • x + (1 - θ) • y) : ℝ) ≥
              Real.rpow (g x : ℝ) θ * Real.rpow (g y : ℝ) (1 - θ)

/- [BLOCK Exercise 2.27-(c) | 16 | defn]
A function φ : D → [0,∞) on a convex set D is log-concave if for all a,b ∈ D and all θ ∈ [0,1],
φ(θ a + (1-θ)b) ≥ φ(a)^θ φ(b)^{1-θ}.
-/
def IsLogConcaveOn {n : ℕ} (D : Set (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) : Prop :=
  Convex ℝ D ∧
    (∀ a ∈ D, ∀ b ∈ D, ∀ θ : ℝ,
      0 ≤ θ →
        θ ≤ 1 →
          φ (θ • a + (1 - θ) • b) ≥ Real.rpow (φ a) θ * Real.rpow (φ b) (1 - θ)) ∧
    (∀ a ∈ D, 0 ≤ φ a)

/- [BLOCK Exercise 2.27-(c) | 17 | thm]
Let X be an ℝ^n-valued random variable with log-concave density f:ℝ^n → [0,∞), where f is a density
with respect to Lebesgue measure and log f is concave on the support of f. Let g:ℝ^n → ℝ be concave,
and set Y=g(X). For a∈ ℝ, define φ(a)=E((Y-a)_+), (s)_+=s,0. Assume φ(a) exists for all a∈ℝ. Prove
that φ is convex and log-concave on ℝ; that is, for all a,b∈ ℝ and all θ∈[0,1], φ(θ a+(1-θ)b)≤
θφ(a)+(1-θ)φ(b) and φ(θ a+(1-θ)b)≥ φ(a)^θφ(b)^{1-θ}.
-/
theorem positivePartExpectation_convex_and_logConcave
    {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → ℝ)
    (φ : ℝ → ℝ)
    (hf : IsLogConcaveDensity f)
    (hf_density : ∫ x, f x = 1)
    (hf_integrable : MeasureTheory.Integrable f)
    (hg : ConcaveOn ℝ Set.univ g)
    (hφ_integrable : ∀ a : ℝ, MeasureTheory.Integrable (fun x => max (g x - a) 0 * f x))
    (hφ : ∀ a : ℝ, φ a = ∫ x, max (g x - a) 0 * f x) :
    (∀ a : ℝ, 0 ≤ φ a) ∧
      (∀ a b θ : ℝ,
        0 ≤ θ →
          θ ≤ 1 →
            φ (θ * a + (1 - θ) * b) ≤ θ * φ a + (1 - θ) * φ b) ∧
      (∀ a b θ : ℝ,
        0 ≤ θ →
          θ ≤ 1 →
            φ (θ * a + (1 - θ) * b) ≥
              Real.rpow (φ a) θ * Real.rpow (φ b) (1 - θ)) := by
  sorry

end «problem-30»
