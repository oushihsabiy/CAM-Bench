import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-136»
/-
Exercise 6.1 | 15 | defn

Random variables v₁, …, vₘ are independent and identically distributed if they are mutually
independent and there exists a probability distribution P such that vᵢ ∼ P for every i = 1, …, m.
-/
def IsProbabilityDensityFunction (p : ℝ → ℝ) : Prop :=
  Measurable p ∧ (∀ z : ℝ, 0 ≤ p z) ∧ ∫ z : ℝ, p z = 1

/-
A function f: ℝ^n → ℝ_ + is log - concave if its support is convex and, for all x, y in its support
and
all θ ∈ [0, 1], f(θ x + (1 - θ)y) ≥ f(x)^θ f(y)^1 - θ.
-/
def IsLogConcave {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
    Convex ℝ {x : Fin n → ℝ | 0 < f x} ∧
    ∀ ⦃x y : Fin n → ℝ⦄,
      x ∈ {x : Fin n → ℝ | 0 < f x} →
      y ∈ {x : Fin n → ℝ | 0 < f x} →
      ∀ ⦃θ : ℝ⦄, θ ∈ Set.Icc (0 : ℝ) 1 →
        f (θ • x + (1 - θ) • y) ≥
          Real.rpow (f x) θ * Real.rpow (f y) (1 - θ)

/-
The effective domain of an extended - real - valued function g: ℝ^n → ℝ cup {+ ∞} is dom g = {x ∈
ℝ^n | g
x < + ∞}.
-/
def LogLikelihood (L : α → ℝ) : α → EReal :=
  fun θ => if 0 < L θ then (Real.log (L θ) : EReal) else ⊤

/-
The convex optimization problem min_{x∈ℝ^n, μ∈ℝ, σ > 0} (mlog σ + \sum_{i = 1}^m g((yᵢ - a_iᵀ x -
μ)/(σ))).
-/
structure LogConcaveLocationScaleMLE where
  n : ℕ
  m : ℕ
  y : Fin m → ℝ
  a : Fin m → Fin n → ℝ
  g : ℝ → EReal

def LogConcaveLocationScaleMLE.objective
    (p : LogConcaveLocationScaleMLE) :
    (Fin p.n → ℝ) → ℝ → ℝ → EReal :=
  fun x μ σ =>
    (p.m : EReal) * Real.log σ +
      ∑ i : Fin p.m, p.g (((p.y i) - (∑ j : Fin p.n, p.a i j * x j) - μ) / σ)

def LogConcaveLocationScaleMLE.isFeasible
    (p : LogConcaveLocationScaleMLE) :
    (Fin p.n → ℝ) → ℝ → ℝ → Prop :=
  fun _ _ σ => 0 < σ

def LogConcaveLocationScaleMLE.precisionObjective
    (p : LogConcaveLocationScaleMLE) :
    (Fin p.n → ℝ) → ℝ → ℝ → EReal :=
  fun z ν τ =>
    -((p.m : EReal) * Real.log τ) +
      ∑ i : Fin p.m, p.g (τ * p.y i - (∑ j : Fin p.n, p.a i j * z j) - ν)

def LogConcaveLocationScaleMLE.precisionFeasible
    (p : LogConcaveLocationScaleMLE) :
    (Fin p.n → ℝ) → ℝ → ℝ → Prop :=
  fun _ _ τ => 0 < τ

theorem logConcaveLocationScaleMLE_precision_reformulation_convex
    (p : LogConcaveLocationScaleMLE)
    (f : ℝ → ℝ)
    (hf_logconcave : IsLogConcave (n := 1) (fun x : Fin 1 → ℝ => f (x 0)))
    (hg : p.g = fun t => if 0 < f t then (-Real.log (f t) : EReal) else ⊤) :
    (∀ r s θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      p.g (θ * r + (1 - θ) * s) ≤
        (θ : EReal) * p.g r + ((1 - θ : ℝ) : EReal) * p.g s) ∧
    (∀ x : Fin p.n → ℝ, ∀ μ σ τ : ℝ,
      p.isFeasible x μ σ →
      τ = σ⁻¹ →
      p.precisionObjective (fun j => τ * x j) (τ * μ) τ = p.objective x μ σ) ∧
    Convex ℝ {u : (Fin p.n → ℝ) × ℝ × ℝ | p.precisionFeasible u.1 u.2.1 u.2.2} ∧
    ∀ u u' : (Fin p.n → ℝ) × ℝ × ℝ, ∀ θ : ℝ,
      u ∈ {u : (Fin p.n → ℝ) × ℝ × ℝ | p.precisionFeasible u.1 u.2.1 u.2.2} →
      u' ∈ {u : (Fin p.n → ℝ) × ℝ × ℝ | p.precisionFeasible u.1 u.2.1 u.2.2} →
      0 ≤ θ →
      θ ≤ 1 →
      p.precisionObjective
          (fun i => θ * u.1 i + (1 - θ) * u'.1 i)
          (θ * u.2.1 + (1 - θ) * u'.2.1)
          (θ * u.2.2 + (1 - θ) * u'.2.2) ≤
        ((θ : EReal) * p.precisionObjective u.1 u.2.1 u.2.2 +
          ((1 - θ : ℝ) : EReal) * p.precisionObjective u'.1 u'.2.1 u'.2.2) := by
  sorry

end «problem-136»
