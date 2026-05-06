import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-70»
/-
Random variables v₁, , vₘ are independent and identically distributed if they are mutually
independent and there exists a probability law P such that each vᵢ has distribution P.
-/
def ProbabilityDensity
    (p : ℝ → ℝ)
    (μ : MeasureTheory.Measure ℝ := MeasureTheory.volume) : Prop :=
  Measurable p ∧
  (∀ x, 0 ≤ p x) ∧
  ∫ x, p x ∂μ = 1


def LogConcave (f : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
  Convex ℝ {x : ℝ | f x > 0} ∧
  ∀ x y θ : ℝ,
    0 ≤ θ →
      θ ≤ 1 →
        f (θ * x + (1 - θ) * y) ≥ Real.rpow (f x) θ * Real.rpow (f y) (1 - θ)


structure LogLikelihoodConvexProgram where
  n : ℕ
  m : ℕ
  a : Fin m → Fin n → ℝ
  y : Fin m → ℝ
  g : ℝ → ℝ
def LogLikelihoodConvexProgram.residual
    (P : LogLikelihoodConvexProgram) (x : Fin P.n → ℝ) (μ σ : ℝ) (i : Fin P.m) : ℝ :=
  (P.y i - ∑ j : Fin P.n, P.a i j * x j - μ) / σ

def LogLikelihoodConvexProgram.objective
    (P : LogLikelihoodConvexProgram) (x : Fin P.n → ℝ) (μ σ : ℝ) : ℝ :=
  P.m * Real.log σ + ∑ i : Fin P.m, P.g (P.residual x μ σ i)

def LogLikelihoodConvexProgram.isFeasible
    (P : LogLikelihoodConvexProgram) (_x : Fin P.n → ℝ) (_μ σ : ℝ) : Prop :=
  0 < σ

def LogLikelihoodConvexProgram.transformedResidual
    (P : LogLikelihoodConvexProgram) (w : Fin P.n → ℝ) (ν t : ℝ) (i : Fin P.m) : ℝ :=
  P.y i * t - ∑ j : Fin P.n, P.a i j * w j - ν

def LogLikelihoodConvexProgram.transformedObjective
    (P : LogLikelihoodConvexProgram) (w : Fin P.n → ℝ) (ν t : ℝ) : ℝ :=
  -(P.m : ℝ) * Real.log t + ∑ i : Fin P.m, P.g (P.transformedResidual w ν t i)


-- /-
-- Consider the linear measurement model yᵢ = a_iᵀ x + vᵢ, i = 1, ..., m, where m ≥ 1, the data yᵢ∈ ℝ
-- and
-- aᵢ∈ ℝ^n are given, and the unknown parameter is x∈ ℝ^n. Assume that v₁, ..., vₘ are independent and
-- identically distributed with density p(z) = (1)/(σ)f((z - μ)/(σ)), where f: ℝ→ ℝ_ + is a given
-- normalized density satisfying int_{ℝ} f(t)dt = 1, and μ∈ ℝ and σ > 0 are unknown scalar parameters.
-- Let g(t) = - log f(t) on the set where f(t) > 0, and assume that f is log - concave, equivalently,
-- that
-- g is convex on its effective domain. Prove that maximizing the log - likelihood - mlog σ + \sum_{i =
-- 1}^m
-- log f((yᵢ - a_iᵀ x - μ)/(σ)) over x∈ℝ^n, μ∈ℝ, and σ > 0 is equivalent to solving log - likelihood
-- convex
-- program and that this objective is convex in (x, μ, σ).
-- -/
-- theorem maximizing_logLikelihood_equiv_logLikelihoodConvexProgram
--     (P : LogLikelihoodConvexProgram)
--     (f : ℝ → ℝ)
--     (hf_density : ProbabilityDensity f)
--     (hf_logConcave : LogConcave f)
--     -- g(t) = - log f(t) on the support where f(t) > 0
--     (hg : ∀ t, 0 < f t → P.g t = -Real.log (f t)) :
--     -- (1) The log - likelihood equals - P.objective at any feasible (x, μ, σ) where f > 0 at all
--     -- residuals,
--     -- so maximizing the log - likelihood is equivalent to minimizing P.objective.
--     (∀ (x : Fin P.n → ℝ) (μ σ : ℝ),
--       P.isFeasible x μ σ →
--       (∀ i : Fin P.m, 0 < f (P.residual x μ σ i)) →
--       -(↑P.m * Real.log σ) + ∑ i : Fin P.m, Real.log (f (P.residual x μ σ i))
--         = -(P.objective x μ σ)) ∧
--     -- (2) P.objective is convex on the effective domain where σ > 0 and every residual lies in
--     -- the support of f, so that g(t) = -log f(t) is actually specified at each residual value.
--     ConvexOn ℝ
--       {p : (Fin P.n → ℝ) × ℝ × ℝ |
--         0 < p.2.2 ∧ ∀ i : Fin P.m, 0 < f (P.residual p.1 p.2.1 p.2.2 i)}
--       (fun p => P.objective p.1 p.2.1 p.2.2) := by
--     sorry

theorem maximizing_logLikelihood_equiv_logLikelihoodConvexProgram
    (P : LogLikelihoodConvexProgram)
    (f : ℝ → ℝ)
    (hf_density : ProbabilityDensity f)
    (hf_logConcave : LogConcave f)
    -- g(t) = - log f(t) on the support where f(t) > 0
    (hg : ∀ t, 0 < f t → P.g t = -Real.log (f t))
    (hg_convex :
      ConvexOn ℝ
        {r : ℝ | 0 < f r}
        P.g) :
    -- (1) Under the change of variables w = x/σ, ν = μ/σ, t = 1/σ, the original log-likelihood
    -- equals the negative of the transformed objective, so maximizing the log-likelihood is
    -- equivalent to minimizing the transformed objective.
    (∀ (x : Fin P.n → ℝ) (μ σ : ℝ),
      P.isFeasible x μ σ →
      (∀ i : Fin P.m, 0 < f (P.residual x μ σ i)) →
      (let w : Fin P.n → ℝ := fun j => x j / σ;
       let ν : ℝ := μ / σ;
       let t : ℝ := 1 / σ;
       -(↑P.m * Real.log σ) + ∑ i : Fin P.m, Real.log (f (P.residual x μ σ i))
         = -(P.transformedObjective w ν t))) ∧
    -- (2) The transformed objective is convex on the natural domain t > 0 where every transformed
    -- residual lies in the support of f.
    ConvexOn ℝ
      {p : (Fin P.n → ℝ) × ℝ × ℝ |
        0 < p.2.2 ∧ ∀ i : Fin P.m, 0 < f (P.transformedResidual p.1 p.2.1 p.2.2 i)}
      (fun p => P.transformedObjective p.1 p.2.1 p.2.2) := by
  sorry


end «problem-70»
