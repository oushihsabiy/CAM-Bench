import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-69»
/-
For a function f: ℝ^n → ℝ cup {+ ∞}, its convex conjugate f*: ℝ^n → ℝ cup {+ ∞} is defined by f*(y)
=
sup_{x∈ℝ^n}(yᵀ x - f(x)).
-/
def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup {r : EReal | ∃ x : Fin n → ℝ, r = (∑ i : Fin n, (y i) * (x i)) - f x}

/-
Given an optimization problem with objective function f₀, inequality constraint functions fᵢ, and
equality constraint functions hⱼ, the dual function is g(λ, nu) = inf_x (f₀(x) + sum_i λ_i fᵢ(x) +
sum_j
nu_j hⱼ(x)), with domain consisting of the multipliers for which the infimum is well defined.
-/
def newtonStepOneDimMax
    (g' g'' : ℝ → ℝ)
    (ν : ℝ) :
    Option ℝ :=
  if _h : g'' ν = 0 then
    none
  else
    some (-(g' ν) / (g'' ν))

/-
A simple operation count model for one Newton step in the separable dual problem: evaluate the
`n` coordinates contributing to g', evaluate the `n` coordinates contributing to g'', and then
perform a constant number of scalar operations.
-/
def separableEqualityDualNewtonStepOpCount (n : ℕ) : ℕ :=
  2 * n + 3

/-
Consider the optimization problem minimize & \sum_{i = 1}^n fᵢ(xᵢ); subject to &
\sum_{i = 1}^n xᵢ = 1, array with decision variable x = (x₁, ..., xₙ)∈ℝ^n, where each
function fᵢ: ℝ→ℝ is twice differentiable and satisfies fᵢ''(z) ≥ m > 0 for all z∈ℝ, i = 1, ..., n.
-/
structure SeparableEqualityConstrainedProblem where
  n : ℕ
  f : Fin n → ℝ → ℝ
  m : ℝ
  m_pos : 0 < m
  twiceDifferentiable : ∀ i : Fin n, ContDiff ℝ 2 (f i)
  secondDerivLowerBound : ∀ i : Fin n, ∀ z : ℝ, m ≤ deriv (deriv (f i)) z

/-
Define the dual function by g(nu) = - nu - \sum_{i = 1}^n fᵢ*(- nu), nu∈ℝ. For each nu∈ℝ, define
x(nu)∈ℝ^n by xᵢ(nu) = (fᵢ')^{- 1}(- nu), equivalently, xᵢ(nu) = (fᵢ*)'(- nu).
-/
def separableConvexConjugateReal
    (P : SeparableEqualityConstrainedProblem) :
    (ℝ → EReal) × (ℝ → Fin P.n → ℝ) :=
  let fi_conj : Fin P.n → ℝ → EReal :=
    fun i y => convexConjugate (fun z : Fin 1 → ℝ => (P.f i (z 0) : EReal)) (fun _ => y)
  let g : ℝ → EReal :=
    fun ν => ((-ν : ℝ) : EReal) - ∑ i : Fin P.n, fi_conj i (-ν)
  let x : ℝ → Fin P.n → ℝ :=
    fun ν i => deriv (fun y => (fi_conj i y).toReal) (-ν)
  (g, x)

def separableEqualityDualFunction
    (P : SeparableEqualityConstrainedProblem) :
    ℝ → EReal :=
  (separableConvexConjugateReal P).1

def separableEqualityDualX
    (P : SeparableEqualityConstrainedProblem) :
    ℝ → Fin P.n → ℝ :=
  (separableConvexConjugateReal P).2

structure SeparableEqualityDualData (P : SeparableEqualityConstrainedProblem) where
  dualFunction : ℝ → EReal
  x : ℝ → Fin P.n → ℝ

structure SeparableEqualityDualNewtonStepComputation
    (P : SeparableEqualityConstrainedProblem)
    (D : SeparableEqualityDualData P)
    (ν : ℝ) where
  gradientValue : ℝ
  curvatureValue : ℝ
  step : ℝ
  opCount : ℕ
  curvature_ne_zero : curvatureValue ≠ 0

/-
maximize g(ν).
-/
structure DualMaximizationProblem
    (P : SeparableEqualityConstrainedProblem) where
  objective : ℝ → EReal

def DualMaximizationProblem.mkDefault
    (P : SeparableEqualityConstrainedProblem) : DualMaximizationProblem P :=
  { objective := separableEqualityDualFunction P }

def DualMaximizationProblem.feasibleSet
    {P : SeparableEqualityConstrainedProblem} (_ : DualMaximizationProblem P) : Set ℝ :=
  Set.univ

/-
Consider the separable equality - constrained problem. For each i, let fᵢ* be the convex conjugate
of
fᵢ, fᵢ*(y) = sup_{x∈ℝ} (yx - fᵢ(x)). Assume that fᵢ* and (fᵢ*)' are readily computable, and that for
any scalar nu∈ℝ, the equation fᵢ'(x) = nu can be solved for x. Define the dual function by g(nu) =
- nu - \sum_{i = 1}^n fᵢ*(- nu), nu∈ℝ. For each nu∈ℝ, define x(nu)∈ℝ^n by xᵢ(nu) = (fᵢ')^{- 1}(-
nu),
equivalently xᵢ(nu) = (fᵢ*)'(- nu). Prove that the dual problem is the dual maximization problem,
and that g'(nu) = \sum_{i = 1}^n xᵢ(nu) - 1, g''(nu) = - \sum_{i = 1}^n (1)/(fᵢ''(xᵢ(nu))).
-/
theorem separableEqualityDual_derivatives
    (P : SeparableEqualityConstrainedProblem)
    (hfin : ∀ ν : ℝ, separableEqualityDualFunction P ν ≠ ⊤ ∧ separableEqualityDualFunction P ν ≠ ⊥)
    (hconj_fin :
      ∀ ν : ℝ, ∀ i : Fin P.n,
        convexConjugate (fun z : Fin 1 → ℝ => (P.f i (z 0) : EReal)) (fun _ => -ν) ≠ ⊤ ∧
          convexConjugate (fun z : Fin 1 → ℝ => (P.f i (z 0) : EReal)) (fun _ => -ν) ≠ ⊥)
    (hconj_diff :
      ∀ ν : ℝ, ∀ i : Fin P.n,
        DifferentiableAt ℝ
          (fun y : ℝ =>
            (convexConjugate (fun z : Fin 1 → ℝ => (P.f i (z 0) : EReal)) (fun _ => y)).toReal)
          (-ν))
    (hg_twice :
      ∀ ν : ℝ,
        DifferentiableAt ℝ (fun t : ℝ => (separableEqualityDualFunction P t).toReal) ν ∧
          DifferentiableAt ℝ
            (fun t : ℝ => deriv (fun s : ℝ => (separableEqualityDualFunction P s).toReal) t) ν) :
    (∀ ν : ℝ,
      ∀ i : Fin P.n,
        deriv (P.f i) (separableEqualityDualX P ν i) = -ν) ∧
    ((DualMaximizationProblem.mkDefault P).objective = separableEqualityDualFunction P ∧
      (DualMaximizationProblem.mkDefault P).feasibleSet = Set.univ) ∧
    (∀ ν : ℝ,
      deriv (fun t : ℝ => ((separableEqualityDualFunction P t).toReal)) ν
        = (∑ i : Fin P.n, separableEqualityDualX P ν i) - 1) ∧
    (∀ ν : ℝ,
      deriv (fun t : ℝ => deriv (fun s : ℝ => ((separableEqualityDualFunction P s).toReal)) t) ν
        = -∑ i : Fin P.n, (1 / deriv (deriv (P.f i)) (separableEqualityDualX P ν i))) := by
  sorry

/-
Consider the separable equality - constrained problem. For each i, let fᵢ* be the convex conjugate
of
fᵢ, fᵢ*(y) = sup_{x∈ℝ} (yx - fᵢ(x)). Assume that fᵢ* and (fᵢ*)' are readily computable, and that for
any scalar nu∈ℝ, the equation fᵢ'(x) = nu can be solved for x. Define the dual function by g(nu) =
- nu - \sum_{i = 1}^n fᵢ*(- nu), nu∈ℝ. For each nu∈ℝ, define x(nu)∈ℝ^n by xᵢ(nu) = (fᵢ')^{- 1}(-
nu),
equivalently xᵢ(nu) = (fᵢ*)'(- nu). Hence prove that a Newton step for the dual problem can be
computed with computational complexity of order n.
-/
theorem separableEqualityDual_newtonStep_complexity_linear
    (P : SeparableEqualityConstrainedProblem)
    (D : SeparableEqualityDualData P)
    (hdenom :
      ∀ ν : ℝ,
        (∑ i : Fin P.n, (1 / deriv (deriv (P.f i)) (D.x ν i))) ≠ 0) :
    ∀ ν : ℝ,
      ∃ comp : SeparableEqualityDualNewtonStepComputation P D ν,
        some comp.step =
          newtonStepOneDimMax
            (fun t => (∑ i : Fin P.n, D.x t i) - 1)
            (fun t => -∑ i : Fin P.n, (1 / deriv (deriv (P.f i)) (D.x t i)))
            ν ∧
        comp.opCount = separableEqualityDualNewtonStepOpCount P.n ∧
        comp.opCount = 2 * P.n + 3 ∧
        comp.opCount ≤ 5 * P.n + 5 := by
  sorry

end «problem-69»
