import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-91»
/-
The domain of an extended - real - valued function f is dom f = {x | f(x) < + infinity}.
-/
def domain {α : Type*} (f : α → EReal) : Set α := {x | f x < ⊤}

/-
Given a function f and a feasible set C, a point x* in C is optimal if f(x*) < = f(y) for all y in
C.
-/
def IsOptimalPoint {α β : Type*} [Preorder β] (f : α → β) (C : Set α) (xStar : α) : Prop :=
  xStar ∈ C ∧ ∀ ⦃y : α⦄, y ∈ C → f xStar ≤ f y

/-
Consider the optimization problem: minimize f₀(x) = - \sum_{i = 1}^m log(bᵢ - a_iᵀ x) over x ∈ ℝ^n,
with domain dom f₀ = {x ∈ ℝ^n | Ax < b} = {x ∈ ℝ^n | a_iᵀ x < bᵢ for i = 1, ..., m}.
-/
open scoped BigOperators

structure LogBarrierOptimizationProblem where
  n : ℕ
  m : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def LogBarrierOptimizationProblem.slack
    (p : LogBarrierOptimizationProblem) (x : Fin p.n → ℝ) (i : Fin p.m) : ℝ :=
  p.b i - ∑ j : Fin p.n, p.A i j * x j

def LogBarrierOptimizationProblem.isFeasible
    (p : LogBarrierOptimizationProblem) (x : Fin p.n → ℝ) : Prop :=
  ∀ i : Fin p.m, (∑ j : Fin p.n, p.A i j * x j) < p.b i

def LogBarrierOptimizationProblem.feasibleSet
    (p : LogBarrierOptimizationProblem) : Set (Fin p.n → ℝ) :=
  {x | p.isFeasible x}

def LogBarrierOptimizationProblem.objective
    (p : LogBarrierOptimizationProblem) (x : Fin p.n → ℝ) : EReal := by
  classical
  exact
    if p.isFeasible x then
      (↑(- ∑ i : Fin p.m, Real.log (p.slack x i)) : EReal)
    else
      ⊤

def LogBarrierOptimizationProblem.domainSet
    (p : LogBarrierOptimizationProblem) : Set (Fin p.n → ℝ) :=
  domain p.objective

/-
Let A ∈ ℝ^(m x n) have rows a_iᵀ for i = 1, ..., m, and let b ∈ ℝ^m have components bᵢ. Consider
logarithmic barrier minimization and assume dom f₀ is nonempty. Let X_opt = {x in dom f₀ | f₀(x) < =
f₀(y) for all y in dom f₀} be the set of optimal points. Prove that for every x* in X_opt, X_opt =
{x* + v | Av = 0}.
-/
theorem optimalSet_eq_translate_of_ker_for_logBarrier
    (p : LogBarrierOptimizationProblem)
    (hdom : (p.domainSet).Nonempty)
    (xStar : Fin p.n → ℝ)
    (hxStar : IsOptimalPoint p.objective p.domainSet xStar) :
    {x : Fin p.n → ℝ | IsOptimalPoint p.objective p.domainSet x} =
      {x : Fin p.n → ℝ |
        ∃ v : Fin p.n → ℝ,
          Matrix.mulVec p.A v = 0 ∧ x = fun j => xStar j + v j} := by
  sorry
end «problem-91»