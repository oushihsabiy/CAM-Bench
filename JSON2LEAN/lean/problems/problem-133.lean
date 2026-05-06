import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-133»
/-
A nonlinear program is an optimization problem of the form min_x f(x) subject to equality
constraints cᵢ(x) = 0 for i∈mathcal E and inequality constraints cᵢ(x) ≥ 0 for i∈I}, where
at least one of the functions involved is nonlinear.
-/
structure NonlinearProgram (α : Type*) [AddCommMonoid α] [Module ℝ α] where
  f : α → ℝ
  equalityIndex : Type*
  equalityConstraint : equalityIndex → α → ℝ
  inequalityIndex : Type*
  inequalityConstraint : inequalityIndex → α → ℝ
  nonlinear : ¬ ((∃ a : α →ₗ[ℝ] ℝ, f = a) ∧
    (∀ i : equalityIndex, ∃ a : α →ₗ[ℝ] ℝ, equalityConstraint i = a) ∧
    (∀ i : inequalityIndex, ∃ a : α →ₗ[ℝ] ℝ, inequalityConstraint i = a))
/-
-/
def NonlinearProgram.IsFeasible {α : Type*} [AddCommMonoid α] [Module ℝ α]
    (P : NonlinearProgram α) (x : α) : Prop :=
  (∀ i : P.equalityIndex, P.equalityConstraint i x = 0) ∧
  ∀ i : P.inequalityIndex, 0 ≤ P.inequalityConstraint i x

/-
Let g: mathbf ℝ^n→R. A point x is a stationary point of g if D(g(x); p) ≥ 0 for all p∈mathbf
ℝ^n, where D(g(x); p) = lim_{αdownarrow 0}(g(x + α p) - g(x))/(α) whenever the limit exists.
-/
def IsStationaryPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℝ) (x : E) : Prop :=
  ∀ p : E, ∀ d : ℝ,
    Tendsto
      (fun α : ℝ => (g (x + α • p) - g x) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 d) →
      0 ≤ d

/-
A point x is an infeasible stationary point for the nonlinear program if x is infeasible for the
constraints and D(h(x); p) ≥ 0 for all p∈mathbf ℝ^n.
-/
def NonlinearProgram.IsInfeasible {α : Type*} [AddCommMonoid α] [Module ℝ α]
    (P : NonlinearProgram α) (x : α) : Prop :=
  (∃ i : P.equalityIndex, P.equalityConstraint i x ≠ 0) ∨
    ∃ i : P.inequalityIndex, P.inequalityConstraint i x < 0

/-
Given an objective function f, a constraint - violation measure h, and μ > 0, the function φ_1(x; μ)
=
f(x) + μ h(x) is an exact penalty function if there exists barμ > 0 such that every minimizer of the
constrained problem is a minimizer of φ_1(·; μ) for all μ ≥ barμ.
-/
structure DifferentiableNonlinearProgram (n : ℕ) where
  equalityIndex : Type*
  inequalityIndex : Type*
  f : (Fin n → ℝ) → ℝ
  equalityConstraint : equalityIndex → (Fin n → ℝ) → ℝ
  inequalityConstraint : inequalityIndex → (Fin n → ℝ) → ℝ
  f_differentiable : Differentiable ℝ f
  equalityConstraint_differentiable :
    ∀ i : equalityIndex, Differentiable ℝ (equalityConstraint i)
  inequalityConstraint_differentiable :
    ∀ i : inequalityIndex, Differentiable ℝ (inequalityConstraint i)
  nonlinear : ¬ ((∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, f = a) ∧
    (∀ i : equalityIndex, ∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, equalityConstraint i = a) ∧
    (∀ i : inequalityIndex, ∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, inequalityConstraint i = a))

private lemma DifferentiableNonlinearProgram.nonlinear_for_toNonlinearProgram
    {n : ℕ} (P : DifferentiableNonlinearProgram n) :
    ¬ ((∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, P.f = a) ∧
      (∀ i : P.equalityIndex, ∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, P.equalityConstraint i = a) ∧
      (∀ i : P.inequalityIndex, ∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, P.inequalityConstraint i = a)) :=
  P.nonlinear

def DifferentiableNonlinearProgram.toNonlinearProgram
    {n : ℕ} (P : DifferentiableNonlinearProgram n) :
    NonlinearProgram (Fin n → ℝ) where
  f := P.f
  equalityIndex := P.equalityIndex
  equalityConstraint := P.equalityConstraint
  inequalityIndex := P.inequalityIndex
  inequalityConstraint := P.inequalityConstraint
  nonlinear := by
    exact DifferentiableNonlinearProgram.nonlinear_for_toNonlinearProgram P

def DifferentiableNonlinearProgram.IsFeasible
    {n : ℕ} (P : DifferentiableNonlinearProgram n) (x : Fin n → ℝ) : Prop :=
  P.toNonlinearProgram.IsFeasible x

/-
Exercise 17.8 | 62 | thm

Let f: ℝⁿ → ℝ and cᵢ: ℝⁿ → ℝ for i ∈ E ∪ I be differentiable, where E and I are given index sets.
Consider the nonlinear program minₓ f(x) subject to cᵢ(x) = 0 for i ∈ E, cᵢ(x) ≥ 0 for i ∈ I. Define

h(x) = ∑_{i ∈ E} |cᵢ(x)| + ∑_{i ∈ I} [cᵢ(x)]⁻,

[t]⁻: = {0 if t ∈ ℝ, - t if t ∈ ℝ,

and, for μ > 0, φ₁(x; μ) = f(x) + μ h(x). For a function g: ℝⁿ → ℝ, say that x is a stationary point
of g if D(g(x); p) ≥ 0 for all p ∈ ℝⁿ, where

D(g(x); p) = lim_{α ↓ 0} (g(x + αp) - g(x)) / α

whenever the limit exists. Say that x is an infeasible stationary point for the nonlinear program if
x is infeasible for the constraints and D(h(x); p) ≥ 0 for all p ∈ ℝⁿ. Assume that there exists μ >
0 such that x ∈ ℝⁿ is a stationary point of φ₁(·; μ) for every μ > μ, and that x is infeasible for
the nonlinear program. Using

D(φ₁(x; μ); p) = ∇f(x)ᵀp + μ D(h(x); p),

prove that x is an infeasible stationary point for the nonlinear program.
-/
theorem infeasible_of_eventually_stationary_penalty
    {n : ℕ}
    (P : DifferentiableNonlinearProgram n)
    [Fintype P.equalityIndex] [Fintype P.inequalityIndex]
    (h : (Fin n → ℝ) → ℝ)
    (h_def : h =
      fun x : Fin n → ℝ =>
        (∑ i : P.equalityIndex, |P.equalityConstraint i x|) +
        ∑ i : P.inequalityIndex, max 0 (-P.inequalityConstraint i x))
    (xhat : Fin n → ℝ) (muhat : ℝ)
    (h_muhat_pos : 0 < muhat)
    (h_infeasible : P.toNonlinearProgram.IsInfeasible xhat)
    (h_stationary :
      ∀ μ : ℝ, muhat < μ →
        IsStationaryPoint (fun x : Fin n → ℝ => P.f x + μ * h x) xhat) :
    P.toNonlinearProgram.IsInfeasible xhat ∧ IsStationaryPoint h xhat := by
  sorry

end «problem-133»