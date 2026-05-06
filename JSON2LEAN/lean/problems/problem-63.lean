import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-63»
/-
A collection of equations and inequalities is called the optimality conditions for an optimization
problem if every optimal point satisfies them. In smooth constrained optimization, this usually
refers to first - order necessary conditions such as the KKT conditions.
-/
def OptimalityConditions {α : Type _} (isOptimal : α → Prop) (conds : α → Prop) : Prop :=
  ∀ ⦃x : α⦄, isOptimal x → conds x

/-
Consider the optimization problem max_{x ∈ ℝ^n} \sum_{j = 1}^m π_j log(p_jᵀ x) subject to 1ᵀ x = 1,
x
succeq 0, where 1 ∈ ℝ^n is the all - ones vector, x succeq 0 means xᵢ ≥ 0 for i = 1, ..., n, and pⱼ
∈
ℝ^n are given vectors for j = 1, ..., m. The probabilities satisfy π_j > 0 for j = 1, ..., m,
\sum_{j =
1}^m π_j = 1. Assume that p_jᵀ x > 0 for every feasible x at which the objective is evaluated.
-/
structure LogUtilitySimplexMaximization where
  n : ℕ
  m : ℕ
  p : Fin m → Fin n → ℝ
  π : Fin m → ℝ
  pi_pos : ∀ j : Fin m, 0 < π j
  pi_sum_one : (∑ j : Fin m, π j) = 1
  payoff_pos_on_simplex :
    ∀ x : Fin n → ℝ,
      ((∑ i : Fin n, x i) = 1 ∧ ∀ i : Fin n, 0 ≤ x i) →
      ∀ j : Fin m, 0 < ∑ i : Fin n, p j i * x i

def LogUtilitySimplexMaximization.Feasible (P : LogUtilitySimplexMaximization) (x : Fin P.n → ℝ) : Prop :=
  (∑ i : Fin P.n, x i) = 1 ∧ ∀ i : Fin P.n, 0 ≤ x i

def LogUtilitySimplexMaximization.payoff (P : LogUtilitySimplexMaximization) (j : Fin P.m)
    (x : Fin P.n → ℝ) : ℝ :=
  ∑ i : Fin P.n, P.p j i * x i

def LogUtilitySimplexMaximization.objective (P : LogUtilitySimplexMaximization)
    (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.m, P.π j * Real.log (P.payoff j x)

def LogUtilitySimplexMaximization.objectiveDefined (P : LogUtilitySimplexMaximization)
    (x : Fin P.n → ℝ) : Prop :=
  ∀ j : Fin P.m, 0 < P.payoff j x

def LogUtilitySimplexMaximization.isOptimal (P : LogUtilitySimplexMaximization)
    (x : Fin P.n → ℝ) : Prop :=
  P.Feasible x ∧ P.objectiveDefined x ∧
    ∀ y : Fin P.n → ℝ, P.Feasible y → P.objectiveDefined y → P.objective y ≤ P.objective x

/-
Consider the optimization problem log - utility simplex maximization. Show that the optimality
conditions for this problem can be written as 1ᵀ x = 1, x succeq 0, and, for each i = 1, ..., n, xᵢ
>
0 implies \sum_{j = 1}^m π_j \frac{p_{ij}}{p_jᵀ x} = 1, xᵢ = 0 implies \sum_{j = 1}^m π_j
\frac{p_{ij}}{p_jᵀ x} ≤ 1.
-/
theorem logUtilitySimplexMaximization_optimality_conditions
    (P : LogUtilitySimplexMaximization)
    (conds : Fin P.n → (Fin P.n → ℝ) → Prop := fun i x =>
      if 0 < x i then
        (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) = 1
      else
        (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) ≤ 1) :
    OptimalityConditions P.isOptimal
      (fun x =>
        P.Feasible x ∧
        P.objectiveDefined x ∧
        ∀ i : Fin P.n,
          (0 < x i →
            (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) = 1) ∧
          (x i = 0 →
            (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) ≤ 1)) := by
  sorry

end «problem-63»