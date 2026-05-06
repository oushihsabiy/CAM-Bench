import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-36»
/-
Let f: ℝ^n → ℝ and cᵢ: ℝ^n → ℝ for i ∈ I be given, where I is the index set of
constraints. Consider the optimization problem min_{x ∈ ℝ^n} f(x) s. t. cᵢ(x) ≤ 0, i ∈ I.
-/
structure InequalityConstrainedOptimizationProblem (n ι : Type) where
  objective : (n → ℝ) → ℝ
  constraint : ι → (n → ℝ) → ℝ

def InequalityConstrainedOptimizationProblem.IsFeasible
    {n ι : Type} (P : InequalityConstrainedOptimizationProblem n ι) (x : n → ℝ) : Prop :=
  ∀ i : ι, P.constraint i x ≤ 0

def InequalityConstrainedOptimizationProblem.ObjectiveValue
    {n ι : Type} (P : InequalityConstrainedOptimizationProblem n ι) (x : n → ℝ) : ℝ :=
  P.objective x

/-
The unconstrained problem min_{x ∈ ℝ^n} F(x)
-/
structure UnconstrainedOptimizationProblem (n : Type) where
  objective : (n → ℝ) → EReal


def UnconstrainedOptimizationProblem.ObjectiveValue
    {n : Type} (P : UnconstrainedOptimizationProblem n) (x : n → ℝ) : EReal :=
  P.objective x

def InequalityConstrainedOptimizationProblem.supremumReformulation
    {n ι : Type} [Fintype ι] (P : InequalityConstrainedOptimizationProblem n ι) :
    UnconstrainedOptimizationProblem n :=
  { objective := fun x =>
      sSup {s : EReal | ∃ lam : ι → ℝ, (∀ i : ι, 0 ≤ lam i) ∧
        s = ((P.objective x + ∑ i : ι, lam i * P.constraint i x : ℝ) : EReal)} }

/-
Let f: ℝ^n → ℝ and cᵢ: ℝ^n → ℝ (i ∈ I) be given functions, and let I be the
constraint index set. Consider the inequality constrained optimization problem min_{x ∈ ℝ^n} f(x) s.
t. cᵢ(x) ≤ 0, i ∈ I. Define F(x) = sup_{λ_i ≥ 0, i ∈ I}{f(x) + \sum_{i∈I}λ_i
cᵢ(x)}, where the supremum is taken over all multiplier vectors satisfying λ_i ≥ 0 (i ∈ I).
Prove that the original problem is equivalent to unconstrained supremum reformulation. Here,
“equivalent” means: The two problems have the same optimal value.
-/
theorem inequality_constrained_problem_eq_unconstrained_supremum_reformulation
    {n ι : Type} [Fintype ι]
    (P : InequalityConstrainedOptimizationProblem n ι)
    (h_feasible : ∃ x : n → ℝ, P.IsFeasible x) :
    let Q : UnconstrainedOptimizationProblem n := P.supremumReformulation
    sInf {r : EReal | ∃ x : n → ℝ, P.IsFeasible x ∧ ((P.ObjectiveValue x : ℝ) : EReal) = r} =
      sInf {r : EReal | ∃ x : n → ℝ, Q.ObjectiveValue x = r} := by
  sorry

/-
Let f: ℝ^n → ℝ and cᵢ: ℝ^n → ℝ (i ∈ I) be given functions, and let I be the
constraint index set. Consider the inequality constrained optimization problem min_{x ∈ ℝ^n} f(x) s.
t. cᵢ(x) ≤ 0, i ∈ I. Define F(x) = sup_{λ_i ≥ 0, i ∈ I}{f(x) + \sum_{i∈I}λ_i
cᵢ(x)}, where the supremum is taken over all multiplier vectors satisfying λ_i ≥ 0 (i ∈ I).
Prove that the original problem is equivalent to unconstrained supremum reformulation. Here,
“equivalent” means: The set of optimal solutions of the original problem coincides with the set of
optimal solutions of the unconstrained problem min_{x ∈ ℝ^n} F(x).
-/
theorem inequality_constrained_problem_and_unconstrained_supremum_reformulation_have_same_optimal_solutions
    {n ι : Type} [Fintype ι]
    (P : InequalityConstrainedOptimizationProblem n ι)
    (h_feasible : ∃ x : n → ℝ, P.IsFeasible x) :
    let Q : UnconstrainedOptimizationProblem n := P.supremumReformulation
    {x : n → ℝ |
        P.IsFeasible x ∧
        ∀ y : n → ℝ, P.IsFeasible y → P.ObjectiveValue x ≤ P.ObjectiveValue y} =
      {x : n → ℝ |
        ∀ y : n → ℝ, Q.ObjectiveValue x ≤ Q.ObjectiveValue y} := by
  sorry


end «problem-36»
