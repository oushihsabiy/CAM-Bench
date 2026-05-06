import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-131»
/-
The linear independence constraint qualification holds at a feasible point if the gradients of all
equality constraints together with the gradients of all inequality constraints active at that point
are linearly independent.
-/
def LinearIndependenceConstraintQualification
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    (eqConstr : ι → E → ℝ) (ineqConstr : κ → E → ℝ) (x : E) : Prop :=
  LinearIndependent ℝ
    (fun z : Sum ι {j : κ // ineqConstr j x = 0} =>
      Sum.elim
        (fun i : ι => gradient (eqConstr i) x)
        (fun j => gradient (ineqConstr j.1) x)
        z)

/-
An inequality constraint is active at a feasible point if it is satisfied with equality at that
point.
-/
def ActiveInequalityConstraint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Type*}
    (ineqConstr : κ → E → ℝ) (x : E) (j : κ) : Prop :=
  ineqConstr j x = 0

/-
For a feasible point of a problem with inequality constraints gⱼ(x) ≥ 0, the active set is A(x) =
{j: gⱼ(x) = 0}; equivalently, it is the set of indices of the inequality constraints active at that
point.
-/
def SlackEqualityReformulation
    {E : Type*} {κ : Type*}
    (ineqConstr : κ → E → ℝ) : (E × (κ → ℝ)) → κ → ℝ :=
  fun xs j => ineqConstr j xs.1 - xs.2 j

def SlackVariableReformulation
    {E : Type*} {κ : Type*}
    (ineqConstr : κ → E → ℝ) (xs : E × (κ → ℝ)) : Prop :=
  (∀ j : κ, ineqConstr j xs.1 - xs.2 j = 0) ∧
  (∀ j : κ, 0 ≤ xs.2 j)

/-
Exercise 19.1 - (c) | 18 | opt_prob

Let f: ℝⁿ → ℝ, c_e: ℝⁿ → ℝ^{m_e}, and cᵢ: ℝⁿ → ℝ^{mᵢ} be continuously differentiable. Consider the
nonlinear program

min f(x) subject to c_e(x) = 0, cᵢ(x) ≥ 0,

where (cᵢ(x))ⱼ ≥ 0 for j = 1, …, mᵢ. Also consider the slack - variable reformulation

min_{x, s} f(x) subject to c_e(x) = 0, cᵢ(x) - s = 0, s ≥ 0,

with s ∈ ℝ^{mᵢ} and sⱼ ≥ 0 for j = 1, …, mᵢ.
-/
structure NonlinearProgramWithSlackReformulation
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ι : Type*) (κ : Type*) where
  objective : E → ℝ
  eqConstr : ι → E → ℝ
  ineqConstr : κ → E → ℝ
  objectiveContDiff : ContDiff ℝ ⊤ objective
  eqConstrContDiff : ∀ i : ι, ContDiff ℝ ⊤ (eqConstr i)
  ineqConstrContDiff : ∀ j : κ, ContDiff ℝ ⊤ (ineqConstr j)
  slackEqConstr : (E × (κ → ℝ)) → κ → ℝ := SlackEqualityReformulation ineqConstr
  slackObjective : E × (κ → ℝ) → ℝ := fun xs => objective xs.1
  slackNonneg : (E × (κ → ℝ)) → κ → Prop := fun xs j => 0 ≤ xs.2 j

def NonlinearProgramWithSlackReformulation.isFeasible
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    (P : NonlinearProgramWithSlackReformulation E ι κ) (x : E) : Prop :=
  (∀ i : ι, P.eqConstr i x = 0) ∧ ∀ j : κ, 0 ≤ P.ineqConstr j x

def NonlinearProgramWithSlackReformulation.slackFeasible
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    (P : NonlinearProgramWithSlackReformulation E ι κ) (xs : E × (κ → ℝ)) : Prop :=
  (∀ i : ι, P.eqConstr i xs.1 = 0) ∧
    SlackVariableReformulation P.ineqConstr xs

/-
Exercise 19.1 - (c)

Let nonlinear program and slack reformulation.

Suppose x ∈ ℝ^n is feasible for the first problem, and define s = cᵢ(x) ∈ ℝ^{mᵢ}, so that (x, s) is
feasible for the slack - variable problem.

For a feasible point of a nonlinear program, LICQ holds if the gradients of all equality constraints
and of all active inequality constraints are linearly independent. An inequality constraint is
active at a feasible point if it is satisfied with equality. For the first problem, the active set
at x is A(x) = {j ∈ {1, …, mᵢ}: (cᵢ(x))_j = 0}, and LICQ at x means that {∇(c_e)_1(x), …,
∇(c_e)_{m_e}(x), ∇(cᵢ)_j(x) (j ∈ A(x))} is a linearly independent family ∈ ℝ^n. For the
slack - variable problem, the inequality constraints are sⱼ ≥ 0, j = 1, …, mᵢ, and the active set at
(x, s) is A(x, s) = {j ∈ {1, …, mᵢ}: sⱼ = 0}.

Show that LICQ holds at x for min f(x) subject to c_e(x) = 0, cᵢ(x) ≥ 0,

if and only if LICQ holds at (x, s) for min_{x, s} f(x) subject to c_e(x) = 0, cᵢ(x) - s = 0, s ≥ 0.
-/
theorem licq_iff_licq_slack_reformulation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    [hProdNormed : NormedAddCommGroup (E × (κ → ℝ))]
    [hProdInner : InnerProductSpace ℝ (E × (κ → ℝ))]
    (hProdComplete : @CompleteSpace (E × (κ → ℝ))
      (PseudoMetricSpace.toUniformSpace (α := E × (κ → ℝ))))
    (P : NonlinearProgramWithSlackReformulation E ι κ)
    (x : E)
    (s : κ → ℝ)
    (hx : P.isFeasible x)
    (hs : s = fun j => P.ineqConstr j x)
    (hxs : P.slackFeasible (x, s)) :
    LinearIndependenceConstraintQualification P.eqConstr P.ineqConstr x ↔
      @LinearIndependenceConstraintQualification
        (E × (κ → ℝ)) hProdNormed hProdInner hProdComplete (Sum ι κ) κ
        (fun ij : Sum ι κ => fun z : E × (κ → ℝ) =>
          Sum.elim
            (fun i => P.eqConstr i z.1)
            (fun j => P.slackEqConstr z j)
            ij)
        (fun j : κ => fun z : E × (κ → ℝ) => z.2 j)
        (x, s) := by
  sorry

end «problem-131»