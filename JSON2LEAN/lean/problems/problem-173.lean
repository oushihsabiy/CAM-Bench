import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-173»
/-
Given an objective function f and constraint functions c_i with multipliers λ_i, the Lagrangian is
the function L(x, λ) = f(x) - ∑_i λ_i c_i(x).
-/
def Lagrangian {E ι : Type*} [Fintype ι] (f : E → ℝ) (c : ι → E → ℝ) (x : E) (lam : ι → ℝ) : ℝ :=
  f x - ∑ i, lam i * c i x

/-
For a differentiable nonlinear program with equality constraints c_i(x) = 0 for i∈ mathcal E and
inequality constraints c_i(x) ge 0 for i∈ I, the Karush - - Kuhn - - Tucker conditions at (x^*,
λ^*) are: stationarity, ∇_x L(x^*, λ^*) = 0; primal feasibility, c_i(x^*) = 0 for i∈ mathcal E and
c_i(x^*) ge 0 for i∈ I}; dual feasibility, λ_i^* ge 0 for i∈ I; and complementary
slackness, λ_i^* c_i(x^*) = 0 for i∈ I.
-/
def LICQ
    {E ι : Type*}
    [AddCommMonoid E]
    [Module ℝ E]
    [Fintype ι]
    (Eeq Ineq : Set ι)
    (cgrad : ι → E → E)
    (c : ι → E → ℝ)
    (x : E) : Prop :=
  LinearIndependent ℝ (fun i : {i // i ∈ Eeq ∪ {j | j ∈ Ineq ∧ c j x = 0}} => cgrad i.1 x)

/-
For inequality constraints indexed by I, the active set at a point x^* is mathcal A(x^*) =
{i∈ I: c_i(x^*) = 0}.
-/
def Stationarity
    {E ι : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [Fintype ι]
    (f : E → ℝ)
    (c : ι → E → ℝ)
    (x : E)
    (lam : ι → ℝ) : Prop :=
  gradient f x - ∑ i : ι, (lam i) • gradient (c i) x = 0

/-
A point x^* is primal feasible if it satisfies all constraints: c_i(x^*) = 0 for all equality
constraints and c_i(x^*) ge 0 for all inequality constraints.
-/
def PrimalFeasible
    {E ι : Type*}
    (Eeq Ineq : Set ι)
    (c : ι → E → ℝ)
    (x : E) : Prop :=
  (∀ i ∈ Eeq, c i x = 0) ∧
  (∀ i ∈ Ineq, c i x ≥ 0)

/-
For multipliers associated with inequality constraints, dual feasibility means that λ_i^* ge 0 for
every i∈ I.
-/
def DualFeasible
    {ι : Type*}
    (Ineq : Set ι)
    (lam : ι → ℝ) : Prop :=
  ∀ i ∈ Ineq, lam i ≥ 0

/-
Complementary slackness holds for inequality constraints if λ_i^* c_i(x^*) = 0 for every i∈ mathcal
I.
-/
def ComplementarySlackness
    {E ι : Type*}
    (Ineq : Set ι)
    (c : ι → E → ℝ)
    (x : E)
    (lam : ι → ℝ) : Prop :=
  ∀ i ∈ Ineq, lam i * c i x = 0

/-
Multipliers outside the equality and inequality index sets are not part of the optimization
problem, so they are normalized to zero when the ambient index type contains extra labels.
-/
def ZeroOffConstraintSet
    {ι : Type*}
    (Eeq Ineq : Set ι)
    (lam : ι → ℝ) : Prop :=
  ∀ i : ι, i ∉ Eeq ∪ Ineq → lam i = 0

/-
A Lagrange multiplier is a scalar coefficient associated with a constraint in the Lagrangian; a
vector λ is a multiplier vector at x^* if it satisfies the relevant optimality conditions together
with x^*.
-/
def MultiplierVector
    {E ι : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (Eeq Ineq : Set ι)
    (f : E → ℝ)
    (c : ι → E → ℝ)
    (x : E)
    (lam : ι → ℝ) : Prop :=
  DifferentiableAt ℝ f x ∧
  (∀ i : ι, i ∈ Eeq ∪ Ineq → DifferentiableAt ℝ (c i) x) ∧
  Stationarity f c x lam ∧
  PrimalFeasible Eeq Ineq c x ∧
  DualFeasible Ineq lam ∧
  ComplementarySlackness Ineq c x lam ∧
  ZeroOffConstraintSet Eeq Ineq lam

/-
Let f: mathbf{R}^n to mathbf{R} and c_i: mathbf{R}^n to mathbf{R} for i ∈ mathcal{E} ∪ mathcal{I} be
differentiable, where mathcal{E} and mathcal{I} are the index sets of equality and inequality
constraints. Define L(x, λ) = f(x) - ∑_i∈ mathcal{E∪ mathcal{I}} λ_i c_i(x). Assume x^* ∈
mathbf{R}^n
and λ^* = (λ_i^*)_i∈ mathcal{E∪ mathcal{I}} satisfy ∇_x L(x^*, λ^*) = ∇ f(x^*) - ∑_i∈ mathcal{E∪
mathcal{I}} λ_i^* ∇ c_i(x^*) = 0, c_i(x^*) = 0 text{for all} i∈ mathcal{E}, c_i(x^*) ge 0 text{for
all} i∈ mathcal{I}, λ_i^* ge 0 text{for all} i∈ mathcal{I}, λ_i^* c_i(x^*) = 0 text{for all} i∈
mathcal{I}. Let mathcal{A}(x^*) = {, i∈ mathcal{I}: c_i(x^*) = 0,}. Assume that LICQ holds at x^*,
meaning that the set {∇ c_i(x^*): i∈ mathcal{E}∪ mathcal{A}(x^*)} is linearly independent. Prove
that the Lagrange multiplier λ^* appearing in the KKT conditions is unique.
-/
theorem kkt_multiplier_unique_under_LICQ
    {E ι : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [Fintype ι]
    (Eeq Ineq : Set ι)
    (f : E → ℝ)
    (c : ι → E → ℝ)
    (x : E)
    (lamStar : ι → ℝ)
    (hdisjoint : Disjoint Eeq Ineq)
    (hKKTStar : MultiplierVector Eeq Ineq f c x lamStar)
    (hLICQ : LICQ Eeq Ineq (fun i y => gradient (c i) y) c x)
    : (∀ i : ι, i ∈ Ineq → c i x ≠ 0 → lamStar i = 0) ∧
      (∀ i : ι, i ∉ Eeq ∪ Ineq → lamStar i = 0) ∧
      ∀ lam : ι → ℝ,
        MultiplierVector Eeq Ineq f c x lam →
        lam = lamStar := by
  sorry

end «problem-173»
