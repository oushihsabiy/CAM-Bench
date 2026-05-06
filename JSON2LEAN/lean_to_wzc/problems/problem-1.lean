import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-1»

/-
For an inequality constraint of the form h(x) ≤ 0, a Lagrange multiplier is a scalar λ ∈ ℝ_+ such
that the associated Lagrangian is L(x, λ) = f(x) + λ h(x).

The dual function for this problem can be unbounded below, so the Lagrangian and dual function are
modeled in `EReal`, not `ℝ`.
-/
def lagrangianWithIneqMultiplier {α : Type*} (f h : α → ℝ) : α → NNReal → EReal :=
  fun x lam => ((f x + (lam : ℝ) * h x : ℝ) : EReal)

/-
Given a Lagrangian L(x, λ), the Lagrangian dual function is g(λ) = inf_x L(x, λ).
-/
def lagrangianDualFunction {α : Type*} (L : α → NNReal → EReal) : NNReal → EReal :=
  fun lam => sInf (Set.range (fun x : α => L x lam))

/-
The Lagrangian dual problem is the optimization problem sup_{λ ≥ 0} g(λ).
-/
def lagrangianDualProblem {α : Type*} (L : α → NNReal → EReal) : EReal :=
  sSup (Set.range (fun lam : NNReal => lagrangianDualFunction L lam))

/-
For primal optimal value p* and dual optimal value d*, the duality gap is p* - d*.
-/
def dualityGap (pStar dStar : EReal) : EReal := pStar - dStar

/-
The optimal value of an optimization problem is the infimum of its objective over the feasible set.
-/
def optimalValue {α : Type*} (feasibleSet : Set α) (f : α → ℝ) : EReal :=
  sInf ((fun x : α => (f x : EReal)) '' feasibleSet)

/-
Consider the optimization problem (P) min_{x, y ∈ ℝ} e^x + e^y subject to

  x^2 / y ≤ 0,

where the quotient is defined in the usual sense, so y ≠ 0. Hence the feasible set is

  {(x, y) ∈ ℝ^2 | y ≠ 0 ∧ x^2 / y ≤ 0}.

All ingredients of this concrete problem are defined explicitly below.
-/
def nonlinearProgramPObjective : ℝ × ℝ → ℝ :=
  fun p => Real.exp p.1 + Real.exp p.2

def nonlinearProgramPConstraint : ℝ × ℝ → ℝ :=
  fun p => p.1 ^ 2 / p.2

def nonlinearProgramPFeasibleSet : Set (ℝ × ℝ) :=
  {p | p.2 ≠ 0 ∧ nonlinearProgramPConstraint p ≤ 0}

def nonlinearProgramPPrimalOptimalValue : EReal :=
  optimalValue nonlinearProgramPFeasibleSet nonlinearProgramPObjective

/-
The Lagrangian is evaluated only on points with y ≠ 0.
-/
def nonlinearProgramPDualDomain : Type :=
  {p : ℝ × ℝ // p.2 ≠ 0}

def nonlinearProgramPLagrangian : nonlinearProgramPDualDomain → NNReal → EReal :=
  fun p lam =>
    ((
      Real.exp p.1.1 + Real.exp p.1.2 +
        (lam : ℝ) * (p.1.1 ^ 2 / p.1.2) : ℝ
    ) : EReal)

def nonlinearProgramPDualFunction : NNReal → EReal :=
  lagrangianDualFunction nonlinearProgramPLagrangian

def nonlinearProgramPDualOptimalValue : EReal :=
  lagrangianDualProblem nonlinearProgramPLagrangian

def nonlinearProgramPDualityGap : EReal :=
  dualityGap nonlinearProgramPPrimalOptimalValue nonlinearProgramPDualOptimalValue

/-
Write down the Lagrangian dual problem of (P).
-/
theorem nonlinearProgramP_lagrangian_dual_problem :
    nonlinearProgramPDualOptimalValue =
    sSup
      (Set.range (fun lam : NNReal =>
        sInf
          (Set.range (fun p : nonlinearProgramPDualDomain =>
            ((
              Real.exp p.1.1 + Real.exp p.1.2 +
                (lam : ℝ) * (p.1.1 ^ 2 / p.1.2) : ℝ
            ) : EReal))))) := by
  sorry

/-
At λ = 0, the dual function is the infimum of e^x + e^y over y ≠ 0, which is 0.
-/
theorem nonlinearProgramP_dual_function_eq_zero_at_zero :
    nonlinearProgramPDualFunction 0 = ((0 : ℝ) : EReal) := by
  sorry

/-
For every positive multiplier λ, the Lagrangian is unbounded below by taking y → 0- with x ≠ 0.
Thus the dual function is -∞, represented by `⊥ : EReal`.
-/
theorem nonlinearProgramP_dual_function_eq_bot_of_pos
    (lam : NNReal) (h_lam : 0 < lam) :
    nonlinearProgramPDualFunction lam = (⊥ : EReal) := by
  sorry

/-
The dual optimal value is the supremum of the dual function over λ ≥ 0. Since g(0) = 0 and
g(λ) = -∞ for λ > 0, the dual optimal value is 0.
-/
theorem nonlinearProgramP_dual_optimal_value_eq_zero :
    nonlinearProgramPDualOptimalValue = ((0 : ℝ) : EReal) := by
  sorry

/-
The primal optimal value is also 0: feasible points with x, y → -∞ make e^x + e^y approach 0.
Therefore the duality gap is 0.
-/
theorem nonlinearProgramP_primal_optimal_value_eq_zero_and_duality_gap_eq_zero :
    nonlinearProgramPPrimalOptimalValue = ((0 : ℝ) : EReal) ∧
      nonlinearProgramPDualityGap = ((0 : ℝ) : EReal) := by
  sorry

end «problem-1»
