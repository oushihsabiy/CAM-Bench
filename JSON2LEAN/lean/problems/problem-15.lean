import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-15»
/-
For a convex optimization problem with inequality constraints fᵢ(x) ≤ q 0, Slater's condition holds
if there exists x∈ℝ^n such that fᵢ(x) < 0 for all i = 1, ..., m.
-/
def StrongDuality (pStar dStar : ℝ) : Prop :=
  pStar = dStar

/-
Let f₀, f₁, ..., fₘ: ℝ^n→ℝ be convex functions. Consider the optimization problem minimize & f₀(x);
subject to & fᵢ(x) ≤ 0, i = 1, ..., m, array with variable x∈ℝ^n.
-/
structure ConvexPrimalProblem (n m : ℕ) where
  objective : (Fin n → ℝ) → ℝ
  constraints : Fin m → (Fin n → ℝ) → ℝ

def ConvexPrimalProblem.isFeasible {n m : ℕ} (P : ConvexPrimalProblem n m) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin m, P.constraints i x ≤ 0

def ConvexPrimalProblem.objectiveValue {n m : ℕ} (P : ConvexPrimalProblem n m) (x : Fin n → ℝ) : ℝ :=
  P.objective x

def ConvexPrimalProblem.dualFunction {n m : ℕ} (P : ConvexPrimalProblem n m) (lam : Fin m → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x : Fin n → ℝ, r = P.objective x + ∑ i : Fin m, lam i * P.constraints i x}

def ConvexPrimalProblem.satisfiesSlater {n m : ℕ} (P : ConvexPrimalProblem n m) : Prop :=
  ∃ x : Fin n → ℝ, ∀ i : Fin m, P.constraints i x < 0

/-
The dual problem is maximize & g(λ); subject to & λ succeq 0, array where λ∈ℝ^m, λ_i ≥ 0 for i =
1, ..., m, and g is the dual function associated with the primal problem.
-/
structure LagrangeDualProblem (n m : ℕ) where
  primal : ConvexPrimalProblem n m

def LagrangeDualProblem.isFeasible {n m : ℕ} (_D : LagrangeDualProblem n m) (lam : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, 0 ≤ lam i

def LagrangeDualProblem.objectiveValue {n m : ℕ} (D : LagrangeDualProblem n m) (lam : Fin m → ℝ) : ℝ :=
  D.primal.dualFunction lam

def LagrangeDualProblem.dualFunction {n m : ℕ} (D : LagrangeDualProblem n m) (lam : Fin m → ℝ) : ℝ :=
  D.primal.dualFunction lam

/-
For a fixed t > 0, consider the unconstrained optimization problem minimize f₀(x) + tmax_i = 1, ...,
m
fᵢ(x)^ +, where fᵢ(x)^ + = fᵢ(x), 0 for i = 1, ..., m.
-/
structure ExactPenaltyProblem (n m : ℕ) where
  primal : ConvexPrimalProblem n m
  t : ℝ
  t_pos : 0 < t

def ExactPenaltyProblem.positivePart (P : ExactPenaltyProblem n m) (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  max (P.primal.constraints i x) 0

def ExactPenaltyProblem.penaltyTerm (P : ExactPenaltyProblem n m) (x : Fin n → ℝ) : ℝ :=
  sSup ((fun i : Fin m => P.positivePart i x) '' Set.univ)

def ExactPenaltyProblem.objectiveValue (P : ExactPenaltyProblem n m) (x : Fin n → ℝ) : ℝ :=
  P.primal.objective x + P.t * P.penaltyTerm x

/-
Consider the convex primal problem and its Lagrange dual problem. Assume Slater's condition holds,
strong duality holds, the dual optimum is attained, and the dual optimal solution is unique; denote
it by λ^star. For a fixed t > 0, consider the exact penalty problem. Show that the objective
function in this problem is convex.
-/
theorem exactPenaltyProblem_objective_convex
    {n m : ℕ} (P : ExactPenaltyProblem n m)
    (hobjective_convex : ConvexOn ℝ Set.univ P.primal.objective)
    (hconstraints_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (P.primal.constraints i)) :
    ConvexOn ℝ Set.univ P.objectiveValue := by
  sorry

end «problem-15»
