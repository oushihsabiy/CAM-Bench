import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-3»
/-
Let A ∈ ℝ^{m × n} have rows a_1ᵀ, ..., a_mᵀ, let b ∈ ℝ^m, c ∈ ℝ^n, and let μ > 0. Consider the
convex
optimization problem min_{x ∈ ℝ^n} (cᵀ x + (1)/(μ) \sum_{i = 1}^m log(1 + e^{μ(a_iᵀ x - bᵢ)})).
-/
structure ConvexLogisticProgram where
  m : ℕ
  n : ℕ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ
  μ : ℝ
  μ_pos : 0 < μ

def ConvexLogisticProgram.rowDot (P : ConvexLogisticProgram) (i : Fin P.m) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.A i j * x j

def ConvexLogisticProgram.objective (P : ConvexLogisticProgram) (x : Fin P.n → ℝ) : ℝ :=
  (∑ j : Fin P.n, P.c j * x j) +
    (1 / P.μ) * ∑ i : Fin P.m, Real.log (1 + Real.exp (P.μ * (P.rowDot i x - P.b i)))

def ConvexLogisticProgram.optimalValue (P : ConvexLogisticProgram) : EReal :=
  sInf ((fun x : Fin P.n → ℝ => (P.objective x : EReal)) '' Set.univ)

/-
Consider the following primal - dual pair of linear programs: primal: & min cᵀ x; & subject to Ax ≤
b,
dual: & max - bᵀ z; & subject to Aᵀ z + c = 0,; & z ≥ 0.
-/
structure PrimalDualLinearProgram where
  m : ℕ
  n : ℕ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ

def PrimalDualLinearProgram.primalFeasible (P : PrimalDualLinearProgram) (x : Fin P.n → ℝ) : Prop :=
  ∀ i : Fin P.m, (∑ j : Fin P.n, P.A i j * x j) ≤ P.b i

def PrimalDualLinearProgram.primalObjective (P : PrimalDualLinearProgram) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.c j * x j

def PrimalDualLinearProgram.dualFeasible (P : PrimalDualLinearProgram) (z : Fin P.m → ℝ) : Prop :=
  (∀ j : Fin P.n, (∑ i : Fin P.m, P.A i j * z i) + P.c j = 0) ∧
    ∀ i : Fin P.m, 0 ≤ z i

def PrimalDualLinearProgram.dualObjective (P : PrimalDualLinearProgram) (z : Fin P.m → ℝ) : ℝ :=
  -∑ i : Fin P.m, P.b i * z i

def PrimalDualLinearProgram.primalOptimalValue (P : PrimalDualLinearProgram) : EReal :=
  sInf ((fun x : Fin P.n → ℝ => (P.primalObjective x : EReal)) '' {x | P.primalFeasible x})

def PrimalDualLinearProgram.dualOptimalValue (P : PrimalDualLinearProgram) : EReal :=
  sSup ((fun z : Fin P.m → ℝ => (P.dualObjective z : EReal)) '' {z | P.dualFeasible z})

/-
Consider the convex logistic program. Let q^star be its optimal value. Consider also the primal -
dual
linear programs. Assume the primal linear program is feasible, these linear programs have finite
optimal value p^star, and that there exists a dual optimal solution z^star ∈ ℝ^m such that
z^star ≤ 1, where all inequalities are componentwise and 1 ∈ ℝ^m is the all - ones vector. Show that
p^star ≤ q^star ≤ p^star + \frac{m log 2}{μ}.
-/
theorem primal_dual_linear_program_optimalValue_le_convexLogisticProgram_optimalValue_le
    (P : PrimalDualLinearProgram)
    (Q : ConvexLogisticProgram)
    (hm : Q.m = P.m)
    (hn : Q.n = P.n)
    (hA : ∀ i : Fin P.m, ∀ j : Fin P.n, Q.A (Fin.cast hm.symm i) (Fin.cast hn.symm j) = P.A i j)
    (hb : ∀ i : Fin P.m, Q.b (Fin.cast hm.symm i) = P.b i)
    (hc : ∀ j : Fin P.n, Q.c (Fin.cast hn.symm j) = P.c j)
    (pStar : ℝ)
    (h_primal_feasible : ∃ x : Fin P.n → ℝ, P.primalFeasible x)
    (hp_primal : P.primalOptimalValue = (pStar : EReal))
    (hp_dual : P.dualOptimalValue = (pStar : EReal))
    (hz_exists : ∃ zStar : Fin P.m → ℝ,
      (P.dualFeasible zStar ∧ P.dualObjective zStar = pStar) ∧
      (∀ i : Fin P.m, zStar i ≤ 1)) :
    (pStar : EReal) ≤ Q.optimalValue ∧
      Q.optimalValue ≤ ((pStar + (P.m : ℝ) * Real.log 2 / Q.μ : ℝ) : EReal) := by
  sorry

end «problem-3»
