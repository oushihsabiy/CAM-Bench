import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-23»
/-
Given a norm ‖·‖ on ℝ^n, its dual norm is defined by ‖g‖_*: = sup{gᵀ d: ‖d‖ ≤ 1} for g ∈ ℝ^n.
-/
def dualNorm {n : ℕ} (norm : (Fin n → ℝ) → ℝ) (g : Fin n → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ d : Fin n → ℝ, norm d ≤ 1 ∧ r = ∑ i, g i * d i}

/-
Let Δ x_{nsd} be any solution of min_{‖d‖ ≤ 1} ∇ f(x)ᵀ d.
-/
structure NormalizedSteepestDescentSubproblem (n : ℕ) where
  norm : (Fin n → ℝ) → ℝ
  norm_nonneg : ∀ d : Fin n → ℝ, 0 ≤ norm d
  norm_eq_zero_iff : ∀ d : Fin n → ℝ, norm d = 0 ↔ d = 0
  norm_smul : ∀ (a : ℝ) (d : Fin n → ℝ), norm (a • d) = |a| * norm d
  norm_add_le : ∀ d e : Fin n → ℝ, norm (d + e) ≤ norm d + norm e
  gradient : Fin n → ℝ
  step : Fin n → ℝ

def NormalizedSteepestDescentSubproblem.isFeasible
    {n : ℕ} (P : NormalizedSteepestDescentSubproblem n) (d : Fin n → ℝ) : Prop :=
  P.norm d ≤ 1

def NormalizedSteepestDescentSubproblem.objective
    {n : ℕ} (P : NormalizedSteepestDescentSubproblem n) (d : Fin n → ℝ) : ℝ :=
  ∑ i, P.gradient i * d i

def NormalizedSteepestDescentSubproblem.optimalValue
    {n : ℕ} (P : NormalizedSteepestDescentSubproblem n) : ℝ :=
  P.objective P.step

def NormalizedSteepestDescentSubproblem.IsOptimalStep
    {n : ℕ} (P : NormalizedSteepestDescentSubproblem n) (d : Fin n → ℝ) : Prop :=
  P.isFeasible d ∧ ∀ d' : Fin n → ℝ, P.isFeasible d' → P.objective d ≤ P.objective d'

theorem gradient_dot_scaled_normalized_steepest_descent_eq_neg_dualNorm_sq
    {n : ℕ} (P : NormalizedSteepestDescentSubproblem n)
    (hunitBall_nonempty : ∃ d : Fin n → ℝ, P.isFeasible d)
    (hstep_optimal : P.IsOptimalStep P.step)
    (Δx_sd : Fin n → ℝ)
    (hΔx_sd : Δx_sd = fun i => dualNorm P.norm P.gradient * P.step i) :
    P.optimalValue = -dualNorm P.norm P.gradient ∧
      ∑ i, P.gradient i * Δx_sd i = -(dualNorm P.norm P.gradient) ^ 2 := by
  sorry

end «problem-23»
