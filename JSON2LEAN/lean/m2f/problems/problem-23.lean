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
  let S : Set ℝ := {r : ℝ | ∃ d : Fin n → ℝ, P.norm d ≤ 1 ∧ r = ∑ i, P.gradient i * d i}
  -- Negating a feasible direction stays in the unit ball because the norm is absolutely homogeneous.
  have hfeasible_neg : ∀ d : Fin n → ℝ, P.isFeasible d → P.isFeasible (-d) := by
    intro d hd
    calc
      P.norm (-d) = |(-1 : ℝ)| * P.norm d := by
        simpa using P.norm_smul (-1) d
      _ = P.norm d := by norm_num
      _ ≤ 1 := hd
  -- The objective is linear, so negating the direction flips the sign of the value.
  have hobjective_neg : ∀ d : Fin n → ℝ, P.objective (-d) = -P.objective d := by
    intro d
    simp [NormalizedSteepestDescentSubproblem.objective]
  -- Optimality at `-d` bounds every attainable objective value by `-P.optimalValue`.
  have hupper : ∀ r ∈ S, r ≤ -P.optimalValue := by
    intro r hr
    rcases hr with ⟨d, hd, rfl⟩
    have hstep_le := hstep_optimal.2 (-d) (hfeasible_neg d hd)
    rw [hobjective_neg] at hstep_le
    have hstep_le' : P.optimalValue ≤ -P.objective d := by
      simpa [NormalizedSteepestDescentSubproblem.optimalValue] using hstep_le
    have hbound : P.objective d ≤ -P.optimalValue := by
      simpa using (neg_le_neg hstep_le')
    simpa [NormalizedSteepestDescentSubproblem.objective] using hbound
  have hS_bddAbove : BddAbove S := by
    refine ⟨-P.optimalValue, ?_⟩
    intro r hr
    exact hupper r hr
  -- The value `-P.optimalValue` is attained by the feasible direction `-P.step`.
  have hneg_optimal_mem : -P.optimalValue ∈ S := by
    refine ⟨-P.step, hfeasible_neg P.step hstep_optimal.1, ?_⟩
    calc
      -P.optimalValue = P.objective (-P.step) := by
        rw [hobjective_neg, NormalizedSteepestDescentSubproblem.optimalValue]
      _ = ∑ i, P.gradient i * (-P.step i) := rfl
  have hS_nonempty : S.Nonempty := ⟨-P.optimalValue, hneg_optimal_mem⟩
  -- The supremum is exactly the attained upper bound, hence the optimal value is its negative.
  have hdual_eq : dualNorm P.norm P.gradient = -P.optimalValue := by
    unfold dualNorm
    change sSup S = -P.optimalValue
    exact le_antisymm (csSup_le hS_nonempty hupper) (le_csSup hS_bddAbove hneg_optimal_mem)
  have hoptimal_eq : P.optimalValue = -dualNorm P.norm P.gradient := by
    linarith
  constructor
  · exact hoptimal_eq
  · -- Rewrite the scaled step, factor out the dual norm, and substitute the first identity.
    rw [hΔx_sd]
    calc
      ∑ i, P.gradient i * (dualNorm P.norm P.gradient * P.step i)
          = ∑ i, dualNorm P.norm P.gradient * (P.gradient i * P.step i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = dualNorm P.norm P.gradient * ∑ i, P.gradient i * P.step i := by
            rw [← Finset.mul_sum]
      _ = dualNorm P.norm P.gradient * P.optimalValue := by
            rfl
      _ = -(dualNorm P.norm P.gradient) ^ 2 := by
            rw [hoptimal_eq]
            ring

end «problem-23»
