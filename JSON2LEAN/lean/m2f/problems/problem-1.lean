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
  -- Unfold the named dual optimal value and the two dual constructions to expose the `sSup`/`sInf`
  -- formula appearing on the right-hand side.
  unfold nonlinearProgramPDualOptimalValue lagrangianDualProblem lagrangianDualFunction
  -- Unfold the concrete Lagrangian; the resulting expression is definitionally the target formula.
  unfold nonlinearProgramPLagrangian
  rfl

/-
At λ = 0, the dual function is the infimum of e^x + e^y over y ≠ 0, which is 0.
-/
/-- The explicit witness coordinate `-((n : ℝ) + 1)` is never zero. -/
lemma nonlinearProgramP_zeroWitness_nonzero (n : ℕ) : (-((n : ℝ) + 1) : ℝ) ≠ 0 := by
  -- The witness coordinate is strictly negative, so it cannot vanish.
  linarith [show (0 : ℝ) < (n : ℝ) + 1 by positivity]

/-- At multiplier zero, every Lagrangian value is nonnegative. -/
lemma nonlinearProgramP_zeroMultiplier_value_nonneg (p : nonlinearProgramPDualDomain) :
    (0 : EReal) ≤ nonlinearProgramPLagrangian p 0 := by
  -- Setting `lam = 0` removes the constraint term, leaving only positive exponentials.
  have h_nonneg : (0 : ℝ) ≤ Real.exp p.1.1 + Real.exp p.1.2 := by
    positivity
  simpa only [nonlinearProgramPLagrangian, NNReal.coe_zero, zero_mul, add_zero] using
    (show (0 : EReal) ≤ ((Real.exp p.1.1 + Real.exp p.1.2 : ℝ) : EReal) by
      exact_mod_cast h_nonneg)

/-- The explicit witness family has a closed-form value when the multiplier is zero. -/
lemma nonlinearProgramP_zeroWitness_value (n : ℕ) :
    nonlinearProgramPLagrangian
        ⟨(-((n : ℝ) + 1), -((n : ℝ) + 1)), nonlinearProgramP_zeroWitness_nonzero n⟩ 0 =
      (((2 : ℝ) * Real.exp (-((n : ℝ) + 1)) : ℝ) : EReal) := by
  -- Route correction: evaluate at `lam = 0` first so the quotient term disappears.
  simp only [nonlinearProgramPLagrangian, NNReal.coe_zero, zero_mul, add_zero]
  ring_nf

/-- The explicit witness values converge to `0` in `EReal`. -/
lemma nonlinearProgramP_zeroWitness_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ => (((2 : ℝ) * Real.exp (-((n : ℝ) + 1)) : ℝ) : EReal))
      Filter.atTop (𝓝 0) := by
  -- First send the exponent to `atBot`.
  have h_shiftReal : Filter.Tendsto (fun x : ℝ => x + 1) Filter.atTop Filter.atTop :=
    le_of_eq (Filter.map_add_atTop_eq (α := ℝ) 1)
  have h_exp_arg : Filter.Tendsto (fun n : ℕ => (-((n : ℝ) + 1) : ℝ)) Filter.atTop
      Filter.atBot := by
    have h_shiftNat : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1 : ℝ)) Filter.atTop
        Filter.atTop :=
      h_shiftReal.comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, neg_add, add_comm, add_left_comm, add_assoc] using
      tendsto_neg_atTop_atBot.comp h_shiftNat
  -- Then compose with `exp`, scale by `2`, and coerce into `EReal`.
  have h_real : Filter.Tendsto
      (fun n : ℕ => (2 : ℝ) * Real.exp (-((n : ℝ) + 1)))
      Filter.atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp h_exp_arg).const_mul (2 : ℝ)
  have h_coe : Filter.Tendsto (fun x : ℝ => (x : EReal)) (𝓝 (0 : ℝ))
      (𝓝 ((0 : ℝ) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto
  exact h_coe.comp h_real

theorem nonlinearProgramP_dual_function_eq_zero_at_zero :
    nonlinearProgramPDualFunction 0 = ((0 : ℝ) : EReal) := by
  -- Unfold the dual function so the goal becomes an infimum over zero-multiplier values.
  unfold nonlinearProgramPDualFunction lagrangianDualFunction
  refine sInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_
  · -- Every value in the range is nonnegative, so `0` is a lower bound.
    rintro _ ⟨p, rfl⟩
    exact nonlinearProgramP_zeroMultiplier_value_nonneg p
  · -- The witness sequence gets below any target level `w > 0`.
    intro w hw
    have h_eventually : ∀ᶠ n : ℕ in Filter.atTop,
        (((2 : ℝ) * Real.exp (-((n : ℝ) + 1)) : ℝ) : EReal) < w := by
      exact nonlinearProgramP_zeroWitness_tendsto_zero.eventually (Iio_mem_nhds hw)
    rcases h_eventually.exists with ⟨n, hn⟩
    refine ⟨nonlinearProgramPLagrangian
        ⟨(-((n : ℝ) + 1), -((n : ℝ) + 1)), nonlinearProgramP_zeroWitness_nonzero n⟩ 0,
      ?_, ?_⟩
    · exact ⟨⟨(-((n : ℝ) + 1), -((n : ℝ) + 1)), nonlinearProgramP_zeroWitness_nonzero n⟩, rfl⟩
    · rw [nonlinearProgramP_zeroWitness_value n]
      simpa [neg_add, add_comm, add_left_comm, add_assoc] using hn

/-
For every positive multiplier λ, the Lagrangian is unbounded below by taking y → 0- with x ≠ 0.
Thus the dual function is -∞, represented by `⊥ : EReal`.
-/
/-- The negative reciprocal witness used for positive multipliers is never zero. -/
lemma nonlinearProgramP_posMultiplierWitness_nonzero (n : ℕ) :
    (-(1 / ((n : ℝ) + 1)) : ℝ) ≠ 0 := by
  -- The reciprocal is nonzero because the denominator is strictly positive.
  have hnonzero : (1 / ((n : ℝ) + 1) : ℝ) ≠ 0 := by
    positivity
  exact neg_ne_zero.mpr hnonzero

/-- Evaluating the Lagrangian on the positive-multiplier witness exposes a linear `-(n + 1)` term. -/
lemma nonlinearProgramP_posMultiplierWitness_value (lam : NNReal) (n : ℕ) :
    nonlinearProgramPLagrangian
        ⟨(1, -(1 / ((n : ℝ) + 1))), nonlinearProgramP_posMultiplierWitness_nonzero n⟩ lam =
      (((Real.exp 1 + Real.exp (-(1 / ((n : ℝ) + 1))) -
          (lam : ℝ) * ((n : ℝ) + 1) : ℝ)) : EReal) := by
  -- Simplify the quotient term `1 / (-(1 / (n + 1)))` to `-(n + 1)`.
  have hden : ((n : ℝ) + 1 : ℝ) ≠ 0 := by
    positivity
  have hquot :
      ((lam : ℝ) * (1 ^ 2 / (-(1 / ((n : ℝ) + 1))) : ℝ)) =
        -(lam : ℝ) * ((n : ℝ) + 1) := by
    field_simp [hden]
  -- Rewriting the Lagrangian with the simplified quotient gives the claimed closed form.
  change (((Real.exp 1 + Real.exp (-(1 / ((n : ℝ) + 1))) +
      (lam : ℝ) * (1 ^ 2 / (-(1 / ((n : ℝ) + 1))) : ℝ) : ℝ)) : EReal) = _
  rw [hquot]
  ring_nf

/-- The witness value is bounded above by replacing the second exponential with `1`. -/
lemma nonlinearProgramP_posMultiplierWitness_upper_bound (lam : NNReal) (n : ℕ) :
    nonlinearProgramPLagrangian
        ⟨(1, -(1 / ((n : ℝ) + 1))), nonlinearProgramP_posMultiplierWitness_nonzero n⟩ lam ≤
      ((((Real.exp 1 + 1) - (lam : ℝ) * ((n : ℝ) + 1) : ℝ)) : EReal) := by
  -- First rewrite to the explicit witness value.
  rw [nonlinearProgramP_posMultiplierWitness_value]
  -- The exponent is nonpositive, so its exponential is at most `1`.
  have hle_arg : (-(1 / ((n : ℝ) + 1)) : ℝ) ≤ 0 := by
    have hnonneg : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
      positivity
    linarith
  have h_exp : Real.exp (-(1 / ((n : ℝ) + 1))) ≤ 1 := by
    simpa using (Real.exp_le_one_iff.mpr hle_arg)
  -- Substitute the exponential bound into the closed-form expression.
  exact_mod_cast (show
    Real.exp 1 + Real.exp (-(1 / ((n : ℝ) + 1))) - (lam : ℝ) * ((n : ℝ) + 1) ≤
      (Real.exp 1 + 1) - (lam : ℝ) * ((n : ℝ) + 1) by
    linarith)

theorem nonlinearProgramP_dual_function_eq_bot_of_pos
    (lam : NNReal) (h_lam : 0 < lam) :
    nonlinearProgramPDualFunction lam = (⊥ : EReal) := by
  -- Unfold the dual function and characterize `⊥` via witnesses below every larger bound.
  unfold nonlinearProgramPDualFunction lagrangianDualFunction
  refine sInf_eq_bot.mpr ?_
  intro b hb
  by_cases h_top : b = ⊤
  · -- If the comparison bound is `⊤`, any finite witness value is enough.
    refine ⟨nonlinearProgramPLagrangian
        ⟨(1, -(1 / ((((0 : ℕ) : ℝ)) + 1))), nonlinearProgramP_posMultiplierWitness_nonzero 0⟩
          lam, ?_, ?_⟩
    · exact
        ⟨⟨(1, -(1 / ((((0 : ℕ) : ℝ)) + 1))), nonlinearProgramP_posMultiplierWitness_nonzero 0⟩,
          rfl⟩
    · rw [h_top, nonlinearProgramP_posMultiplierWitness_value lam 0]
      exact EReal.coe_lt_top _
  · -- If the bound is finite, choose `n` so the linear term forces the witness value below it.
    have h_lam_real : (0 : ℝ) < (lam : ℝ) := by
      exact_mod_cast h_lam
    have hb_coe : ((b.toReal : ℝ) : EReal) = b :=
      EReal.coe_toReal h_top hb.ne'
    rcases exists_nat_gt ((Real.exp 1 + 1 - b.toReal) / (lam : ℝ)) with ⟨n, hn⟩
    have hn_one : (n : ℝ) < (n : ℝ) + 1 := by
      linarith
    have hn' : ((Real.exp 1 + 1 - b.toReal) / (lam : ℝ)) < (n : ℝ) + 1 := by
      exact lt_trans hn hn_one
    have hmul : Real.exp 1 + 1 - b.toReal < ((n : ℝ) + 1) * (lam : ℝ) := by
      exact (div_lt_iff₀ h_lam_real).mp hn'
    have hbound_real :
        (Real.exp 1 + 1) - (lam : ℝ) * ((n : ℝ) + 1) < b.toReal := by
      nlinarith [hmul]
    have hbound :
        ((((Real.exp 1 + 1) - (lam : ℝ) * ((n : ℝ) + 1) : ℝ)) : EReal) < b := by
      rw [← hb_coe]
      exact_mod_cast hbound_real
    let p : nonlinearProgramPDualDomain :=
      ⟨(1, -(1 / ((n : ℝ) + 1))), nonlinearProgramP_posMultiplierWitness_nonzero n⟩
    refine ⟨nonlinearProgramPLagrangian p lam, ?_, ?_⟩
    · exact ⟨p, rfl⟩
    · -- The explicit witness value is below the finite bound by the upper estimate above.
      exact lt_of_le_of_lt
        (by simpa [p] using nonlinearProgramP_posMultiplierWitness_upper_bound lam n)
        hbound

/-
The dual optimal value is the supremum of the dual function over λ ≥ 0. Since g(0) = 0 and
g(λ) = -∞ for λ > 0, the dual optimal value is 0.
-/
theorem nonlinearProgramP_dual_optimal_value_eq_zero :
    nonlinearProgramPDualOptimalValue = ((0 : ℝ) : EReal) := by
  -- Unfold the dual optimal value so the goal is the supremum of the dual-function range.
  unfold nonlinearProgramPDualOptimalValue lagrangianDualProblem
  change sSup (Set.range nonlinearProgramPDualFunction) = ((0 : ℝ) : EReal)
  apply le_antisymm
  · -- Every value in the range is at most `0`: the zero multiplier gives `0`, and every
    -- nonzero multiplier is positive and sends the dual function to `⊥`.
    refine sSup_le ?_
    rintro _ ⟨lam, rfl⟩
    by_cases h_lam : lam = 0
    · rw [h_lam, nonlinearProgramP_dual_function_eq_zero_at_zero]
    · have h_pos : (0 : NNReal) < lam := pos_iff_ne_zero.mpr h_lam
      rw [nonlinearProgramP_dual_function_eq_bot_of_pos lam h_pos]
      exact bot_le
  · -- The multiplier `lam = 0` contributes the value `0`, so `0` is below the supremum.
    refine le_sSup ?_
    exact ⟨0, nonlinearProgramP_dual_function_eq_zero_at_zero⟩

/-
The primal optimal value is also 0: feasible points with x, y → -∞ make e^x + e^y approach 0.
Therefore the duality gap is 0.
-/
/-- The same witness family used at multiplier zero is feasible for the primal problem. -/
lemma nonlinearProgramP_zeroWitness_feasible (n : ℕ) :
    (-((n : ℝ) + 1), -((n : ℝ) + 1)) ∈ nonlinearProgramPFeasibleSet := by
  -- The `y`-coordinate is strictly negative, so the witness lies in the domain of the quotient.
  refine ⟨nonlinearProgramP_zeroWitness_nonzero n, ?_⟩
  -- Simplify the constraint value to the witness coordinate itself.
  change (((-((n : ℝ) + 1) : ℝ) ^ 2) / (-((n : ℝ) + 1) : ℝ)) ≤ 0
  have hdiv :
      (((-((n : ℝ) + 1) : ℝ) ^ 2) / (-((n : ℝ) + 1) : ℝ)) = -((n : ℝ) + 1) := by
    field_simp [nonlinearProgramP_zeroWitness_nonzero n]
  rw [hdiv]
  -- The simplified coordinate is negative, so the constraint is satisfied.
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by
    positivity
  linarith

theorem nonlinearProgramP_primal_optimal_value_eq_zero_and_duality_gap_eq_zero :
    nonlinearProgramPPrimalOptimalValue = ((0 : ℝ) : EReal) ∧
      nonlinearProgramPDualityGap = ((0 : ℝ) : EReal) := by
  -- Route correction: prove the primal infimum by the same lower-bound/approximation pattern
  -- used for the dual function at `lam = 0`, but now over the feasible image set.
  have h_primal : nonlinearProgramPPrimalOptimalValue = ((0 : ℝ) : EReal) := by
    -- Unfold the primal value so the goal becomes an infimum over feasible objective values.
    unfold nonlinearProgramPPrimalOptimalValue optimalValue
    refine sInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_
    · -- Every feasible objective value is nonnegative because it is a sum of exponentials.
      rintro _ ⟨p, hp, rfl⟩
      have h_nonneg : (0 : ℝ) ≤ Real.exp p.1 + Real.exp p.2 := by
        positivity
      simpa [nonlinearProgramPObjective] using
        (show (0 : EReal) ≤ ((Real.exp p.1 + Real.exp p.2 : ℝ) : EReal) by
          exact_mod_cast h_nonneg)
    · -- The explicit feasible witness family drives the objective below any `w > 0`.
      intro w hw
      have h_eventually : ∀ᶠ n : ℕ in Filter.atTop,
          (((2 : ℝ) * Real.exp (-((n : ℝ) + 1)) : ℝ) : EReal) < w := by
        exact nonlinearProgramP_zeroWitness_tendsto_zero.eventually (Iio_mem_nhds hw)
      rcases h_eventually.exists with ⟨n, hn⟩
      refine ⟨((nonlinearProgramPObjective (-((n : ℝ) + 1), -((n : ℝ) + 1)) : ℝ) : EReal),
        ?_, ?_⟩
      · exact ⟨(-((n : ℝ) + 1), -((n : ℝ) + 1)), nonlinearProgramP_zeroWitness_feasible n, rfl⟩
      · -- Reuse the closed-form witness value already computed at multiplier zero.
        rw [show ((nonlinearProgramPObjective (-((n : ℝ) + 1), -((n : ℝ) + 1)) : ℝ) : EReal) =
            (((2 : ℝ) * Real.exp (-((n : ℝ) + 1)) : ℝ) : EReal) by
              simpa [nonlinearProgramPObjective, nonlinearProgramPLagrangian] using
                nonlinearProgramP_zeroWitness_value n]
        exact hn
  constructor
  · -- The first component is exactly the primal-value computation above.
    exact h_primal
  · -- Once both optimal values are identified as `0`, the duality gap is a direct simplification.
    simpa [nonlinearProgramPDualityGap, dualityGap, h_primal,
      nonlinearProgramP_dual_optimal_value_eq_zero]

end «problem-1»
