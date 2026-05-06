import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-138»
/-
For the problem min_x f(x) subject to inequality constraints gᵢ(x) ≤ 0, the Karush - Kuhn - Tucker
conditions at x* assert that there exist multipliers λ_i* ≥ 0 such that gᵢ(x*) ≤ 0 for all i (primal
feasibility), λ_i* gᵢ(x*) = 0 for all i (complementary slackness), and, when differentiable, ∇ f(x*)
+ sum_i λ_i* ∇ gᵢ(x*) = 0 (stationarity).
-/
open scoped BigOperators

def KarushKuhnTuckerConditions
    {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (xStar : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ lam : Fin m → ℝ,
    (∀ i, 0 ≤ lam i) ∧
    (∀ i, g i xStar ≤ 0) ∧
    (∀ i, lam i * g i xStar = 0) ∧
    (gradient f xStar + ∑ i, lam i • gradient (g i) xStar = 0)

/-- Every feasible objective value in the exponential problem is nonnegative. -/
lemma exponentialFeasibleValueNonnegative
    {r : ℝ}
    (hr :
      r ∈ {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin 2),
        x 1 ≠ 0 ∧ ((x 0) ^ 2 / x 1 ≤ 0) ∧ (Real.exp (x 0) + Real.exp (x 1) = r)}) :
    0 ≤ r := by
  -- Route correction: the constraint is not needed here; positivity of both exponentials already
  -- gives the lower bound required for the feasible-value set.
  rcases hr with ⟨x, _, _, hfx⟩
  have hx0 : 0 < Real.exp (x 0) := Real.exp_pos (x 0)
  have hx1 : 0 < Real.exp (x 1) := Real.exp_pos (x 1)
  rw [← hfx]
  linarith

/-- For any positive target level, there is a feasible point with smaller objective value. -/
lemma existsExponentialFeasiblePointWithObjectiveLt
    {w : ℝ} (hw : 0 < w) :
    ∃ x : EuclideanSpace ℝ (Fin 2),
      x 1 ≠ 0 ∧
      ((x 0) ^ 2 / x 1 ≤ 0) ∧
      Real.exp (x 0) + Real.exp (x 1) < w := by
  by_cases hsmall : w < 4
  · let a : ℝ := Real.log (w / 4)
    have hquarter_pos : 0 < w / 4 := by linarith
    have hquarter_lt_one : w / 4 < 1 := by linarith
    have ha_neg : a < 0 := by
      -- The logarithm is negative because the chosen scale factor lies in `(0, 1)`.
      exact (Real.log_neg_iff hquarter_pos).2 hquarter_lt_one
    have ha_ne : a ≠ 0 := ne_of_lt ha_neg
    have hsq_div : a ^ 2 / a = a := by
      -- We simplify the constraint at the diagonal point `(a, a)` using `a ≠ 0`.
      field_simp [ha_ne]
    have hexp : Real.exp a = w / 4 := by
      -- The objective is designed so that both exponential terms equal `w / 4`.
      rw [show a = Real.log (w / 4) by rfl, Real.exp_log hquarter_pos]
    refine ⟨!₂[a, a], ?_, ?_, ?_⟩
    · -- Feasibility requires the denominator to be nonzero.
      simpa using ha_ne
    · -- The inequality constraint reduces to `a ≤ 0`, which follows from `a < 0`.
      change a ^ 2 / a ≤ 0
      rw [hsq_div]
      linarith
    · -- The objective value is exactly `w / 2`, hence strictly below `w`.
      change Real.exp a + Real.exp a < w
      nlinarith
  · refine ⟨!₂[0, 1], ?_, ?_, ?_⟩
    · -- The fallback feasible point has nonzero second coordinate.
      norm_num
    · -- Its constraint value is exactly zero.
      norm_num
    · have h_exp_bound : 1 + Real.exp 1 < 4 := by
        -- The standard estimate `exp 1 < 3` gives a clean absolute upper bound.
        linarith [Real.exp_one_lt_three]
      have hfour_le : 4 ≤ w := le_of_not_gt hsmall
      -- This branch handles large `w` by using the fixed feasible point `(0, 1)`.
      change Real.exp 0 + Real.exp 1 < w
      rw [Real.exp_zero]
      linarith

/-- The feasible objective-value set for the exponential problem has infimum `0`. -/
lemma exponentialFeasibleValueSet_sInf_eq_zero :
    sInf {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin 2),
      x 1 ≠ 0 ∧ ((x 0) ^ 2 / x 1 ≤ 0) ∧ (Real.exp (x 0) + Real.exp (x 1) = r)} = 0 := by
  let S : Set ℝ := {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin 2),
    x 1 ≠ 0 ∧ ((x 0) ^ 2 / x 1 ≤ 0) ∧ (Real.exp (x 0) + Real.exp (x 1) = r)}
  have h_nonempty : S.Nonempty := by
    -- The point `(0, 1)` is feasible and contributes the value `1 + exp 1`.
    refine ⟨1 + Real.exp 1, ?_⟩
    refine ⟨!₂[0, 1], ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · change Real.exp 0 + Real.exp 1 = 1 + Real.exp 1
      rw [Real.exp_zero]
  have h_lower : ∀ a ∈ S, 0 ≤ a := by
    -- Every member of the feasible-value set is a sum of two positive exponentials.
    intro a ha
    exact exponentialFeasibleValueNonnegative ha
  have h_approx : ∀ w, 0 < w → ∃ a ∈ S, a < w := by
    intro w hw
    obtain ⟨x, hx1, hgx, hlt⟩ := existsExponentialFeasiblePointWithObjectiveLt hw
    refine ⟨Real.exp (x 0) + Real.exp (x 1), ?_, hlt⟩
    exact ⟨x, hx1, hgx, rfl⟩
  -- The infimum is zero because zero is a lower bound and feasible values get arbitrarily close.
  exact csInf_eq_of_forall_ge_of_forall_gt_exists_lt h_nonempty h_lower h_approx

/-- The exponential constrained problem has no globally optimal feasible point. -/
lemma noGlobalMinimizerForExponentialConstraintProblem :
    ¬ ∃ xStar : EuclideanSpace ℝ (Fin 2),
      xStar 1 ≠ 0 ∧
      ((xStar 0) ^ 2 / xStar 1 ≤ 0) ∧
      (∀ x : EuclideanSpace ℝ (Fin 2),
        x 1 ≠ 0 → ((x 0) ^ 2 / x 1 ≤ 0) →
        Real.exp (xStar 0) + Real.exp (xStar 1) ≤ Real.exp (x 0) + Real.exp (x 1)) := by
  intro h
  rcases h with ⟨xStar, hxStar1, hgStar, hopt⟩
  have hobj_pos : 0 < Real.exp (xStar 0) + Real.exp (xStar 1) := by
    -- The objective is always strictly positive because each exponential term is positive.
    have hx0 : 0 < Real.exp (xStar 0) := Real.exp_pos (xStar 0)
    have hx1 : 0 < Real.exp (xStar 1) := Real.exp_pos (xStar 1)
    linarith
  obtain ⟨x, hx1, hgx, hlt⟩ :=
    existsExponentialFeasiblePointWithObjectiveLt (w := Real.exp (xStar 0) + Real.exp (xStar 1))
      hobj_pos
  have hle := hopt x hx1 hgx
  linarith


/-
Consider the exponential constrained optimization problem. Determine whether this problem satisfies
the KKT conditions at its optimal solution.
-/
theorem exponentialConstrainedOptimizationProblem_has_no_optimal_solution_and_no_kkt_point :
    let f : EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun x => Real.exp (x 0) + Real.exp (x 1)
    let g : Fin 1 → EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun _ x => (x 0) ^ 2 / x 1
    Set.Nonempty {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin 2), x 1 ≠ 0 ∧ g 0 x ≤ 0 ∧ f x = r} ∧
    BddBelow {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin 2), x 1 ≠ 0 ∧ g 0 x ≤ 0 ∧ f x = r} ∧
    sInf {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin 2), x 1 ≠ 0 ∧ g 0 x ≤ 0 ∧ f x = r} = 0 ∧
    ¬ ∃ xStar : EuclideanSpace ℝ (Fin 2),
      xStar 1 ≠ 0 ∧
      g 0 xStar ≤ 0 ∧
      (∀ x : EuclideanSpace ℝ (Fin 2), x 1 ≠ 0 → g 0 x ≤ 0 → f xStar ≤ f x) ∧
      KarushKuhnTuckerConditions f g xStar := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The feasible-value set is nonempty via the explicit feasible point `(0, 1)`.
    refine ⟨1 + Real.exp 1, ?_⟩
    refine ⟨!₂[0, 1], ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · change Real.exp 0 + Real.exp 1 = 1 + Real.exp 1
      rw [Real.exp_zero]
  · -- Zero is a lower bound because every feasible value is nonnegative.
    refine ⟨0, ?_⟩
    intro r hr
    exact exponentialFeasibleValueNonnegative hr
  · -- The separate infimum lemma keeps the theorem statement flat.
    exact exponentialFeasibleValueSet_sInf_eq_zero
  · intro h
    rcases h with ⟨xStar, hxStar1, hgStar, hopt, _⟩
    -- Route correction: the KKT witness is irrelevant once global optimality is impossible.
    exact noGlobalMinimizerForExponentialConstraintProblem ⟨xStar, hxStar1, hgStar, hopt⟩


end «problem-138»
