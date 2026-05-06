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

/-- At a feasible point, the supremum reformulation returns the original objective value. -/
lemma supremumReformulation_objectiveValue_eq_of_feasible
    {n ι : Type} [Fintype ι]
    (P : InequalityConstrainedOptimizationProblem n ι) (x : n → ℝ)
    (hxf : P.IsFeasible x) :
    (P.supremumReformulation).ObjectiveValue x = ((P.ObjectiveValue x : ℝ) : EReal) := by
  classical
  -- Unfold the reformulated objective so we can compare its defining supremum pointwise.
  unfold UnconstrainedOptimizationProblem.ObjectiveValue
  unfold InequalityConstrainedOptimizationProblem.supremumReformulation
  unfold InequalityConstrainedOptimizationProblem.ObjectiveValue
  apply le_antisymm
  · -- Every admissible multiplier contributes a nonpositive penalty at a feasible point.
    refine sSup_le ?_
    rintro s ⟨lam, hlam_nonneg, rfl⟩
    have hsum_nonpos : ∑ i : ι, lam i * P.constraint i x ≤ 0 := by
      refine Finset.sum_nonpos ?_
      intro i hi
      exact mul_nonpos_of_nonneg_of_nonpos (hlam_nonneg i) (hxf i)
    apply EReal.coe_le_coe_iff.2
    linarith
  · -- The zero multiplier is admissible, so the original objective value lies below the supremum.
    have hzero_nonneg : ∀ i : ι, 0 ≤ (0 : ℝ) := by
      intro i
      exact le_rfl
    have hzero_mem :
        (((P.objective x + ∑ i : ι, (0 : ℝ) * P.constraint i x : ℝ) : EReal)) ∈
          {s : EReal | ∃ lam : ι → ℝ, (∀ i : ι, 0 ≤ lam i) ∧
            s = ((P.objective x + ∑ i : ι, lam i * P.constraint i x : ℝ) : EReal)} := by
      exact ⟨fun _ => 0, hzero_nonneg, rfl⟩
    have hle :
        ((P.objective x + ∑ i : ι, (0 : ℝ) * P.constraint i x : ℝ) : EReal) ≤
          sSup {s : EReal | ∃ lam : ι → ℝ, (∀ i : ι, 0 ≤ lam i) ∧
            s = ((P.objective x + ∑ i : ι, lam i * P.constraint i x : ℝ) : EReal)} := by
      exact le_sSup hzero_mem
    simpa using hle

/-- At an infeasible point, the supremum reformulation takes the value `⊤`. -/
lemma supremumReformulation_objectiveValue_eq_top_of_not_feasible
    {n ι : Type} [Fintype ι]
    (P : InequalityConstrainedOptimizationProblem n ι) (x : n → ℝ)
    (hxf : ¬ P.IsFeasible x) :
    (P.supremumReformulation).ObjectiveValue x = ⊤ := by
  classical
  -- Unfold the reformulated objective and show its defining set contains arbitrarily large values.
  unfold UnconstrainedOptimizationProblem.ObjectiveValue
  unfold InequalityConstrainedOptimizationProblem.supremumReformulation
  unfold InequalityConstrainedOptimizationProblem.IsFeasible at hxf
  rw [EReal.eq_top_iff_forall_lt]
  push_neg at hxf
  rcases hxf with ⟨i, hi⟩
  intro b
  let t : ℝ := max 0 ((b - P.objective x) / P.constraint i x) + 1
  let lam : ι → ℝ := fun j => if j = i then t else 0
  -- The chosen multiplier is nonnegative and concentrates all weight on one violated constraint.
  have hlam_nonneg : ∀ j : ι, 0 ≤ lam j := by
    intro j
    by_cases hj : j = i
    · have hlamj : lam j = t := by
        simp [lam, hj]
      rw [hlamj]
      unfold t
      have hmax :
          0 ≤ max 0 ((b - P.objective x) / P.constraint i x) := le_max_left 0 _
      linarith
    · simp [lam, hj]
  have hlt_t : (b - P.objective x) / P.constraint i x < t := by
    have hle :
        (b - P.objective x) / P.constraint i x ≤ max 0 ((b - P.objective x) / P.constraint i x) :=
      le_max_right 0 ((b - P.objective x) / P.constraint i x)
    have hone :
        max 0 ((b - P.objective x) / P.constraint i x) <
          max 0 ((b - P.objective x) / P.constraint i x) + 1 := by
      linarith
    exact lt_of_le_of_lt hle hone
  have hmul : b - P.objective x < t * P.constraint i x := by
    rw [div_lt_iff₀ hi] at hlt_t
    simpa [mul_comm] using hlt_t
  have hsum :
      ∑ j : ι, lam j * P.constraint j x = t * P.constraint i x := by
    simp [lam, t]
  have hvalue_gt :
      (b : EReal) <
        ((P.objective x + ∑ j : ι, lam j * P.constraint j x : ℝ) : EReal) := by
    apply EReal.coe_lt_coe_iff.2
    rw [hsum]
    linarith
  have hmem :
      ((P.objective x + ∑ j : ι, lam j * P.constraint j x : ℝ) : EReal) ∈
        {s : EReal | ∃ lam : ι → ℝ, (∀ i : ι, 0 ≤ lam i) ∧
          s = ((P.objective x + ∑ i : ι, lam i * P.constraint i x : ℝ) : EReal)} := by
    exact ⟨lam, hlam_nonneg, rfl⟩
  have hle :
      ((P.objective x + ∑ j : ι, lam j * P.constraint j x : ℝ) : EReal) ≤
        sSup {s : EReal | ∃ lam : ι → ℝ, (∀ i : ι, 0 ≤ lam i) ∧
          s = ((P.objective x + ∑ i : ι, lam i * P.constraint i x : ℝ) : EReal)} := by
    exact le_sSup hmem
  exact lt_of_lt_of_le hvalue_gt hle

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
  classical
  -- Replace the reformulated problem name and work with the two value sets directly.
  dsimp
  -- The nonemptiness assumption belongs to the original statement, even though the lattice squeeze
  -- below does not need to use it explicitly.
  let _ := h_feasible
  set feasibleValues : Set EReal :=
    {r : EReal | ∃ x : n → ℝ, P.IsFeasible x ∧ ((P.ObjectiveValue x : ℝ) : EReal) = r}
      with hfeasibleValues
  set reformValues : Set EReal :=
    {r : EReal | ∃ x : n → ℝ, (P.supremumReformulation).ObjectiveValue x = r}
      with hreformValues
  -- Every feasible objective value is realized by the supremum reformulation at the same point.
  have h_feasible_subset : feasibleValues ⊆ reformValues := by
    intro r hr
    rw [hfeasibleValues] at hr
    rcases hr with ⟨x, hxf, hxr⟩
    rw [hreformValues]
    refine ⟨x, ?_⟩
    rw [supremumReformulation_objectiveValue_eq_of_feasible P x hxf]
    exact hxr
  -- Every reformulated value is either a feasible objective value or `⊤`.
  have h_reform_subset : reformValues ⊆ insert ⊤ feasibleValues := by
    intro r hr
    rw [hreformValues] at hr
    rcases hr with ⟨x, hxr⟩
    by_cases hxf : P.IsFeasible x
    · right
      rw [hfeasibleValues]
      refine ⟨x, hxf, ?_⟩
      calc
        ((P.ObjectiveValue x : ℝ) : EReal) = (P.supremumReformulation).ObjectiveValue x := by
          symm
          exact supremumReformulation_objectiveValue_eq_of_feasible P x hxf
        _ = r := hxr
    · left
      calc
        r = (P.supremumReformulation).ObjectiveValue x := hxr.symm
        _ = ⊤ := supremumReformulation_objectiveValue_eq_top_of_not_feasible P x hxf
  -- The two inclusions squeeze the infima from opposite directions.
  have h_reform_le : sInf reformValues ≤ sInf feasibleValues := by
    exact sInf_le_sInf h_feasible_subset
  have h_feasible_le : sInf feasibleValues ≤ sInf reformValues := by
    exact sInf_le_sInf_of_subset_insert_top h_reform_subset
  exact le_antisymm h_feasible_le h_reform_le

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
  classical
  -- Replace the reformulated problem name and compare the two optimality predicates pointwise.
  dsimp
  ext x
  constructor
  · intro hx
    change
      (P.IsFeasible x ∧
        ∀ y : n → ℝ, P.IsFeasible y → P.ObjectiveValue x ≤ P.ObjectiveValue y) at hx
    rcases hx with ⟨hxf, hxmin⟩
    -- A feasible optimizer remains optimal after infeasible points are sent to `⊤`.
    change ∀ y : n → ℝ,
      (P.supremumReformulation).ObjectiveValue x ≤ (P.supremumReformulation).ObjectiveValue y
    intro y
    by_cases hyf : P.IsFeasible y
    · rw [supremumReformulation_objectiveValue_eq_of_feasible P x hxf,
        supremumReformulation_objectiveValue_eq_of_feasible P y hyf]
      exact EReal.coe_le_coe_iff.2 (hxmin y hyf)
    · rw [supremumReformulation_objectiveValue_eq_top_of_not_feasible P y hyf]
      exact le_top
  · intro hx
    -- Any optimizer of the reformulation must be feasible, because a feasible point exists.
    change ∀ y : n → ℝ,
      (P.supremumReformulation).ObjectiveValue x ≤ (P.supremumReformulation).ObjectiveValue y at hx
    have hxf : P.IsFeasible x := by
      by_contra hx_not_feasible
      rcases h_feasible with ⟨y, hyf⟩
      have hxy := hx y
      rw [supremumReformulation_objectiveValue_eq_top_of_not_feasible P x hx_not_feasible,
        supremumReformulation_objectiveValue_eq_of_feasible P y hyf] at hxy
      have hy_top : (((P.ObjectiveValue y : ℝ) : EReal)) = ⊤ := top_le_iff.mp hxy
      exact EReal.coe_ne_top _ hy_top
    change P.IsFeasible x ∧
      ∀ y : n → ℝ, P.IsFeasible y → P.ObjectiveValue x ≤ P.ObjectiveValue y
    refine ⟨hxf, ?_⟩
    -- Once both points are feasible, the reformulated order is exactly the original one.
    intro y hyf
    have hxy := hx y
    rw [supremumReformulation_objectiveValue_eq_of_feasible P x hxf,
      supremumReformulation_objectiveValue_eq_of_feasible P y hyf] at hxy
    exact EReal.coe_le_coe_iff.1 hxy


end «problem-36»
