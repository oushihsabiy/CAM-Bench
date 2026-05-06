import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-91»
/-
The domain of an extended - real - valued function f is dom f = {x | f(x) < + infinity}.
-/
def domain {α : Type*} (f : α → EReal) : Set α := {x | f x < ⊤}

/-
Given a function f and a feasible set C, a point x* in C is optimal if f(x*) < = f(y) for all y in
C.
-/
def IsOptimalPoint {α β : Type*} [Preorder β] (f : α → β) (C : Set α) (xStar : α) : Prop :=
  xStar ∈ C ∧ ∀ ⦃y : α⦄, y ∈ C → f xStar ≤ f y

/-
Consider the optimization problem: minimize f₀(x) = - \sum_{i = 1}^m log(bᵢ - a_iᵀ x) over x ∈ ℝ^n,
with domain dom f₀ = {x ∈ ℝ^n | Ax < b} = {x ∈ ℝ^n | a_iᵀ x < bᵢ for i = 1, ..., m}.
-/
open scoped BigOperators

structure LogBarrierOptimizationProblem where
  n : ℕ
  m : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def LogBarrierOptimizationProblem.slack
    (p : LogBarrierOptimizationProblem) (x : Fin p.n → ℝ) (i : Fin p.m) : ℝ :=
  p.b i - ∑ j : Fin p.n, p.A i j * x j

def LogBarrierOptimizationProblem.isFeasible
    (p : LogBarrierOptimizationProblem) (x : Fin p.n → ℝ) : Prop :=
  ∀ i : Fin p.m, (∑ j : Fin p.n, p.A i j * x j) < p.b i

def LogBarrierOptimizationProblem.feasibleSet
    (p : LogBarrierOptimizationProblem) : Set (Fin p.n → ℝ) :=
  {x | p.isFeasible x}

def LogBarrierOptimizationProblem.objective
    (p : LogBarrierOptimizationProblem) (x : Fin p.n → ℝ) : EReal := by
  classical
  exact
    if p.isFeasible x then
      (↑(- ∑ i : Fin p.m, Real.log (p.slack x i)) : EReal)
    else
      ⊤

def LogBarrierOptimizationProblem.domainSet
    (p : LogBarrierOptimizationProblem) : Set (Fin p.n → ℝ) :=
  domain p.objective

namespace LogBarrierOptimizationProblem

/-- Membership in the objective domain is exactly feasibility. -/
lemma mem_domainSet_iff_isFeasible
    (p : LogBarrierOptimizationProblem) (x : Fin p.n → ℝ) :
    x ∈ p.domainSet ↔ p.isFeasible x := by
  -- Expand the extended-real objective and observe that only feasible points avoid `⊤`.
  by_cases hx : p.isFeasible x
  · have hlt : ((↑(-∑ i : Fin p.m, Real.log (p.slack x i)) : EReal) < ⊤) := by
      exact EReal.coe_lt_top _
    simpa [LogBarrierOptimizationProblem.domainSet, domain, LogBarrierOptimizationProblem.objective, hx]
      using hlt
  · simp [LogBarrierOptimizationProblem.domainSet, domain, LogBarrierOptimizationProblem.objective, hx]

/-- The slack is the coordinatewise difference `b - A x`. -/
lemma slack_eq_sub_mulVec
    (p : LogBarrierOptimizationProblem) (x : Fin p.n → ℝ) (i : Fin p.m) :
    p.slack x i = p.b i - (p.A *ᵥ x) i := by
  -- This is just the definition of `Matrix.mulVec` rewritten at coordinate `i`.
  simp [LogBarrierOptimizationProblem.slack, Matrix.mulVec, dotProduct]

/-- Points in the objective domain have strictly positive slack in every coordinate. -/
lemma slack_pos_of_mem_domainSet
    (p : LogBarrierOptimizationProblem) {x : Fin p.n → ℝ} (hx : x ∈ p.domainSet) :
    ∀ i : Fin p.m, 0 < p.slack x i := by
  -- Convert domain membership back to the original strict inequalities `A x < b`.
  intro i
  have hfeas : p.isFeasible x := (p.mem_domainSet_iff_isFeasible x).mp hx
  simpa [LogBarrierOptimizationProblem.slack] using sub_pos.mpr (hfeas i)

/-- Equal images under `A` give equal slack vectors. -/
lemma slack_eq_of_mulVec_eq
    (p : LogBarrierOptimizationProblem) {x y : Fin p.n → ℝ}
    (hxy : p.A *ᵥ x = p.A *ᵥ y) (i : Fin p.m) :
    p.slack x i = p.slack y i := by
  -- Once `A x = A y`, the coordinate formula for slack is identical on both sides.
  rw [p.slack_eq_sub_mulVec, p.slack_eq_sub_mulVec]
  exact congrArg (fun z => p.b i - z i) hxy

/-- The slack at the midpoint is the midpoint of the slacks. -/
lemma slack_midpoint
    (p : LogBarrierOptimizationProblem) (x y : Fin p.n → ℝ) (i : Fin p.m) :
    p.slack ((1 / 2 : ℝ) • (x + y)) i = (p.slack x i + p.slack y i) / 2 := by
  -- Rewrite the midpoint through the linearity of `A` and then collect terms.
  rw [p.slack_eq_sub_mulVec, p.slack_eq_sub_mulVec, p.slack_eq_sub_mulVec]
  rw [Matrix.mulVec_smul, Matrix.mulVec_add]
  simp [smul_eq_mul]
  ring

/-- Equal images under `A` preserve both domain membership and objective value. -/
lemma same_mulVec_same_domain_and_objective
    (p : LogBarrierOptimizationProblem) {x y : Fin p.n → ℝ}
    (hxy : p.A *ᵥ x = p.A *ᵥ y) :
    (x ∈ p.domainSet ↔ y ∈ p.domainSet) ∧ p.objective x = p.objective y := by
  have hrow : ∀ i : Fin p.m, ∑ j : Fin p.n, p.A i j * x j = ∑ j : Fin p.n, p.A i j * y j := by
    intro i
    simpa [Matrix.mulVec, dotProduct] using congrArg (fun z => z i) hxy
  -- First transport feasibility through the equality of all slacks.
  have hfeas : p.isFeasible x ↔ p.isFeasible y := by
    constructor
    · intro hx i
      simpa [hrow i] using hx i
    · intro hy i
      simpa [hrow i] using hy i
  have hdomain : x ∈ p.domainSet ↔ y ∈ p.domainSet := by
    simpa [p.mem_domainSet_iff_isFeasible x, p.mem_domainSet_iff_isFeasible y] using hfeas
  have hobjective : p.objective x = p.objective y := by
    -- On feasible points the objective is a real-valued sum of logs, and equal slacks give equal sums.
    by_cases hx : p.isFeasible x
    · have hy : p.isFeasible y := hfeas.mp hx
      have hsum :
          ∑ i : Fin p.m, Real.log (p.slack x i) =
            ∑ i : Fin p.m, Real.log (p.slack y i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [p.slack_eq_of_mulVec_eq hxy i]
      simp [LogBarrierOptimizationProblem.objective, hx, hy, hsum]
    · have hy : ¬ p.isFeasible y := by
        intro hy
        exact hx (hfeas.mpr hy)
      simp [LogBarrierOptimizationProblem.objective, hx, hy]
  exact ⟨hdomain, hobjective⟩

/-- Two optimal points must have the same image under `A`. -/
lemma mulVec_eq_of_isOptimalPoint
    (p : LogBarrierOptimizationProblem) {x y : Fin p.n → ℝ}
    (hx : IsOptimalPoint p.objective p.domainSet x)
    (hy : IsOptimalPoint p.objective p.domainSet y) :
    p.A *ᵥ x = p.A *ᵥ y := by
  classical
  -- We argue by contradiction: differing images give a midpoint with strictly smaller objective.
  by_contra hxy
  obtain ⟨i0, hi0⟩ : ∃ i : Fin p.m, (p.A *ᵥ x) i ≠ (p.A *ᵥ y) i := by
    have hnot : ¬ ∀ i : Fin p.m, (p.A *ᵥ x) i = (p.A *ᵥ y) i := by
      intro hall
      apply hxy
      funext i
      exact hall i
    exact not_forall.mp hnot
  let z : Fin p.n → ℝ := (1 / 2 : ℝ) • (x + y)
  have hxSlackPos : ∀ i : Fin p.m, 0 < p.slack x i := p.slack_pos_of_mem_domainSet hx.1
  have hySlackPos : ∀ i : Fin p.m, 0 < p.slack y i := p.slack_pos_of_mem_domainSet hy.1
  have hzFeasible : p.isFeasible z := by
    -- Midpoint slacks stay positive because they are averages of positive slacks.
    intro i
    have hzSlackPos : 0 < p.slack z i := by
      rw [p.slack_midpoint x y i]
      linarith [hxSlackPos i, hySlackPos i]
    simpa [LogBarrierOptimizationProblem.slack] using hzSlackPos
  have hz : z ∈ p.domainSet := (p.mem_domainSet_iff_isFeasible z).mpr hzFeasible
  have hiSlackNe : p.slack x i0 ≠ p.slack y i0 := by
    -- A differing row sum gives a differing slack in the same coordinate.
    rw [p.slack_eq_sub_mulVec, p.slack_eq_sub_mulVec]
    intro hslack
    have hcoord : (p.A *ᵥ x) i0 = (p.A *ᵥ y) i0 := by
      linarith
    exact hi0 hcoord
  have hcoord_le :
      ∀ i : Fin p.m,
        (1 / 2 : ℝ) * Real.log (p.slack x i) + (1 / 2 : ℝ) * Real.log (p.slack y i) ≤
          Real.log (p.slack z i) := by
    -- Concavity of `log` controls every coordinate at the midpoint.
    intro i
    have hconc :=
      strictConcaveOn_log_Ioi.concaveOn.2 (hxSlackPos i) (hySlackPos i)
        (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    change (1 / 2 : ℝ) * Real.log (p.slack x i) + (1 / 2 : ℝ) * Real.log (p.slack y i) ≤
      Real.log (p.slack ((1 / 2 : ℝ) • (x + y)) i)
    rw [p.slack_midpoint x y i]
    have hmid :
        (1 / 2 : ℝ) * p.slack x i + (1 / 2 : ℝ) * p.slack y i =
          (p.slack x i + p.slack y i) / 2 := by
      ring
    rw [← hmid]
    simpa [smul_eq_mul] using hconc
  have hcoord_lt :
      (1 / 2 : ℝ) * Real.log (p.slack x i0) + (1 / 2 : ℝ) * Real.log (p.slack y i0) <
        Real.log (p.slack z i0) := by
    -- At the coordinate where `A x` and `A y` differ, strict concavity is strict.
    have hstrict :=
      strictConcaveOn_log_Ioi.2 (hxSlackPos i0) (hySlackPos i0) hiSlackNe
        (show (0 : ℝ) < 1 / 2 by norm_num)
        (show (0 : ℝ) < 1 / 2 by norm_num)
        (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    change (1 / 2 : ℝ) * Real.log (p.slack x i0) + (1 / 2 : ℝ) * Real.log (p.slack y i0) <
      Real.log (p.slack ((1 / 2 : ℝ) • (x + y)) i0)
    rw [p.slack_midpoint x y i0]
    have hmid :
        (1 / 2 : ℝ) * p.slack x i0 + (1 / 2 : ℝ) * p.slack y i0 =
          (p.slack x i0 + p.slack y i0) / 2 := by
      ring
    rw [← hmid]
    simpa [smul_eq_mul] using hstrict
  have hsum_lt :
      ∑ i : Fin p.m,
          ((1 / 2 : ℝ) * Real.log (p.slack x i) + (1 / 2 : ℝ) * Real.log (p.slack y i)) <
        ∑ i : Fin p.m, Real.log (p.slack z i) := by
    -- Summing preserves the one strict coordinate and the weak inequalities elsewhere.
    refine Finset.sum_lt_sum (fun i hi => hcoord_le i) ?_
    exact ⟨i0, Finset.mem_univ i0, hcoord_lt⟩
  have hsum_eq :
      ∑ i : Fin p.m, Real.log (p.slack x i) =
        ∑ i : Fin p.m, Real.log (p.slack y i) := by
    -- Optimality forces equal objective values, hence equal real sums of logs.
    have hobj_eq : p.objective x = p.objective y := le_antisymm (hx.2 hy.1) (hy.2 hx.1)
    have hcoe :
        ((-∑ i : Fin p.m, Real.log (p.slack x i) : ℝ) : EReal) =
          ((-∑ i : Fin p.m, Real.log (p.slack y i) : ℝ) : EReal) := by
      have hxFeasible : p.isFeasible x := (p.mem_domainSet_iff_isFeasible x).mp hx.1
      have hyFeasible : p.isFeasible y := (p.mem_domainSet_iff_isFeasible y).mp hy.1
      simpa [LogBarrierOptimizationProblem.objective, hxFeasible, hyFeasible] using hobj_eq
    have hneg :
        (-∑ i : Fin p.m, Real.log (p.slack x i) : ℝ) =
          (-∑ i : Fin p.m, Real.log (p.slack y i) : ℝ) := by
      simpa using congrArg EReal.toReal hcoe
    linarith
  have hsum_split :
      ∑ i : Fin p.m,
          ((1 / 2 : ℝ) * Real.log (p.slack x i) + (1 / 2 : ℝ) * Real.log (p.slack y i)) =
        (1 / 2 : ℝ) * (∑ i : Fin p.m, Real.log (p.slack x i)) +
          (1 / 2 : ℝ) * (∑ i : Fin p.m, Real.log (p.slack y i)) := by
    -- Separate the two weighted sums before using the equality of optimal values.
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hlog_lt :
      ∑ i : Fin p.m, Real.log (p.slack x i) <
        ∑ i : Fin p.m, Real.log (p.slack z i) := by
    rw [hsum_split, hsum_eq] at hsum_lt
    linarith
  have hobj_lt : p.objective z < p.objective x := by
    -- Larger log-sum means smaller barrier objective.
    have hzFeasible' : p.isFeasible z := (p.mem_domainSet_iff_isFeasible z).mp hz
    have hxFeasible : p.isFeasible x := (p.mem_domainSet_iff_isFeasible x).mp hx.1
    rw [LogBarrierOptimizationProblem.objective, if_pos hzFeasible,
      LogBarrierOptimizationProblem.objective, if_pos hxFeasible]
    rw [EReal.coe_lt_coe_iff]
    linarith
  exact (not_le_of_gt hobj_lt) (hx.2 hz)

end LogBarrierOptimizationProblem

/-
Let A ∈ ℝ^(m x n) have rows a_iᵀ for i = 1, ..., m, and let b ∈ ℝ^m have components bᵢ. Consider
logarithmic barrier minimization and assume dom f₀ is nonempty. Let X_opt = {x in dom f₀ | f₀(x) < =
f₀(y) for all y in dom f₀} be the set of optimal points. Prove that for every x* in X_opt, X_opt =
{x* + v | Av = 0}.
-/
theorem optimalSet_eq_translate_of_ker_for_logBarrier
    (p : LogBarrierOptimizationProblem)
    (hdom : (p.domainSet).Nonempty)
    (xStar : Fin p.n → ℝ)
    (hxStar : IsOptimalPoint p.objective p.domainSet xStar) :
    {x : Fin p.n → ℝ | IsOptimalPoint p.objective p.domainSet x} =
      {x : Fin p.n → ℝ |
        ∃ v : Fin p.n → ℝ,
          Matrix.mulVec p.A v = 0 ∧ x = fun j => xStar j + v j} := by
  -- The optimal set is exactly the affine fiber over the unique optimal image `A xStar`.
  ext x
  constructor
  · intro hx
    -- Any optimal point has the same image under `A` as `xStar`, so their difference lies in the kernel.
    have hmul : p.A *ᵥ x = p.A *ᵥ xStar := p.mulVec_eq_of_isOptimalPoint hx hxStar
    let v : Fin p.n → ℝ := x - xStar
    have hv : p.A *ᵥ v = 0 := by
      rw [show v = x - xStar by rfl, Matrix.mulVec_sub, hmul, sub_self]
    have hxEq : x = fun j => xStar j + v j := by
      funext j
      change x j = xStar j + (x j - xStar j)
      ring
    exact ⟨v, hv, hxEq⟩
  · rintro ⟨v, hv, rfl⟩
    -- Conversely, translating by a kernel vector preserves both feasibility and the barrier value.
    have hmul :
        p.A *ᵥ (fun j => xStar j + v j) = p.A *ᵥ xStar := by
      calc
        p.A *ᵥ (fun j => xStar j + v j) = p.A *ᵥ xStar + p.A *ᵥ v := by
          simpa using Matrix.mulVec_add p.A xStar v
        _ = p.A *ᵥ xStar + 0 := by rw [hv]
        _ = p.A *ᵥ xStar := by simp
    rcases p.same_mulVec_same_domain_and_objective hmul with ⟨hdomEq, hobjEq⟩
    have hxMem : (fun j => xStar j + v j) ∈ p.domainSet := hdomEq.mpr hxStar.1
    refine ⟨hxMem, ?_⟩
    -- The transported point inherits optimality from `xStar` because the objective is unchanged.
    intro y hy
    simpa [hobjEq] using hxStar.2 hy
end «problem-91»
