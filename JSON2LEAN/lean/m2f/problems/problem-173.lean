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
/-- Complementary slackness forces the multiplier of an inactive inequality to vanish. -/
lemma multiplier_eq_zero_of_inactive_ineq
    {E ι : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [Fintype ι]
    (Eeq Ineq : Set ι)
    (f : E → ℝ)
    (c : ι → E → ℝ)
    (x : E)
    (lam : ι → ℝ)
    (hLam : MultiplierVector Eeq Ineq f c x lam)
    {i : ι}
    (hi : i ∈ Ineq)
    (hc : c i x ≠ 0) :
    lam i = 0 := by
  -- Complementary slackness makes the product `lam i * c i x` vanish.
  have hComp : ComplementarySlackness Ineq c x lam := hLam.2.2.2.2.2.1
  have hSlack : lam i * c i x = 0 := hComp i hi
  -- Since the constraint value is nonzero, the multiplier must be zero.
  exact (mul_eq_zero.mp hSlack).resolve_right hc

/-- Subtracting two stationarity equations leaves only the coefficients on the LICQ support. -/
lemma stationarity_difference_on_LICQ_support
    {E ι : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [Fintype ι]
    (Eeq Ineq : Set ι)
    (f : E → ℝ)
    (c : ι → E → ℝ)
    (x : E)
    (lam lam' : ι → ℝ)
    [DecidablePred fun i => i ∈ Eeq ∪ {k | k ∈ Ineq ∧ c k x = 0}]
    (hLam : MultiplierVector Eeq Ineq f c x lam)
    (hLam' : MultiplierVector Eeq Ineq f c x lam') :
    ∑ i ∈ Finset.univ.filter (fun i => i ∈ Eeq ∪ {k | k ∈ Ineq ∧ c k x = 0}),
      (lam i - lam' i) • gradient (c i) x = 0 := by
  classical
  let S : Set ι := Eeq ∪ {k | k ∈ Ineq ∧ c k x = 0}
  have hStat : Stationarity f c x lam := hLam.2.2.1
  have hStat' : Stationarity f c x lam' := hLam'.2.2.1
  have hZeroOff : ZeroOffConstraintSet Eeq Ineq lam := hLam.2.2.2.2.2.2
  have hZeroOff' : ZeroOffConstraintSet Eeq Ineq lam' := hLam'.2.2.2.2.2.2
  have hFull :
      ∑ i, (lam i - lam' i) • gradient (c i) x = 0 := by
    -- Rewriting both stationarity conditions as equal sums lets us subtract them directly.
    have hSumEq :
        ∑ i, lam i • gradient (c i) x =
          ∑ i, lam' i • gradient (c i) x := by
      exact (sub_eq_zero.mp hStat).symm.trans (sub_eq_zero.mp hStat')
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact hSumEq
  have hRestrictedEqFull :
      ∑ i with S i, (lam i - lam' i) • gradient (c i) x =
        ∑ i, (lam i - lam' i) • gradient (c i) x := by
    -- Every term outside the support already has zero coefficient, so filtering does not change the sum.
    refine Finset.sum_subset
      (s₁ := Finset.univ.filter S) (s₂ := (Finset.univ : Finset ι))
      (f := fun i : ι => (lam i - lam' i) • gradient (c i) x)
      (Finset.filter_subset S Finset.univ) ?_
    intro i _ hiNotMem
    have hiNotSupport : ¬ S i := by
      simpa using hiNotMem
    by_cases hiIneq : i ∈ Ineq
    · have hiInactive : c i x ≠ 0 := by
        intro hcx
        exact hiNotSupport (Or.inr ⟨hiIneq, hcx⟩)
      have hLamZero : lam i = 0 :=
        multiplier_eq_zero_of_inactive_ineq Eeq Ineq f c x lam hLam hiIneq hiInactive
      have hLam'Zero : lam' i = 0 :=
        multiplier_eq_zero_of_inactive_ineq Eeq Ineq f c x lam' hLam' hiIneq hiInactive
      simp [hLamZero, hLam'Zero]
    · have hiOutside : i ∉ Eeq ∪ Ineq := by
        intro hiUnion
        apply hiNotSupport
        rcases hiUnion with hiEq | hiIneq'
        · exact Or.inl hiEq
        · exact False.elim (hiIneq hiIneq')
      have hLamZero : lam i = 0 := hZeroOff i hiOutside
      have hLam'Zero : lam' i = 0 := hZeroOff' i hiOutside
      simp [hLamZero, hLam'Zero]
  -- Replacing the full sum by the filtered one yields the desired restricted stationarity equation.
  have hRestrictedOnS :
      ∑ i with S i, (lam i - lam' i) • gradient (c i) x = 0 := by
    calc
      ∑ i with S i, (lam i - lam' i) • gradient (c i) x
        = ∑ i, (lam i - lam' i) • gradient (c i) x := hRestrictedEqFull
      _ = 0 := hFull
  have hFilterEq :
      Finset.univ.filter S =
        Finset.univ.filter (fun i => i ∈ Eeq ∨ i ∈ Ineq ∧ c i x = 0) := by
    ext i
    simp [Finset.mem_filter, S]
    constructor <;> intro h <;> exact h
  rw [hFilterEq] at hRestrictedOnS
  simpa using hRestrictedOnS

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
  classical
  let _ := hdisjoint
  have hZeroOffStar : ZeroOffConstraintSet Eeq Ineq lamStar := hKKTStar.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro i hiIneq hiInactive
    -- Complementary slackness rules out nonzero multipliers on inactive inequalities.
    exact multiplier_eq_zero_of_inactive_ineq Eeq Ineq f c x lamStar hKKTStar hiIneq hiInactive
  · intro i hiOutside
    -- The distinguished multiplier already vanishes off the declared constraint set.
    exact hZeroOffStar i hiOutside
  · intro lam hLam
    have hZeroOff : ZeroOffConstraintSet Eeq Ineq lam := hLam.2.2.2.2.2.2
    have hLICQ' :
        LinearIndependent ℝ
          (fun j : {i // i ∈ Eeq ∪ {k | k ∈ Ineq ∧ c k x = 0}} =>
            gradient (c j.1) x) := by
      simpa [LICQ] using hLICQ
    have hLinOn :
        LinearIndepOn ℝ (fun i : ι => gradient (c i) x)
          (Eeq ∪ {k | k ∈ Ineq ∧ c k x = 0}) := by
      simpa [Function.comp] using
        (linearIndependent_comp_subtype_iff (R := ℝ)
          (v := fun i : ι => gradient (c i) x)
          (s := Eeq ∪ {k | k ∈ Ineq ∧ c k x = 0})).mp hLICQ'
    have hLinOnFilter :
        LinearIndepOn ℝ (fun i : ι => gradient (c i) x)
          ↑(Finset.univ.filter (fun i => i ∈ Eeq ∪ {k | k ∈ Ineq ∧ c k x = 0})) := by
      simpa using hLinOn
    have hRestricted :
        ∑ i ∈ Finset.univ.filter (fun i => i ∈ Eeq ∪ {k | k ∈ Ineq ∧ c k x = 0}),
          (lam i - lamStar i) • gradient (c i) x = 0 :=
      stationarity_difference_on_LICQ_support Eeq Ineq f c x lam lamStar hLam hKKTStar
    have hCoeffZero :
        ∀ i ∈ Finset.univ.filter (fun i => i ∈ Eeq ∪ {k | k ∈ Ineq ∧ c k x = 0}),
          lam i - lamStar i = 0 :=
      (linearIndepOn_finset_iff.mp hLinOnFilter) (fun i => lam i - lamStar i) hRestricted
    -- A case split on the index shows the two multipliers agree everywhere.
    funext i
    by_cases hiEq : i ∈ Eeq
    · exact sub_eq_zero.mp (hCoeffZero i (by simp [hiEq]))
    · by_cases hiIneq : i ∈ Ineq
      · by_cases hiActive : c i x = 0
        · exact sub_eq_zero.mp (hCoeffZero i (by simp [hiIneq, hiActive]))
        · have hLamZero : lam i = 0 :=
            multiplier_eq_zero_of_inactive_ineq Eeq Ineq f c x lam hLam hiIneq hiActive
          have hStarZero : lamStar i = 0 :=
            multiplier_eq_zero_of_inactive_ineq Eeq Ineq f c x lamStar hKKTStar hiIneq hiActive
          rw [hLamZero, hStarZero]
      · have hiOutside : i ∉ Eeq ∪ Ineq := by
          intro hiUnion
          rcases hiUnion with hiEq' | hiIneq'
          · exact hiEq hiEq'
          · exact hiIneq hiIneq'
        rw [hZeroOff i hiOutside, hZeroOffStar i hiOutside]

end «problem-173»
