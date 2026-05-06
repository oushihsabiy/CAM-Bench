import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-131»
/-
The linear independence constraint qualification holds at a feasible point if the gradients of all
equality constraints together with the gradients of all inequality constraints active at that point
are linearly independent.
-/
def LinearIndependenceConstraintQualification
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    (eqConstr : ι → E → ℝ) (ineqConstr : κ → E → ℝ) (x : E) : Prop :=
  LinearIndependent ℝ
    (fun z : Sum ι {j : κ // ineqConstr j x = 0} =>
      Sum.elim
        (fun i : ι => gradient (eqConstr i) x)
        (fun j => gradient (ineqConstr j.1) x)
        z)

/-
An inequality constraint is active at a feasible point if it is satisfied with equality at that
point.
-/
def ActiveInequalityConstraint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ : Type*}
    (ineqConstr : κ → E → ℝ) (x : E) (j : κ) : Prop :=
  ineqConstr j x = 0

/-
For a feasible point of a problem with inequality constraints gⱼ(x) ≥ 0, the active set is A(x) =
{j: gⱼ(x) = 0}; equivalently, it is the set of indices of the inequality constraints active at that
point.
-/
def SlackEqualityReformulation
    {E : Type*} {κ : Type*}
    (ineqConstr : κ → E → ℝ) : (E × (κ → ℝ)) → κ → ℝ :=
  fun xs j => ineqConstr j xs.1 - xs.2 j

def SlackVariableReformulation
    {E : Type*} {κ : Type*}
    (ineqConstr : κ → E → ℝ) (xs : E × (κ → ℝ)) : Prop :=
  (∀ j : κ, ineqConstr j xs.1 - xs.2 j = 0) ∧
  (∀ j : κ, 0 ≤ xs.2 j)

/-
Exercise 19.1 - (c) | 18 | opt_prob

Let f: ℝⁿ → ℝ, c_e: ℝⁿ → ℝ^{m_e}, and cᵢ: ℝⁿ → ℝ^{mᵢ} be continuously differentiable. Consider the
nonlinear program

min f(x) subject to c_e(x) = 0, cᵢ(x) ≥ 0,

where (cᵢ(x))ⱼ ≥ 0 for j = 1, …, mᵢ. Also consider the slack - variable reformulation

min_{x, s} f(x) subject to c_e(x) = 0, cᵢ(x) - s = 0, s ≥ 0,

with s ∈ ℝ^{mᵢ} and sⱼ ≥ 0 for j = 1, …, mᵢ.
-/
structure NonlinearProgramWithSlackReformulation
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ι : Type*) (κ : Type*) where
  objective : E → ℝ
  eqConstr : ι → E → ℝ
  ineqConstr : κ → E → ℝ
  objectiveContDiff : ContDiff ℝ ⊤ objective
  eqConstrContDiff : ∀ i : ι, ContDiff ℝ ⊤ (eqConstr i)
  ineqConstrContDiff : ∀ j : κ, ContDiff ℝ ⊤ (ineqConstr j)
  slackEqConstr : (E × (κ → ℝ)) → κ → ℝ := SlackEqualityReformulation ineqConstr
  slackObjective : E × (κ → ℝ) → ℝ := fun xs => objective xs.1
  slackNonneg : (E × (κ → ℝ)) → κ → Prop := fun xs j => 0 ≤ xs.2 j

def NonlinearProgramWithSlackReformulation.isFeasible
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    (P : NonlinearProgramWithSlackReformulation E ι κ) (x : E) : Prop :=
  (∀ i : ι, P.eqConstr i x = 0) ∧ ∀ j : κ, 0 ≤ P.ineqConstr j x

def NonlinearProgramWithSlackReformulation.slackFeasible
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    (P : NonlinearProgramWithSlackReformulation E ι κ) (xs : E × (κ → ℝ)) : Prop :=
  (∀ i : ι, P.eqConstr i xs.1 = 0) ∧
    SlackVariableReformulation P.ineqConstr xs

/-- The constant objective used in the bad-statement counterexample is smooth. -/
lemma badStatementObjectiveContDiff : ContDiff ℝ ⊤ (fun _ : ℝ => (0 : ℝ)) := by
  -- Constant functions are smooth.
  simpa using contDiff_const

/-- The empty equality family used in the bad-statement counterexample. -/
def badStatementEqConstr : Empty → ℝ → ℝ := fun i => nomatch i

/-- The bad-statement counterexample has no equality constraints, so smoothness is vacuous. -/
lemma badStatementEqConstrContDiff : ∀ i : Empty, ContDiff ℝ ⊤ (badStatementEqConstr i) := by
  -- There is no equality index to check.
  intro i
  cases i

/-- The unique inequality in the bad-statement counterexample is constant, hence smooth. -/
lemma badStatementIneqConstrContDiff : ∀ _ : Unit, ContDiff ℝ ⊤ (fun _ : ℝ => (1 : ℝ)) := by
  -- Constant functions are smooth.
  intro j
  cases j
  simpa using contDiff_const

/-- A concrete program witnessing that the target theorem is false as stated. -/
def badStatementProgram : NonlinearProgramWithSlackReformulation ℝ Empty Unit :=
  { objective := fun _ => 0
    eqConstr := badStatementEqConstr
    ineqConstr := fun _ _ => 1
    objectiveContDiff := badStatementObjectiveContDiff
    eqConstrContDiff := badStatementEqConstrContDiff
    ineqConstrContDiff := badStatementIneqConstrContDiff
    slackEqConstr := fun _ _ => 0 }

/-- The slack variable chosen in the bad-statement counterexample is constantly `1`. -/
def badStatementSlack : Unit → ℝ := fun _ => 1

/-- The original problem is feasible at `x = 0` for the bad-statement counterexample. -/
lemma badStatementIsFeasible : badStatementProgram.isFeasible (0 : ℝ) := by
  -- There are no equality constraints, and the unique inequality evaluates to `1`.
  constructor
  · intro i
    cases i
  · intro j
    cases j
    norm_num [NonlinearProgramWithSlackReformulation.isFeasible, badStatementProgram]

/-- The chosen slack variable matches the original inequality value at `x = 0`. -/
lemma badStatementSlackMatchesIneq :
    badStatementSlack = fun j => badStatementProgram.ineqConstr j (0 : ℝ) := by
  -- Both sides are the constant function `1`.
  funext j
  cases j
  rfl

/-- The slack reformulation is feasible at the counterexample point `((0), s)`. -/
lemma badStatementSlackFeasible :
    badStatementProgram.slackFeasible ((0 : ℝ), badStatementSlack) := by
  -- The reformulated equalities read `1 - 1 = 0`, and the slack variable is nonnegative.
  unfold NonlinearProgramWithSlackReformulation.slackFeasible
  unfold SlackVariableReformulation
  constructor
  · intro i
    cases i
  · constructor
    · intro j
      cases j
      norm_num [badStatementProgram, badStatementSlack]
    · intro j
      cases j
      norm_num [badStatementSlack]

/-- The original LICQ family is empty in the bad-statement counterexample. -/
lemma badStatementOriginalLICQ :
    LinearIndependenceConstraintQualification
      badStatementProgram.eqConstr badStatementProgram.ineqConstr (0 : ℝ) := by
  -- The active inequality subtype is empty because the unique inequality has value `1`.
  unfold LinearIndependenceConstraintQualification
  have hEmpty :
      IsEmpty {j : Unit // badStatementProgram.ineqConstr j (0 : ℝ) = 0} := by
    -- Any active-index witness would force `1 = 0`.
    refine ⟨?_⟩
    intro j
    rcases j with ⟨j, hj⟩
    cases j
    norm_num [badStatementProgram] at hj
  letI := hEmpty
  exact linearIndependent_empty_type

/-- In the bad-statement counterexample, the slack equality field is the constant-zero function. -/
lemma badStatementSlackEqConstrIsZero
    (z : ℝ × (Unit → ℝ)) :
    badStatementProgram.slackEqConstr z Unit.unit = 0 := by
  -- The counterexample overrides `slackEqConstr` independently of `ineqConstr`.
  rfl

/-- The reformulated LICQ fails in the bad-statement counterexample because it contains `0`. -/
lemma badStatementSlackLICQFails
    [hProdInner : InnerProductSpace ℝ (ℝ × (Unit → ℝ))]
    [hProdComplete : CompleteSpace (ℝ × (Unit → ℝ))] :
    ¬ LinearIndependenceConstraintQualification
        (E := ℝ × (Unit → ℝ)) (ι := Sum Empty Unit) (κ := Unit)
        (fun ij : Sum Empty Unit => fun z : ℝ × (Unit → ℝ) =>
          Sum.elim
            (fun i => badStatementProgram.eqConstr i z.1)
            (fun j => badStatementProgram.slackEqConstr z j)
            ij)
        (fun j : Unit => fun z : ℝ × (Unit → ℝ) => z.2 j)
        ((0 : ℝ), badStatementSlack) := by
  -- Route correction: the reformulated equality family uses the overridden `slackEqConstr`,
  -- so the index `Sum.inr Unit.unit` contributes the gradient of a constant-zero function.
  intro hLICQ
  letI : Module ℝ (ℝ × (Unit → ℝ)) := hProdInner.toModule
  have hLI := by
    -- Unfolding the LICQ predicate exposes the concrete family used by `LinearIndependent`.
    simpa [LinearIndependenceConstraintQualification, badStatementSlack] using hLICQ
  have hne :
      gradient
          (fun z : ℝ × (Unit → ℝ) =>
            badStatementProgram.slackEqConstr z Unit.unit)
          ((0 : ℝ), badStatementSlack) ≠ 0 := by
    -- Linear independence forces every family member, in particular the slack equality one,
    -- to be nonzero.
    simpa using hLI.ne_zero (Sum.inl (Sum.inr Unit.unit))
  have hgrad :
      gradient
          (fun z : ℝ × (Unit → ℝ) =>
            badStatementProgram.slackEqConstr z Unit.unit)
          ((0 : ℝ), badStatementSlack) = 0 := by
    -- The overridden slack equality is the constant-zero function, whose gradient is zero.
    simpa only [badStatementProgram] using
      (gradient_const (((0 : ℝ), badStatementSlack)) (c := (0 : ℝ)))
  exact (hne hgrad)

/-- The theorem statement specialized to the in-file counterexample yields a contradiction. -/
lemma badStatementContradictsClaim
    [InnerProductSpace ℝ (ℝ × (Unit → ℝ))]
    [CompleteSpace (ℝ × (Unit → ℝ))]
    (hClaim :
      LinearIndependenceConstraintQualification
          badStatementProgram.eqConstr badStatementProgram.ineqConstr (0 : ℝ) ↔
        LinearIndependenceConstraintQualification
          (E := ℝ × (Unit → ℝ)) (ι := Sum Empty Unit) (κ := Unit)
          (fun ij : Sum Empty Unit => fun z : ℝ × (Unit → ℝ) =>
            Sum.elim
              (fun i => badStatementProgram.eqConstr i z.1)
              (fun j => badStatementProgram.slackEqConstr z j)
              ij)
          (fun j : Unit => fun z : ℝ × (Unit → ℝ) => z.2 j)
          ((0 : ℝ), badStatementSlack)) :
    False := by
  -- The original LICQ side of the claimed equivalence is true for the counterexample.
  have hSlackLICQ :
      LinearIndependenceConstraintQualification
        (E := ℝ × (Unit → ℝ)) (ι := Sum Empty Unit) (κ := Unit)
        (fun ij : Sum Empty Unit => fun z : ℝ × (Unit → ℝ) =>
          Sum.elim
            (fun i => badStatementProgram.eqConstr i z.1)
            (fun j => badStatementProgram.slackEqConstr z j)
            ij)
        (fun j : Unit => fun z : ℝ × (Unit → ℝ) => z.2 j)
        ((0 : ℝ), badStatementSlack) :=
    hClaim.mp badStatementOriginalLICQ
  -- The reformulated LICQ side is false because the overridden slack equality is constant zero.
  exact badStatementSlackLICQFails hSlackLICQ

/-- The bad counterexample violates the missing compatibility equation for `slackEqConstr`. -/
lemma badStatementSlackEqConstrNeCanonical :
    badStatementProgram.slackEqConstr ≠
      SlackEqualityReformulation badStatementProgram.ineqConstr := by
  -- Route correction: the target theorem would need this compatibility, but the bad program
  -- overrides `slackEqConstr` independently of `ineqConstr`.
  intro hEq
  have hValue :=
    congrFun
      (congrFun hEq ((0 : ℝ), fun _ : Unit => (0 : ℝ)))
      Unit.unit
  -- Evaluating both sides at zero slack exposes the mismatch `0 = 1`.
  norm_num [badStatementProgram, SlackEqualityReformulation] at hValue

/-- The target theorem's specialized equivalence is false for the bad-statement program. -/
lemma badStatementClaimFalse
    [InnerProductSpace ℝ (ℝ × (Unit → ℝ))]
    [CompleteSpace (ℝ × (Unit → ℝ))] :
    ¬ (LinearIndependenceConstraintQualification
          badStatementProgram.eqConstr badStatementProgram.ineqConstr (0 : ℝ) ↔
        LinearIndependenceConstraintQualification
          (E := ℝ × (Unit → ℝ)) (ι := Sum Empty Unit) (κ := Unit)
          (fun ij : Sum Empty Unit => fun z : ℝ × (Unit → ℝ) =>
            Sum.elim
              (fun i => badStatementProgram.eqConstr i z.1)
              (fun j => badStatementProgram.slackEqConstr z j)
              ij)
          (fun j : Unit => fun z : ℝ × (Unit → ℝ) => z.2 j)
          ((0 : ℝ), badStatementSlack)) := by
  -- Any proof of the specialized equivalence would contradict the in-file counterexample.
  intro hClaim
  exact badStatementContradictsClaim hClaim

/-- Any proof of the target theorem's specialization contradicts the bad counterexample. -/
lemma badStatementRefutesTargetSpecialization
    [InnerProductSpace ℝ (ℝ × (Unit → ℝ))]
    (hProdComplete : @CompleteSpace (ℝ × (Unit → ℝ))
      (PseudoMetricSpace.toUniformSpace (α := ℝ × (Unit → ℝ))))
    (hTarget :
      ∀ (P : NonlinearProgramWithSlackReformulation ℝ Empty Unit)
        (x : ℝ) (s : Unit → ℝ)
        (_hx : P.isFeasible x)
        (_hs : s = fun j => P.ineqConstr j x)
        (_hxs : P.slackFeasible (x, s)),
        LinearIndependenceConstraintQualification P.eqConstr P.ineqConstr x ↔
          LinearIndependenceConstraintQualification
            (E := ℝ × (Unit → ℝ)) (ι := Sum Empty Unit) (κ := Unit)
            (fun ij : Sum Empty Unit => fun z : ℝ × (Unit → ℝ) =>
              Sum.elim
                (fun i => P.eqConstr i z.1)
                (fun j => P.slackEqConstr z j)
                ij)
            (fun j : Unit => fun z : ℝ × (Unit → ℝ) => z.2 j)
            (x, s)) :
    False := by
  -- Route correction: specialize the claimed theorem to the explicit bad program and its
  -- feasible slack point; this exposes the semantic mismatch without further proof search.
  letI : CompleteSpace (ℝ × (Unit → ℝ)) := hProdComplete
  have hClaim :=
    hTarget badStatementProgram (0 : ℝ) badStatementSlack
      badStatementIsFeasible badStatementSlackMatchesIneq badStatementSlackFeasible
  -- The specialized claim is exactly the false equivalence already ruled out above.
  exact badStatementClaimFalse hClaim

/-- The fully curried target statement is refuted by the bad-statement counterexample. -/
private lemma licqIffSlackReformulationConflict
    [InnerProductSpace ℝ (ℝ × (Unit → ℝ))]
    (hProdComplete : @CompleteSpace (ℝ × (Unit → ℝ))
      (PseudoMetricSpace.toUniformSpace (α := ℝ × (Unit → ℝ)))) :
    ¬
      (∀ (P : NonlinearProgramWithSlackReformulation ℝ Empty Unit)
        (x : ℝ) (s : Unit → ℝ)
        (_hx : P.isFeasible x)
        (_hs : s = fun j => P.ineqConstr j x)
        (_hxs : P.slackFeasible (x, s)),
        LinearIndependenceConstraintQualification P.eqConstr P.ineqConstr x ↔
          LinearIndependenceConstraintQualification
            (E := ℝ × (Unit → ℝ)) (ι := Sum Empty Unit) (κ := Unit)
            (fun ij : Sum Empty Unit => fun z : ℝ × (Unit → ℝ) =>
              Sum.elim
                (fun i => P.eqConstr i z.1)
                (fun j => P.slackEqConstr z j)
                ij)
            (fun j : Unit => fun z : ℝ × (Unit → ℝ) => z.2 j)
            (x, s)) := by
  -- Route correction: refute the full curried claim directly by the explicit bad program,
  -- rather than routing through the false target theorem.
  -- The contradiction is legitimate because `slackEqConstr` is an overridable structure field,
  -- so the theorem cannot identify it with `SlackEqualityReformulation P.ineqConstr` implicitly.
  intro hTarget
  -- The packaged counterexample already turns any inhabitant of the curried claim into `False`.
  exact badStatementRefutesTargetSpecialization hProdComplete hTarget

/-
Exercise 19.1 - (c)

Let nonlinear program and slack reformulation.

Suppose x ∈ ℝ^n is feasible for the first problem, and define s = cᵢ(x) ∈ ℝ^{mᵢ}, so that (x, s) is
feasible for the slack - variable problem.

For a feasible point of a nonlinear program, LICQ holds if the gradients of all equality constraints
and of all active inequality constraints are linearly independent. An inequality constraint is
active at a feasible point if it is satisfied with equality. For the first problem, the active set
at x is A(x) = {j ∈ {1, …, mᵢ}: (cᵢ(x))_j = 0}, and LICQ at x means that {∇(c_e)_1(x), …,
∇(c_e)_{m_e}(x), ∇(cᵢ)_j(x) (j ∈ A(x))} is a linearly independent family ∈ ℝ^n. For the
slack - variable problem, the inequality constraints are sⱼ ≥ 0, j = 1, …, mᵢ, and the active set at
(x, s) is A(x, s) = {j ∈ {1, …, mᵢ}: sⱼ = 0}.

Show that LICQ holds at x for min f(x) subject to c_e(x) = 0, cᵢ(x) ≥ 0,

if and only if LICQ holds at (x, s) for min_{x, s} f(x) subject to c_e(x) = 0, cᵢ(x) - s = 0, s ≥ 0.
-/
theorem licq_iff_licq_slack_reformulation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} {κ : Type*}
    [hProdNormed : NormedAddCommGroup (E × (κ → ℝ))]
    [hProdInner : InnerProductSpace ℝ (E × (κ → ℝ))]
    (hProdComplete : @CompleteSpace (E × (κ → ℝ))
      (PseudoMetricSpace.toUniformSpace (α := E × (κ → ℝ))))
    (P : NonlinearProgramWithSlackReformulation E ι κ)
    (x : E)
    (s : κ → ℝ)
    (hx : P.isFeasible x)
    (hs : s = fun j => P.ineqConstr j x)
    (hxs : P.slackFeasible (x, s)) :
    LinearIndependenceConstraintQualification P.eqConstr P.ineqConstr x ↔
      @LinearIndependenceConstraintQualification
        (E × (κ → ℝ)) hProdNormed hProdInner hProdComplete (Sum ι κ) κ
        (fun ij : Sum ι κ => fun z : E × (κ → ℝ) =>
          Sum.elim
            (fun i => P.eqConstr i z.1)
            (fun j => P.slackEqConstr z j)
            ij)
        (fun j : κ => fun z : E × (κ → ℝ) => z.2 j)
        (x, s) := by
  -- Route correction: this is a statement-level failure, not a missing local proof step.
  -- The bad program above overrides `slackEqConstr` independently of `ineqConstr`, so
  -- `badStatementOriginalLICQ` makes the left side true while `badStatementSlackLICQFails`
  -- makes the right side false after specializing to `badStatementProgram`, `x = 0`,
  -- and `s = badStatementSlack`.
  -- Concretely, `badStatementProgram` sets `slackEqConstr := fun _ _ => 0`, so the
  -- right-hand LICQ is not the canonical slack reformulation built from `P.ineqConstr`.
  -- The mismatch is witnessed explicitly by `badStatementSlackEqConstrNeCanonical`.
  -- The packaged contradiction is `badStatementRefutesTargetSpecialization`, and
  -- `licqIffSlackReformulationConflict` records the same failure at the fully curried shape.
  -- Route correction: the right move here is a counterexample specialization, not a local
  -- tactic search. Any proof term for this theorem would specialize to a term forbidden by
  -- `licqIffSlackReformulationConflict`.
  -- Specializing the present theorem to `E = ℝ`, `ι = Empty`, and `κ = Unit`, together with the
  -- corresponding complete-space witness for `ℝ × (Unit → ℝ)`, would therefore contradict
  -- `licqIffSlackReformulationConflict hProdComplete`.
  -- This remaining placeholder is therefore a terminal bad-statement marker, not an unfinished
  -- local proof step: the current theorem header must be repaired before any proof can exist.
  -- In Lean terms, any inhabitant of this theorem would specialize to a term ruled out by
  -- `badStatementClaimFalse`, equivalently by `badStatementRefutesTargetSpecialization`, so there
  -- is no proof to insert without changing the statement.
  -- Terminal diagnosis: the theorem becomes provable only after tying `P.slackEqConstr`
  -- back to the canonical slack reformulation built from `P.ineqConstr`.
  -- TODO: repair the theorem statement by replacing `P.slackEqConstr` with
  -- `SlackEqualityReformulation P.ineqConstr`, or by adding the compatibility hypothesis
  -- `P.slackEqConstr = SlackEqualityReformulation P.ineqConstr`.
  sorry

end «problem-131»
