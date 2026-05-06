import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-168»
/-
For the equality - constrained problem min f(x) subject to Ax = b, the KKT system for the Newton
step
(δ x, w) is [∇^2 f(x) & Aᵀ; A & 0] [δ x; w] = - [∇ f(x); Ax - b].
-/
def kktSystem
    {n m : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (hess : Matrix n n ℝ)
    (A : Matrix m n ℝ)
    (grad : n → ℝ)
    (x : n → ℝ)
    (b : m → ℝ) :
    Matrix (Sum n m) (Sum n m) ℝ × (Sum n m → ℝ) :=
  let K : Matrix (Sum n m) (Sum n m) ℝ :=
    Matrix.fromBlocks hess Aᵀ A 0
  let rhs : Sum n m → ℝ :=
    Sum.elim
      (fun i => -grad i)
      (fun j => -(A.mulVec x j - b j))
  (K, rhs)

/-
For a twice differentiable equality - constrained problem, a Newton step is a pair (δ x, w) that
solves the KKT linearization of the first - order optimality conditions at the current point.
-/
def newtonStep
    {n m : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (hess : Matrix n n ℝ)
    (A : Matrix m n ℝ)
    (grad : n → ℝ)
    (x : n → ℝ)
    (b : m → ℝ)
    (Δx : n → ℝ)
    (w : m → ℝ) : Prop :=
  let system := kktSystem hess A grad x b
  let K := system.1
  let rhs := system.2
  K.mulVec (Sum.elim Δx w) = rhs

def separableEqualityNewtonStepOpCount (n : ℕ) : ℕ :=
  6 * n + 8

/-
Consider the optimization problem minimize ∑_{i = 1}^n fᵢ(xᵢ) subject to ∑_{i = 1}^n xᵢ = 1, with
decision variable x = (x₁, …, xₙ) ∈ ℝ^n, where each fᵢ: ℝ → ℝ is twice continuously differentiable
and satisfies fᵢ''(z) ≥ m > 0 for all z ∈ ℝ, i = 1, …, n.
-/
structure SeparableEqualityConstrainedProblem where
  n : ℕ
  f : Fin n → ℝ → ℝ
  objective : (Fin n → ℝ) → ℝ := fun x => ∑ i, f i (x i)
  feasible : (Fin n → ℝ) → Prop := fun x => (∑ i, x i) = 1
  m : ℝ
  m_pos : 0 < m
  f_contDiff : ∀ i, ContDiff ℝ 2 (f i)
  hess_lower_bound : ∀ i z, m ≤ deriv (deriv (f i)) z

/-- A zero-dimensional problem can override `feasible` and make the claimed Newton step fail. -/
theorem newtonStep_computable_in_linear_time_counterexample :
    ∃ (P : SeparableEqualityConstrainedProblem)
      (x : Fin P.n → ℝ)
      (D : Matrix (Fin P.n) (Fin P.n) ℝ)
      (g : Fin P.n → ℝ),
      (∀ i j, D i j = if i = j then deriv (deriv (P.f i)) (x i) else 0) ∧
      (∀ i, 0 < D i i) ∧
      (∀ i, g i = deriv (P.f i) (x i)) ∧
      P.feasible x ∧
      ¬
        (let wScalar : ℝ := -((∑ i : Fin P.n, g i / D i i) / (∑ i : Fin P.n, (1 : ℝ) / D i i))
         let w : Fin 1 → ℝ := fun _ => wScalar
         let dx : Fin P.n → ℝ := fun i => -(g i + wScalar) / D i i
         newtonStep D (fun _ _ => 1) g x (fun _ => 1) dx w ∧
         ∃ C : ℕ, separableEqualityNewtonStepOpCount P.n ≤ C * P.n + C) := by
  let P : SeparableEqualityConstrainedProblem :=
    { n := 0
      f := fun i => Fin.elim0 i
      feasible := fun _ => True
      m := 1
      m_pos := by norm_num
      f_contDiff := by
        intro i
        exact Fin.elim0 i
      hess_lower_bound := by
        intro i z
        exact Fin.elim0 i }
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The zero-dimensional point is the unique function on `Fin 0`.
    simpa [P] using (fun i : Fin 0 => Fin.elim0 i : Fin 0 → ℝ)
  · -- The zero matrix gives a vacuous diagonal system in dimension zero.
    simpa [P] using (0 : Matrix (Fin 0) (Fin 0) ℝ)
  · -- The gradient is likewise vacuous.
    simpa [P] using (fun i : Fin 0 => Fin.elim0 i : Fin 0 → ℝ)
  · -- There are no coordinates, so the Hessian identity is vacuous.
    intro i j
    exact Fin.elim0 i
  · -- Positivity is vacuous because there are no diagonal entries.
    intro i
    exact Fin.elim0 i
  · -- The gradient identity is vacuous in dimension zero.
    intro i
    exact Fin.elim0 i
  · -- Route correction: this counterexample overrides `feasible` by `True`.
    simp [P]
  · -- The lower KKT row becomes `0 = 1`, so the claimed conclusion is impossible.
    intro h
    -- Projecting to the unique lower-row coordinate exposes the contradictory equation.
    have hrow : (0 : ℝ) = 1 := by
      simpa [P, newtonStep, kktSystem, Matrix.mulVec, dotProduct] using
        congrArg (fun v => v (Sum.inr 0)) h.1
    norm_num at hrow

/-
Consider the separable equality - constrained problem. Let D = diag(f₁''(x₁), ..., fₙ''(xₙ)), let
1∈ℝ^n
be the all - ones vector, and let g∈ℝ^n be the ∇of the objective at x. A Newton step (δ x, w) is
defined by the KKT system [ D & 1; 1ᵀ & 0 ] [ δ x; w ] = [ - g; 0 ]. Prove that, by exploiting this
structure, a Newton step can be computed using O(n) arithmetic operations.
-/
/-- The claimed universal Newton-step formula is refuted by the counterexample above. -/
private theorem newtonStepComputableInLinearTimeUniversalFalse :
    ¬
      ∀ (Q : SeparableEqualityConstrainedProblem)
        (y : Fin Q.n → ℝ)
        (E : Matrix (Fin Q.n) (Fin Q.n) ℝ)
        (gradQ : Fin Q.n → ℝ),
        (∀ i j, E i j = if i = j then deriv (deriv (Q.f i)) (y i) else 0) →
        (∀ i, 0 < E i i) →
        (∀ i, gradQ i = deriv (Q.f i) (y i)) →
        Q.feasible y →
        (let wScalar : ℝ := -((∑ i : Fin Q.n, gradQ i / E i i) / (∑ i : Fin Q.n, (1 : ℝ) / E i i))
         let w : Fin 1 → ℝ := fun _ => wScalar
         let dx : Fin Q.n → ℝ := fun i => -(gradQ i + wScalar) / E i i
         newtonStep E (fun _ _ => 1) gradQ y (fun _ => 1) dx w ∧
         ∃ C : ℕ, separableEqualityNewtonStepOpCount Q.n ≤ C * Q.n + C) := by
  -- Route correction: instantiate the claimed universal formula with the existing witness.
  intro h
  rcases newtonStep_computable_in_linear_time_counterexample with
    ⟨Q, y, E, gradQ, hEdiag, hEpos, hgradQ, hy, hfail⟩
  -- The zero-dimensional model satisfies the displayed hypotheses but falsifies the conclusion.
  exact hfail (h Q y E gradQ hEdiag hEpos hgradQ hy)

/-- Any proof of the target universal claim would contradict the existing counterexample package. -/
private theorem newtonStepComputableInLinearTimeContradiction
    (h :
      ∀ (Q : SeparableEqualityConstrainedProblem)
        (y : Fin Q.n → ℝ)
        (E : Matrix (Fin Q.n) (Fin Q.n) ℝ)
        (gradQ : Fin Q.n → ℝ),
        (∀ i j, E i j = if i = j then deriv (deriv (Q.f i)) (y i) else 0) →
        (∀ i, 0 < E i i) →
        (∀ i, gradQ i = deriv (Q.f i) (y i)) →
        Q.feasible y →
        (let wScalar : ℝ := -((∑ i : Fin Q.n, gradQ i / E i i) / (∑ i : Fin Q.n, (1 : ℝ) / E i i))
         let w : Fin 1 → ℝ := fun _ => wScalar
         let dx : Fin Q.n → ℝ := fun i => -(gradQ i + wScalar) / E i i
         newtonStep E (fun _ _ => 1) gradQ y (fun _ => 1) dx w ∧
         ∃ C : ℕ, separableEqualityNewtonStepOpCount Q.n ≤ C * Q.n + C)) :
    False := by
  -- Route correction: the contradiction is already formalized as the negation theorem above.
  exact newtonStepComputableInLinearTimeUniversalFalse h

/-- This target is false as stated because `hx : P.feasible x` is weaker than the hard-coded
all-ones equality row used by `newtonStep`. The file already contains the witness theorem
`newtonStep_computable_in_linear_time_counterexample`, where the lower KKT row simplifies to
`0 = 1` by taking `P.n = 0` and overriding `P.feasible := True`, and the contradiction lemmas
`newtonStepComputableInLinearTimeUniversalFalse` and
`newtonStepComputableInLinearTimeContradiction` formalize that any closed proof here would yield
`False`, concretely through the term
`newtonStepComputableInLinearTimeContradiction newtonStep_computable_in_linear_time`. The weakest
plausible repair is to replace `hx : P.feasible x` by the concrete equality `∑ i, x i = 1`, or
else redefine the KKT system so its lower row is derived from `P.feasible`. This is a
target-level inconsistency rather than a missing local proof lemma, so the theorem cannot be
completed without repairing its statement; the remaining placeholder is therefore a deliberate
bad-statement marker rather than an unfinished proof search. -/
theorem newtonStep_computable_in_linear_time
    (P : SeparableEqualityConstrainedProblem)
    (x : Fin P.n → ℝ)
    (D : Matrix (Fin P.n) (Fin P.n) ℝ)
    (g : Fin P.n → ℝ)
    (hDdiag : ∀ i j, D i j = if i = j then deriv (deriv (P.f i)) (x i) else 0)
    (hDpos : ∀ i, 0 < D i i)
    (hg : ∀ i, g i = deriv (P.f i) (x i))
    (hx : P.feasible x)
    : let wScalar : ℝ := -((∑ i : Fin P.n, g i / D i i) / (∑ i : Fin P.n, (1 : ℝ) / D i i))
      let w : Fin 1 → ℝ := fun _ => wScalar
      let dx : Fin P.n → ℝ := fun i => -(g i + wScalar) / D i i
      newtonStep D (fun _ _ => 1) g x (fun _ => 1) dx w ∧
      ∃ C : ℕ, separableEqualityNewtonStepOpCount P.n ≤ C * P.n + C := by
  -- Route correction: `hx : P.feasible x` does not imply the concrete lower KKT row used by
  -- `newtonStep D (fun _ _ => 1) g x (fun _ => 1) ...`, because that row is hard-coded by
  -- `A := fun _ _ => 1` and `b := fun _ => 1` instead of being derived from `P.feasible`.
  -- The in-file witness `newtonStep_computable_in_linear_time_counterexample` exploits exactly
  -- this gap with `P.n = 0` and `P.feasible := True`, where the lower row simplifies to `0 = 1`.
  -- The semantic obstruction is already packaged by
  -- `newtonStepComputableInLinearTimeUniversalFalse` and
  -- `newtonStepComputableInLinearTimeContradiction`.
  -- Any closed proof of this theorem would therefore yield the lean-checkable contradiction
  -- `newtonStepComputableInLinearTimeContradiction newtonStep_computable_in_linear_time : False`,
  -- whose concrete conflict is the lower KKT row evaluation at `Sum.inr 0`, namely
  -- the impossible equality `(0 : ℝ) = 1`.
  -- Concretely, the counterexample theorem derives that conflict by applying
  -- `congrArg (fun v => v (Sum.inr 0))` to the asserted KKT equality.
  -- This is the precise lean-checkable obstruction that makes the statement uninhabited.
  -- Route correction: the right action here is to report a bad target statement, not to search
  -- for more helper lemmas, because `newtonStepComputableInLinearTimeUniversalFalse` already
  -- proves that no term can inhabit this theorem without making the development inconsistent.
  -- Specializing the target to that witness forces the lower KKT equation at `Sum.inr 0`,
  -- and that evaluation is exactly the impossible equality `(0 : ℝ) = 1`.
  -- This terminal diagnosis is local and checkable: specializing the target to the witness from
  -- `newtonStep_computable_in_linear_time_counterexample` reproduces the impossible row `0 = 1`.
  -- Bad-statement witness: if this theorem were proved, then
  -- `newtonStepComputableInLinearTimeContradiction newtonStep_computable_in_linear_time`
  -- would be a closed term of `False`.
  -- The contradiction route is fully internal to this file, so there is no missing mathlib lemma
  -- to search for here; the obstruction is the theorem statement itself.
  -- This proof block intentionally stops at the contradiction boundary, because the theorem
  -- statement itself must be repaired before any proof term can exist.
  -- TODO: repair the target upstream by replacing `hx : P.feasible x` with the concrete equality
  -- `∑ i, x i = 1`, or by redefining the KKT lower row so it is generated from `P.feasible`.
  -- This remaining placeholder is deliberate: it preserves compilation while marking a
  -- target-level inconsistency for the orchestrator rather than an unfinished local proof.
  sorry

end «problem-168»
