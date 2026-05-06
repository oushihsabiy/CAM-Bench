import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-15»
/-
For a convex optimization problem with inequality constraints fᵢ(x) ≤ q 0, Slater's condition holds
if there exists x∈ℝ^n such that fᵢ(x) < 0 for all i = 1, ..., m.
-/
def StrongDuality (pStar dStar : ℝ) : Prop :=
  pStar = dStar

/-
Let f₀, f₁, ..., fₘ: ℝ^n→ℝ be convex functions. Consider the optimization problem minimize & f₀(x);
subject to & fᵢ(x) ≤ 0, i = 1, ..., m, array with variable x∈ℝ^n.
-/
structure ConvexPrimalProblem (n m : ℕ) where
  objective : (Fin n → ℝ) → ℝ
  constraints : Fin m → (Fin n → ℝ) → ℝ

def ConvexPrimalProblem.isFeasible {n m : ℕ} (P : ConvexPrimalProblem n m) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin m, P.constraints i x ≤ 0

def ConvexPrimalProblem.objectiveValue {n m : ℕ} (P : ConvexPrimalProblem n m) (x : Fin n → ℝ) : ℝ :=
  P.objective x

def ConvexPrimalProblem.dualFunction {n m : ℕ} (P : ConvexPrimalProblem n m) (lam : Fin m → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x : Fin n → ℝ, r = P.objective x + ∑ i : Fin m, lam i * P.constraints i x}

def ConvexPrimalProblem.satisfiesSlater {n m : ℕ} (P : ConvexPrimalProblem n m) : Prop :=
  ∃ x : Fin n → ℝ, ∀ i : Fin m, P.constraints i x < 0

/-
The dual problem is maximize & g(λ); subject to & λ succeq 0, array where λ∈ℝ^m, λ_i ≥ 0 for i =
1, ..., m, and g is the dual function associated with the primal problem.
-/
structure LagrangeDualProblem (n m : ℕ) where
  primal : ConvexPrimalProblem n m

def LagrangeDualProblem.isFeasible {n m : ℕ} (_D : LagrangeDualProblem n m) (lam : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, 0 ≤ lam i

def LagrangeDualProblem.objectiveValue {n m : ℕ} (D : LagrangeDualProblem n m) (lam : Fin m → ℝ) : ℝ :=
  D.primal.dualFunction lam

def LagrangeDualProblem.dualFunction {n m : ℕ} (D : LagrangeDualProblem n m) (lam : Fin m → ℝ) : ℝ :=
  D.primal.dualFunction lam

/-
For a fixed t > 0, consider the unconstrained optimization problem minimize f₀(x) + tmax_i = 1, ...,
m
fᵢ(x)^ +, where fᵢ(x)^ + = fᵢ(x), 0 for i = 1, ..., m.
-/
structure ExactPenaltyProblem (n m : ℕ) where
  primal : ConvexPrimalProblem n m
  t : ℝ
  t_pos : 0 < t

def ExactPenaltyProblem.positivePart (P : ExactPenaltyProblem n m) (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  max (P.primal.constraints i x) 0

def ExactPenaltyProblem.penaltyTerm (P : ExactPenaltyProblem n m) (x : Fin n → ℝ) : ℝ :=
  sSup ((fun i : Fin m => P.positivePart i x) '' Set.univ)

def ExactPenaltyProblem.objectiveValue (P : ExactPenaltyProblem n m) (x : Fin n → ℝ) : ℝ :=
  P.primal.objective x + P.t * P.penaltyTerm x

variable {n m : ℕ}

/-- Each positive-part constraint is convex because it is the supremum of the constraint and zero. -/
lemma ExactPenaltyProblem.positivePart_convex (P : ExactPenaltyProblem n m) (i : Fin m)
    (hconstraint_convex : ConvexOn ℝ Set.univ (P.primal.constraints i)) :
    ConvexOn ℝ Set.univ (P.positivePart i) := by
  -- Rewrite the positive part as a pointwise supremum so `ConvexOn.sup` applies directly.
  simpa [ExactPenaltyProblem.positivePart, max_def] using
    hconstraint_convex.sup (convexOn_const 0 convex_univ)

/-- With a nonempty constraint index type, the penalty term is the indexed supremum of the
positive-part constraints. -/
lemma ExactPenaltyProblem.penaltyTerm_eq_ciSup (P : ExactPenaltyProblem n m) [Nonempty (Fin m)]
    (x : Fin n → ℝ) :
    P.penaltyTerm x = ⨆ i : Fin m, P.positivePart i x := by
  -- Rewrite the set supremum as a nonempty finite supremum and then as `ciSup`.
  calc
    P.penaltyTerm x = Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m => P.positivePart i x) := by
      simp [ExactPenaltyProblem.penaltyTerm, Finset.sup'_eq_csSup_image]
    _ = ⨆ i : Fin m, P.positivePart i x := by
      simpa using (Finset.sup'_univ_eq_ciSup (f := fun i : Fin m => P.positivePart i x))

/-- When the constraint index type is nonempty, each positive-part constraint is bounded above by
the penalty term. -/
lemma ExactPenaltyProblem.positivePart_le_penaltyTerm (P : ExactPenaltyProblem n m) (i : Fin m)
    [Nonempty (Fin m)] (x : Fin n → ℝ) :
    P.positivePart i x ≤ P.penaltyTerm x := by
  -- Rewrite the penalty term as an indexed supremum and use the universal upper bound property.
  rw [P.penaltyTerm_eq_ciSup x]
  exact le_ciSup (f := fun j : Fin m => P.positivePart j x) (Set.finite_range _).bddAbove i

/-- The exact-penalty supremum term is convex when each constraint is convex. -/
lemma ExactPenaltyProblem.penaltyTerm_convex (P : ExactPenaltyProblem n m)
    (hconstraints_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (P.primal.constraints i)) :
    ConvexOn ℝ Set.univ P.penaltyTerm := by
  by_cases hm : Nonempty (Fin m)
  · -- In the nonempty case, use the indexed conditional supremum characterization.
    let _ : Nonempty (Fin m) := hm
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    -- Rewrite each penalty term value as a conditional supremum over the constraint indices.
    rw [P.penaltyTerm_eq_ciSup, P.penaltyTerm_eq_ciSup x, P.penaltyTerm_eq_ciSup y]
    refine ciSup_le (fun i : Fin m => ?_)
    -- Apply convexity to the fixed positive-part constraint.
    have hconvex_ineq := (P.positivePart_convex i (hconstraints_convex i)).2 hx hy ha hb hab
    have hxbound : P.positivePart i x ≤ ⨆ j : Fin m, P.positivePart j x :=
      le_ciSup (f := fun j : Fin m => P.positivePart j x) (Set.finite_range _).bddAbove i
    have hybound : P.positivePart i y ≤ ⨆ j : Fin m, P.positivePart j y :=
      le_ciSup (f := fun j : Fin m => P.positivePart j y) (Set.finite_range _).bddAbove i
    -- Bound the endpoint positive-part terms by the penalty term.
    exact hconvex_ineq.trans <| by
      simpa [smul_eq_mul] using
        add_le_add
          (mul_le_mul_of_nonneg_left hxbound ha)
          (mul_le_mul_of_nonneg_left hybound hb)
  · -- If there are no constraints, the penalty term is the constant zero function.
    have hzero : P.penaltyTerm = fun _ : Fin n → ℝ => 0 := by
      funext x
      have himage : ((fun i : Fin m => P.positivePart i x) '' Set.univ : Set ℝ) = ∅ := by
        ext r
        constructor
        · rintro ⟨i, -, rfl⟩
          exact (hm ⟨i⟩).elim
        · simp
      simp [ExactPenaltyProblem.penaltyTerm, himage, Real.sSup_empty]
    -- Route correction: the empty-index case cannot use `ciSup`, so close it by rewriting to zero.
    rw [hzero]
    simpa using (convexOn_const 0 convex_univ)

/-
Consider the convex primal problem and its Lagrange dual problem. Assume Slater's condition holds,
strong duality holds, the dual optimum is attained, and the dual optimal solution is unique; denote
it by λ^star. For a fixed t > 0, consider the exact penalty problem. Show that the objective
function in this problem is convex.
-/
theorem exactPenaltyProblem_objective_convex
    {n m : ℕ} (P : ExactPenaltyProblem n m)
    (hobjective_convex : ConvexOn ℝ Set.univ P.primal.objective)
    (hconstraints_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (P.primal.constraints i)) :
    ConvexOn ℝ Set.univ P.objectiveValue := by
  -- Prove convexity of the penalty term first, then combine it with the convex objective.
  have hpenalty_convex : ConvexOn ℝ Set.univ P.penaltyTerm :=
    P.penaltyTerm_convex hconstraints_convex
  -- Scale the penalty term by the positive penalty parameter and add it to the objective.
  simpa [ExactPenaltyProblem.objectiveValue] using
    hobjective_convex.add (hpenalty_convex.smul P.t_pos.le)

end «problem-15»
