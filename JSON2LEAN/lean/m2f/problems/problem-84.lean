import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-84»
/-
For the linear constraints Ax = b and x ≥ 0, a point x is strictly feasible if Ax = b and xᵢ > 0 for
all i = 1, ..., n.
-/
def StrictlyFeasible {m n : Type} [Fintype n] (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) : Prop :=
  A.mulVec x = b ∧ ∀ i : n, 0 < x i

/-
For t > 0, the barrier subproblem is the equality - constrained minimization problem t cᵀ x + φ(x) |
Ax = b, where φ is a barrier function defined on the interior of the inequality constraints.
-/
structure BarrierSubproblem (m n : Type) [Fintype n] where
  A : Matrix m n ℝ
  b : m → ℝ
  c : n → ℝ
  φ : (n → ℝ) → ℝ
  t : ℝ
  t_pos : 0 < t
  domain : Set (n → ℝ)

def BarrierSubproblem.feasibleSet {m n : Type} [Fintype n]
    (P : BarrierSubproblem m n) : Set (n → ℝ) :=
  {x | P.A.mulVec x = P.b ∧ x ∈ P.domain}

def BarrierSubproblem.objective {m n : Type} [Fintype n]
    (P : BarrierSubproblem m n) : (n → ℝ) → ℝ :=
  fun x => P.t * dotProduct P.c x + P.φ x

def BarrierSubproblem.IsMinimizer {m n : Type} [Fintype n]
    (P : BarrierSubproblem m n) (x : n → ℝ) : Prop :=
  x ∈ P.feasibleSet ∧ ∀ y, y ∈ P.feasibleSet → P.objective x ≤ P.objective y

/-
Given the Newton step δ x at x for the equality - constrained barrier problem, the Newton decrement
is
λ(x) = δ xᵀ ∇^2 φ(x)δ x.
-/
def NewtonDecrement {n : Type} [Fintype n] [DecidableEq n]
    (φHess : (n → ℝ) → Matrix n n ℝ) (x Δx : n → ℝ) : ℝ :=
  Real.sqrt (dotProduct Δx ((φHess x).mulVec Δx))

/-
For the dual linear inequalities Aᵀ y ≤ c, a point y∈ℝ^m is dual feasible if Aᵀ y ≤ c componentwise.
-/
def DualFeasible {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (c : n → ℝ) (y : m → ℝ) : Prop :=
  ∀ i : n, ((Matrix.transpose A).mulVec y) i ≤ c i

/-
A function φ defined on the interior of a constraint set is a barrier function if φ(x) is finite on
the interior and φ(x)→ + ∞ as x approaches the boundary from the interior.
-/
def LogarithmicBarrierDomain {n : Type} [Fintype n] (x : n → ℝ) : Prop :=
  ∀ i : n, 0 < x i

structure BarrierFunctionWithDomain (n : Type) where
  domain : Set (n → ℝ)
  toFun : {x : n → ℝ // x ∈ domain} → ℝ

instance {n : Type} : CoeFun (BarrierFunctionWithDomain n) (fun _ => (n → ℝ) → ℝ) where
  coe φ x := by
    classical
    exact if hx : x ∈ φ.domain then φ.toFun ⟨x, hx⟩ else 0

def LogarithmicBarrier {n : Type} [Fintype n] : BarrierFunctionWithDomain n where
  domain := {x | LogarithmicBarrierDomain x}
  toFun := fun x => -∑ i : n, Real.log (x.1 i)



structure PrimalDualLinearProgram (m n : Type) [Fintype m] [Fintype n] where
  A : Matrix m n ℝ
  b : m → ℝ
  c : n → ℝ
  rank_eq : A.rank = Fintype.card m
  strictly_feasible_point : n → ℝ
  strictly_feasible : StrictlyFeasible A b strictly_feasible_point

structure LogBarrierSubproblem (m n : Type) [Fintype n] where
  base : BarrierSubproblem m n

def LogBarrierSubproblem.feasibleSet {m n : Type} [Fintype n]
    (P : LogBarrierSubproblem m n) : Set (n → ℝ) :=
  P.base.feasibleSet ∩ P.base.domain

def LogBarrierSubproblem.objective {m n : Type} [Fintype n]
    (P : LogBarrierSubproblem m n) (x : n → ℝ) : ℝ :=
  P.base.objective x

/-- The logarithmic-barrier Hessian quadratic form is the sum of squared relative steps. -/
lemma newtonDecrement_radicand_eq_sum_sq_div
    {n : Type} [Fintype n] [DecidableEq n] (x dx : n → ℝ) :
    dotProduct dx ((Matrix.diagonal (fun i => 1 / (x i) ^ 2)).mulVec dx) =
      ∑ i : n, (dx i / x i) ^ 2 := by
  classical
  -- Expand the diagonal matrix-vector product and normalize each summand algebraically.
  simp_rw [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hx : x i = 0
  · simp [hx]
  · field_simp [hx]

/-- A decrement at most `1` bounds every squared relative coordinate step by `1`. -/
lemma newton_coordinate_sq_le_one
    {n : Type} [Fintype n] [DecidableEq n] (x dx : n → ℝ)
    (hdecr : NewtonDecrement (fun z => Matrix.diagonal (fun i => 1 / (z i) ^ 2)) x dx ≤ 1) :
    ∀ i : n, (dx i / x i) ^ 2 ≤ 1 := by
  classical
  intro i
  -- Rewrite the decrement as a square root of a sum of nonnegative squares.
  have hsum_le :
      ∑ j : n, (dx j / x j) ^ 2 ≤ 1 := by
    have hsum_nonneg : 0 ≤ ∑ j : n, (dx j / x j) ^ 2 := by
      exact Finset.sum_nonneg (fun j _ => sq_nonneg (dx j / x j))
    have hdecr_nonneg :
        0 ≤ NewtonDecrement (fun z => Matrix.diagonal (fun i => 1 / (z i) ^ 2)) x dx := by
      unfold NewtonDecrement
      exact Real.sqrt_nonneg _
    have hsquare_le :
        (NewtonDecrement (fun z => Matrix.diagonal (fun i => 1 / (z i) ^ 2)) x dx) ^ 2 ≤ 1 := by
      nlinarith
    have hrewrite :
        (NewtonDecrement (fun z => Matrix.diagonal (fun i => 1 / (z i) ^ 2)) x dx) ^ 2 =
          ∑ j : n, (dx j / x j) ^ 2 := by
      rw [NewtonDecrement, newtonDecrement_radicand_eq_sum_sq_div, Real.sq_sqrt hsum_nonneg]
    linarith
  -- Compare the chosen coordinate square with the full finite sum.
  have hcoord_le_sum :
      (dx i / x i) ^ 2 ≤ ∑ j : n, (dx j / x j) ^ 2 := by
    simpa only using
      (Finset.single_le_sum
        (f := fun j : n => (dx j / x j) ^ 2)
        (fun j _ => sq_nonneg (dx j / x j))
        (Finset.mem_univ i))
  linarith

/-- A decrement at most `1` forces each Newton step coordinate to stay below the current point. -/
lemma newton_coordinate_le_current_point
    {n : Type} [Fintype n] [DecidableEq n] (x dx : n → ℝ)
    (hx : ∀ i : n, 0 < x i)
    (hdecr : NewtonDecrement (fun z => Matrix.diagonal (fun i => 1 / (z i) ^ 2)) x dx ≤ 1) :
    ∀ i : n, dx i ≤ x i := by
  intro i
  -- Convert the squared bound into an upper bound on the relative step.
  have hsq_le : (dx i / x i) ^ 2 ≤ 1 := newton_coordinate_sq_le_one x dx hdecr i
  have habs_le : |dx i / x i| ≤ 1 := by
    simpa using (sq_le_one_iff_abs_le_one (dx i / x i)).mp hsq_le
  have hratio_le : dx i / x i ≤ 1 := (abs_le.mp habs_le).2
  have hxpos : 0 < x i := hx i
  have hx_nonzero : x i ≠ 0 := ne_of_gt hxpos
  have hmul_le : (dx i / x i) * x i ≤ 1 * x i := mul_le_mul_of_nonneg_right hratio_le hxpos.le
  simpa [div_eq_mul_inv, hx_nonzero, mul_assoc, mul_comm, mul_left_comm] using hmul_le

theorem scaled_newton_dual_variable_dualFeasible
    {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : PrimalDualLinearProgram m n) (B : LogBarrierSubproblem m n)
    (hstrict_feasible : StrictlyFeasible P.A P.b P.strictly_feasible_point)
    (xhat dx : n → ℝ) (w : m → ℝ)
    (h_base :
      B.base.A = P.A ∧
      B.base.b = P.b ∧
      B.base.c = P.c)
    (hxhat : StrictlyFeasible P.A P.b xhat)
    (hNewton1 :
      (Matrix.diagonal (fun i => 1 / (xhat i) ^ 2)).mulVec dx +
        (Matrix.transpose P.A).mulVec w =
      fun i => - (B.base.t * P.c i - 1 / xhat i))
    (hNewton2 : P.A.mulVec dx = 0)
    (hdecr : NewtonDecrement (fun x => Matrix.diagonal (fun i => 1 / (x i) ^ 2)) xhat dx ≤ 1) :
    DualFeasible P.A P.c (- (1 / B.base.t) • w) := by
  intro i
  -- Route correction: use the decrement bound to show `dx i ≤ xhat i`, then solve the
  -- dual inequality by reading the Newton system in coordinate `i`.
  have hxpos : 0 < xhat i := hxhat.2 i
  have hdx_le : dx i ≤ xhat i := newton_coordinate_le_current_point xhat dx hxhat.2 hdecr i
  have hcoord := congrFun hNewton1 i
  -- Rewrite the Newton equation into an explicit formula for the scaled dual coordinate.
  have hscaled :
      ((Matrix.transpose P.A).mulVec (- (1 / B.base.t) • w)) i =
        P.c i + (dx i - xhat i) / (B.base.t * (xhat i) ^ 2) := by
    have ht_nonzero : B.base.t ≠ 0 := ne_of_gt B.base.t_pos
    have hx_nonzero : xhat i ≠ 0 := ne_of_gt hxpos
    have hcoord' :
        ((Matrix.transpose P.A).mulVec w) i =
          -(B.base.t * P.c i - 1 / xhat i) - dx i / (xhat i) ^ 2 := by
      have hadd :=
        congrArg (fun z : ℝ => z - ((Matrix.diagonal (fun j => 1 / (xhat j) ^ 2)).mulVec dx) i) hcoord
      simpa [sub_eq_add_neg, Matrix.mulVec_diagonal, div_eq_mul_inv, mul_assoc, mul_left_comm,
        mul_comm] using hadd
    calc
      ((Matrix.transpose P.A).mulVec (- (1 / B.base.t) • w)) i
          = -(1 / B.base.t) * (((Matrix.transpose P.A).mulVec w) i) := by
              rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      _ = -(1 / B.base.t) * (-(B.base.t * P.c i - 1 / xhat i) - dx i / (xhat i) ^ 2) := by
            rw [hcoord']
      _ = P.c i + (dx i - xhat i) / (B.base.t * (xhat i) ^ 2) := by
            field_simp [ht_nonzero, hx_nonzero]
            ring
  -- The correction term is nonpositive because both factors in the denominator are positive.
  have hfrac_nonpos : (dx i - xhat i) / (B.base.t * (xhat i) ^ 2) ≤ 0 := by
    have hden_pos : 0 < B.base.t * (xhat i) ^ 2 := by
      exact mul_pos B.base.t_pos (sq_pos_of_pos hxpos)
    have hnum_nonpos : dx i - xhat i ≤ 0 := sub_nonpos.mpr hdx_le
    exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_pos.le
  rw [hscaled]
  linarith

end «problem-84»
