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
  sorry

end «problem-84»
