import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-126»
/-
A linear program is an optimization problem of the form (min {c^T x mid Gx le h, Ex = d});
equivalently, it has a linear objective function and linear equality and inequality constraints.
-/
structure LinearProgram (m n p : ℕ) where
  c : Fin n → ℝ
  G : Matrix (Fin m) (Fin n) ℝ
  h : Fin m → ℝ
  E : Matrix (Fin p) (Fin n) ℝ
  d : Fin p → ℝ

def LinearProgram.objective {m n p : ℕ} (P : LinearProgram m n p) (x : Fin n → ℝ) : ℝ :=
  dotProduct P.c x

def LinearProgram.IsFeasible {m n p : ℕ} (P : LinearProgram m n p) (x : Fin n → ℝ) : Prop :=
  (∀ i : Fin m, (P.G.mulVec x) i ≤ P.h i) ∧ (P.E.mulVec x = P.d)

def ComponentwiseGE {m : ℕ} (u v : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, v i ≤ u i

/-
For primal inequality constraints (Ax ge b) with dual variable (y ge 0), complementary slackness
means that (y_i (Ax - b)_i = 0) for every (i); equivalently, (y^T(Ax - b) = 0).
-/
def ComplementarySlackness {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (b y : Fin m → ℝ) : Prop :=
  (∀ i : Fin m, 0 ≤ y i) ∧ ∀ i : Fin m, y i * ((A.mulVec x) i - b i) = 0

/-
For the dual of (min {c^T x mid Ax ge b}), a vector (y in mathbf{R}^m) is dual feasible if (y ge
0) and (A^T y = c).
-/
def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  ComponentwiseGE (A.mulVec x) b

/-
Consider the linear program, with unknown cost vector (c in mathbf{R}^n), [ begin{} text{minimize}
& c^T x text{subject to} & Ax ge b, end{} ] where the decision variable is (x in mathbf{R}^n), and
the inequalities are understood componentwise.
-/
structure LinearProgramWithUnknownCost (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def LinearProgramWithUnknownCost.isFeasible {m n : ℕ} (P : LinearProgramWithUnknownCost m n)
    (x : Fin n → ℝ) : Prop :=
  PrimalFeasible P.A P.b x

def LinearProgramWithUnknownCost.objective {m n : ℕ} (_P : LinearProgramWithUnknownCost m n)
    (c x : Fin n → ℝ) : ℝ :=
  dotProduct c x

/-
Let (A in mathbf{R}^{m \times n}) be given. For each (j = 1, ..., r), let (b^{(j)} in mathbf{R}^m)
and (x^{(j)} in mathbf{R}^n). Consider the linear program with unknown cost. Prove that there
exists a vector (c in mathbf{R}^n) such that, for every (j = 1, ..., r), the point (x^{(j)}) is an
optimal solution of the above linear program with (b = b^{(j)}) if and only if there exist vectors
(y^{(1)}, ..., y^{(r)} in mathbf{R}^m) such that: [ Ax^{(j)} ge b^{(j)}, y^{(j)} ge 0, A^T y^{(j)} =
A^T y^{(1)} (j = 1, ..., r), ] and [ big(y^{(j)} big)^T big(Ax^{(j)} - b^{(j)} big) = 0 (j = 1, ...,
r).
]
-/
theorem exists_common_cost_vector_iff_exists_dual_certificates
    {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin r → Fin m → ℝ) (x : Fin r → Fin n → ℝ) :
    (∃ c : Fin n → ℝ,
      ∀ j : Fin r,
        PrimalFeasible A (b j) (x j) ∧
        ∀ z : Fin n → ℝ, PrimalFeasible A (b j) z → dotProduct c (x j) ≤ dotProduct c z) ↔
    ∃ y : Fin r → Fin m → ℝ,
      (∀ j : Fin r, PrimalFeasible A (b j) (x j)) ∧
      (∀ j : Fin r, ComponentwiseGE (y j) 0) ∧
      (∀ j1 j2 : Fin r, A.transpose.mulVec (y j1) = A.transpose.mulVec (y j2)) ∧
      (∀ j : Fin r, ComplementarySlackness A (x j) (b j) (y j)) := by
  sorry

end «problem-126»
