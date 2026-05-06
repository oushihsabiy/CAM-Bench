import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-2»
/-
For A ∈ ℝ^(m × n), the Moore - - Penrose pseudoinverse A^† is the unique matrix X ∈ ℝ^(n × m) such
that
AXA = A, XAX = X, (AX)^T = AX, and (XA)^T = XA.
-/
def IsMoorePenrosePseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (X : Matrix n m ℝ) : Prop :=
  (A * X * A = A ∧
    X * A * X = X ∧
    (A * X)ᵀ = A * X ∧
    (X * A)ᵀ = X * A) ∧
    ∀ Y : Matrix n m ℝ,
      (A * Y * A = A ∧
        Y * A * Y = Y ∧
        (A * Y)ᵀ = A * Y ∧
        (Y * A)ᵀ = Y * A) → Y = X

def moorePenrosePseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : Matrix n m ℝ :=
  by
    classical
    exact
      if h : ∃ X : Matrix n m ℝ, IsMoorePenrosePseudoinverse A X then
        Classical.choose h
      else
        0



/-
Let A ∈ ℝ^(m × n) and b ∈ ℝ^m. Consider the optimization problem

min_(x ∈ ℝ^n) ‖x‖_2 s. t. Ax = b.
-/
structure MinimumEuclideanNormProblem (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] where
  A : Matrix m n ℝ
  b : m → ℝ

def MinimumEuclideanNormProblem.isFeasible {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (P : MinimumEuclideanNormProblem m n) (x : n → ℝ) : Prop :=
  P.A.mulVec x = P.b

def MinimumEuclideanNormProblem.objective {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (_ : MinimumEuclideanNormProblem m n) (x : n → ℝ) : ℝ :=
  ∑ i : n, x i * x i

def MinimumEuclideanNormProblem.solutionSet {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (P : MinimumEuclideanNormProblem m n) : Set (n → ℝ) :=
  {x | P.isFeasible x ∧ ∀ y, P.isFeasible y → P.objective x ≤ P.objective y}

/-
Let A ∈ ℝ^(m × n) and b ∈ ℝ^m, and consider the minimum Euclidean norm problem:

min_(x ∈ ℝ^n) ‖x ‖_2 s. t. Ax = b.

Here, ‖x‖_2 denotes the Euclidean norm of the vector x, and A^† denotes the Moore - - Penrose
pseudoinverse of the matrix A.

It is known that the linear constraint equation Ax = b is feasible, that is, there exists x ∈ ℝ^n
such that Ax = b. Prove that the optimal solution to this optimization problem can be written
explicitly as x^* = A^†b, and explain that this solution is precisely the one with the smallest
Euclidean norm among all solutions satisfying the constraint Ax = b.
-/
theorem minimumEuclideanNormProblem_solution_eq_pseudoinverse_mul
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (b : m → ℝ) (X : Matrix n m ℝ)
    (hMP : X = moorePenrosePseudoinverse A)
    (hMP_spec : IsMoorePenrosePseudoinverse A X)
    (hfeas : ∃ x : n → ℝ, A.mulVec x = b) :
    X.mulVec b ∈ (MinimumEuclideanNormProblem.solutionSet
      { A := A, b := b } : Set (n → ℝ)) := by
  sorry
end «problem-2»
