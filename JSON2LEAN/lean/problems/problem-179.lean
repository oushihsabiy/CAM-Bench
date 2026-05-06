import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-179»

/- [BLOCK Exercise 16.15 | 18 | opt_prob]
Consider the problem
min_{x ∈ ℝ^n} q(x) = (1)/(2)xᵀ G x + xᵀ c
subject to
Ax = b,
where G ∈ ℝ^{n×n}, c ∈ ℝ^n, A ∈ ℝ^{m × n}, and b ∈ ℝ^m. Assume that A has full row rank, that there
exists at least one x ∈ ℝ^n such that Ax=b, and that Z ∈ ℝ^{n × (n-m)} has columns forming a basis
for the null space of A, so that
N(A)={d ∈ ℝ^n : Ad=0}={Zp : p ∈ ℝ^{n-m}}.
-/
structure EqualityConstrainedQuadraticProgram where
  n : ℕ
  m : ℕ
  G : Matrix (Fin n) (Fin n) ℝ
  c : Fin n → ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  Z : Matrix (Fin n) (Fin (n - m)) ℝ
  full_row_rank : Function.Surjective A.toLin'
  feasible : ∃ x : Fin n → ℝ, A.mulVec x = b
  nullspace_parametrization : ∀ d : Fin n → ℝ, A.mulVec d = 0 ↔ ∃ p : Fin (n - m) → ℝ, Z.mulVec p = d

def EqualityConstrainedQuadraticProgram.objective
    (P : EqualityConstrainedQuadraticProgram) (x : Fin P.n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (P.G.mulVec x) + dotProduct x P.c

def EqualityConstrainedQuadraticProgram.isFeasible
    (P : EqualityConstrainedQuadraticProgram) (x : Fin P.n → ℝ) : Prop :=
  P.A.mulVec x = P.b

/- [BLOCK Exercise 16.15 | 19 | thm]
Consider the equality-constrained quadratic program. Prove that this optimization problem has no
finite solution if the matrix Zᵀ G Z has a negative eigenvalue.
-/
theorem EqualityConstrainedQuadraticProgram.no_finite_solution_of_exists_negative_direction
    (P : EqualityConstrainedQuadraticProgram)
    (hneg :
      ∃ p : Fin (P.n - P.m) → ℝ,
        dotProduct p ((P.Z.transpose.mulVec) (P.G.mulVec (P.Z.mulVec p))) < 0) :
    ∀ x : Fin P.n → ℝ, P.isFeasible x →
      ∃ y : Fin P.n → ℝ, P.isFeasible y ∧ P.objective y < P.objective x := by
  sorry

end «problem-179»
