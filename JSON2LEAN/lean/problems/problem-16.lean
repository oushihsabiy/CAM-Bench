import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-16»
/-
A matrix A ∈ ℝ^m × n has full row rank if rank(A) = m; equivalently, its rows are linearly
independent.
-/
def HasFullRowRank {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : Prop :=
  Matrix.rank A = Fintype.card m

/-
Let G ∈ ℝ^n×n, A ∈ ℝ^m × n, c ∈ ℝ^n, and b ∈ ℝ^m. Consider the equality - constrained quadratic
program min_x ∈ ℝ^n ((1)/(2) xᵀ G x + xᵀ c) subject to Ax = b.
-/
structure EqualityConstrainedQuadraticProgram
    (m n : Type*) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] where
  G : Matrix n n ℝ
  G_symm : G.IsSymm
  A : Matrix m n ℝ
  c : n → ℝ
  b : m → ℝ

def EqualityConstrainedQuadraticProgram.isFeasible
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : EqualityConstrainedQuadraticProgram m n) (x : n → ℝ) : Prop :=
  P.A.mulVec x = P.b

def EqualityConstrainedQuadraticProgram.objective
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : EqualityConstrainedQuadraticProgram m n) (x : n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (P.G.mulVec x) + dotProduct x P.c

/-
Let G ∈ ℝ^{n×n}, A ∈ ℝ^{m × n}, c ∈ ℝ^n, and b ∈ ℝ^m. Consider the equality - constrained quadratic
program min_{x ∈ ℝ^n} ((1)/(2) xᵀ G x + xᵀ c) subject to Ax = b. Assume that A has full row rank,
and let Z ∈ ℝ^{n × (n - m)} have columns forming a basis of the null space of A, so AZ = 0. Suppose
there exists u ∈ ℝ^{n - m} such that uᵀ Zᵀ G Zu < 0. Assume also that there exists (x*, λ^*) ∈ ℝ^n ×
ℝ^m such that [ G & - Aᵀ; A & 0 ] [ x*; λ^* ] = [ - c; b ]. Show that x* is a stationary point of
this
problem but not a local minimizer.
-/
theorem stationary_but_not_local_minimizer_of_negative_reduced_hessian
    {m n k : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (P : EqualityConstrainedQuadraticProgram m n)
    (hGsymm : P.G.IsSymm)
    (hfull : HasFullRowRank P.A)
    (Z : Matrix n k ℝ)
    (hAZ : P.A * Z = 0)
    (hZspan : ∀ d : n → ℝ, P.A.mulVec d = 0 → ∃ v : k → ℝ, Z.mulVec v = d)
    (u : k → ℝ)
    (hZu_ne_zero : Z.mulVec u ≠ 0)
    (hneg : dotProduct u ((Z.transpose * P.G * Z).mulVec u) < 0)
    (xstar : n → ℝ)
    (lambdastar : m → ℝ)
    (hkkt₁ : P.G.mulVec xstar - P.A.transpose.mulVec lambdastar = fun i => -P.c i)
    (hkkt₂ : P.A.mulVec xstar = P.b) :
    P.isFeasible xstar ∧
      (∀ d : n → ℝ, P.A.mulVec d = 0 →
        dotProduct d (P.G.mulVec xstar) + dotProduct d P.c = 0) ∧
      ¬IsLocalMinOn P.objective {x | P.isFeasible x} xstar := by
  sorry

end «problem-16»
