import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-55»

/- [BLOCK Exercise 2.21-(c) | 27 | thm]
Let S^n denote the vector space of all n imes n real symmetric matrices. For X ∈ S^n, let
λ(X)=(λ_1(X),λ_2(X),ldots,λ_n(X)) ∈ ℝ^n denote the vector of eigenvalues of X. For a square matrix
M, let diag(M) ∈ ℝ^n denote the vector of diagonal entries of M. Let V be the set of all n imes n
orthogonal matrices V satisfying Vᵀ V = V Vᵀ = I. A permutation matrix is a matrix obtained by
permuting the rows of the identity matrix. A function f:ℝ^n o ℝ is symmetric if f(x)=f(Px) for every
permutation matrix P and every x ∈ ℝ^n. Let f:ℝ^n o ℝ be symmetric. If f is convex and X∈ S^n, show
that f(λ(X))=sup_{V∈V} figl(diag(Vᵀ X V)igr), where V is the set of n imes n orthogonal matrices.
-/
open Matrix

theorem symmetric_convex_eq_sup_diagonal_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : (n → ℝ) → ℝ)
    (hf_symm : ∀ (e : Equiv.Perm n) (x : n → ℝ), f x = f (fun i => x (e i)))
    (hf_convex : ConvexOn ℝ (Set.univ : Set (n → ℝ)) f)
    (X : Matrix n n ℝ)
    (hX : X.IsSymm)
    (lamX : n → ℝ)
    (hlamX : ∃ V : Matrix n n ℝ,
      V * V.transpose = 1 ∧ V.transpose * V = 1 ∧
      X = V * Matrix.diagonal lamX * V.transpose) :
    f lamX =
      sSup
        {r : ℝ |
          (∃ V : Matrix n n ℝ,
            V * V.transpose = 1 ∧ V.transpose * V = 1 ∧
            r = f (fun i => (V.transpose * X * V) i i)) ∧
          ∀ W : Matrix n n ℝ,
            W * W.transpose = 1 →
            W.transpose * W = 1 →
            f (fun i => (W.transpose * X * W) i i) ≤ r} := by
  sorry

/- [BLOCK Exercise 2.21-(c) | 28 | thm]
Let S^n denote the vector space of all n imes n real symmetric matrices. For X ∈ S^n, let
λ(X)=(λ_1(X),λ_2(X),ldots,λ_n(X)) ∈ ℝ^n denote the vector of eigenvalues of X. For a square matrix
M, let diag(M) ∈ ℝ^n denote the vector of diagonal entries of M. Let V be the set of all n imes n
orthogonal matrices V satisfying Vᵀ V = V Vᵀ = I. A permutation matrix is a matrix obtained by
permuting the rows of the identity matrix. A function f:ℝ^n o ℝ is symmetric if f(x)=f(Px) for every
permutation matrix P and every x ∈ ℝ^n. Let f:ℝ^n o ℝ be symmetric. If f is convex, show further
that the identity f(λ(X))=sup_{V∈V} figl(diag(Vᵀ X V)igr) implies that f(λ(X)) is convex in X.
-/
theorem symmetric_convex_eigenvalue_function_is_convex
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : (n → ℝ) → ℝ)
    (hf_symm : ∀ (e : Equiv.Perm n) (x : n → ℝ), f x = f (fun i => x (e i)))
    (hf_convex : ConvexOn ℝ (Set.univ : Set (n → ℝ)) f)
    (lam : Matrix n n ℝ → n → ℝ)
    (hlam : ∀ X : Matrix n n ℝ, X.IsSymm →
      ∃ V : Matrix n n ℝ,
        V * V.transpose = 1 ∧ V.transpose * V = 1 ∧
        X = V * Matrix.diagonal (lam X) * V.transpose) :
    ConvexOn ℝ
      {X : Matrix n n ℝ | X.IsSymm}
      (fun X => f (lam X)) := by
  sorry

end «problem-55»
