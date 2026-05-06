import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-111»

/- [BLOCK Exercise 4.47-(c) | 11 | defn]
Given a partial symmetric matrix A, a completion is a symmetric matrix X that agrees with A on every
specified entry.
-/
def IsCompletion {n : Type*} (specified : Set (n × n)) (A X : Matrix n n ℝ) : Prop :=
  X.IsSymm ∧ ∀ ⦃i j : n⦄, (i, j) ∈ specified → X i j = A i j

/- [BLOCK Exercise 4.47-(c) | 12 | defn]
A positive definite completion of a partial symmetric matrix A is a completion X that is positive
definite.
-/
def IsPosDefCompletion {n : Type*} [Fintype n] [DecidableEq n]
    (specified : Set (n × n)) (A X : Matrix n n ℝ) : Prop :=
  IsCompletion specified A X ∧ X.PosDef

/- [BLOCK Exercise 4.47-(c) | 13 | defn]
A maximum-determinant completion of a partial symmetric matrix A is a positive definite completion X
whose determinant is at least the determinant of every other positive definite completion of A.
-/
def IsMaxDetCompletion {n : Type*} [Fintype n] [DecidableEq n]
    (specified : Set (n × n)) (A X : Matrix n n ℝ) : Prop :=
  IsPosDefCompletion specified A X ∧
    ∀ Y : Matrix n n ℝ, IsPosDefCompletion specified A Y → Y.det ≤ X.det

/- [BLOCK Exercise 4.47-(c) | 14 | thm]
Let A be a partial real symmetric matrix with symmetric specified pattern and all diagonal entries
specified. Assume A has at least one positive definite completion. Prove that the positive definite
completion with maximum determinant is unique.
-/
theorem maxDetCompletion_unique
    {n : Type*} [Fintype n] [DecidableEq n]
    (specified : Set (n × n)) (A : Matrix n n ℝ)
    (hA : A.IsSymm)
    (hspecified_symm : ∀ ⦃i j : n⦄, (i, j) ∈ specified ↔ (j, i) ∈ specified)
    (hdiag : ∀ i : n, (i, i) ∈ specified)
    (hex : ∃ X : Matrix n n ℝ, IsPosDefCompletion specified A X) :
    ∃! X : Matrix n n ℝ, IsMaxDetCompletion specified A X := by
  sorry

/- [BLOCK Exercise 4.47-(c) | 15 | thm]
With the same setup, let A* be the maximum-determinant positive definite completion. Prove that the
inverse matrix (A*)^{-1} has zero entries at every position that was unspecified in the original
partial matrix.
-/
theorem maxDetCompletion_inv_eq_zero_of_unspecified
    {n : Type*} [Fintype n] [DecidableEq n]
    (specified : Set (n × n)) (A : Matrix n n ℝ)
    (hA : A.IsSymm)
    (hspecified_symm : ∀ ⦃i j : n⦄, (i, j) ∈ specified ↔ (j, i) ∈ specified)
    (hdiag : ∀ i : n, (i, i) ∈ specified)
    (hex : ∃ X : Matrix n n ℝ, IsPosDefCompletion specified A X) :
    ∀ ⦃Astar : Matrix n n ℝ⦄,
      IsMaxDetCompletion specified A Astar →
      ∀ ⦃i j : n⦄, (i, j) ∉ specified → Astar⁻¹ i j = 0 := by
  sorry

end «problem-111»
