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

/-- The objective is the self dot product of the candidate vector. -/
lemma minimumEuclideanNormProblem_objective_eq_dotProduct_self
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : MinimumEuclideanNormProblem m n) (x : n → ℝ) :
    P.objective x = x ⬝ᵥ x := by
  -- The objective was defined entrywise as the sum of the coordinate squares.
  rfl

/-- For a symmetric matrix, every image vector is orthogonal to every kernel vector. -/
lemma symmetric_mulVec_dotProduct_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : Mᵀ = M) (u v : n → ℝ) (hv : M *ᵥ v = 0) :
    (M *ᵥ u) ⬝ᵥ v = 0 := by
  -- Move the matrix across the dot product using symmetry, then use the kernel hypothesis.
  calc
    (M *ᵥ u) ⬝ᵥ v = v ⬝ᵥ (M *ᵥ u) := by rw [dotProduct_comm]
    _ = (v ᵥ* M) ⬝ᵥ u := by rw [Matrix.dotProduct_mulVec]
    _ = (Mᵀ *ᵥ v) ⬝ᵥ u := by rw [← Matrix.mulVec_transpose]
    _ = (M *ᵥ v) ⬝ᵥ u := by rw [hM]
    _ = 0 := by rw [hv, zero_dotProduct]

/-- Orthogonal vectors add their squared norms without a cross term. -/
lemma minimumEuclideanNormProblem_objective_add_of_orthogonal
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : MinimumEuclideanNormProblem m n) (u v : n → ℝ) (horth : u ⬝ᵥ v = 0) :
    P.objective (u + v) = P.objective u + P.objective v := by
  -- Rewrite the objective as a self dot product and let simplification remove the cross terms.
  rw [minimumEuclideanNormProblem_objective_eq_dotProduct_self (P := P) (x := u + v)]
  rw [minimumEuclideanNormProblem_objective_eq_dotProduct_self (P := P) (x := u)]
  rw [minimumEuclideanNormProblem_objective_eq_dotProduct_self (P := P) (x := v)]
  simp [horth, dotProduct_comm v u]

/-- The minimum-Euclidean-norm objective is always nonnegative. -/
lemma minimumEuclideanNormProblem_objective_nonneg
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : MinimumEuclideanNormProblem m n) (x : n → ℝ) :
    0 ≤ P.objective x := by
  -- Each summand in the objective is a square, hence nonnegative.
  dsimp [MinimumEuclideanNormProblem.objective]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

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
  let P : MinimumEuclideanNormProblem m n := { A := A, b := b }
  change P.isFeasible (X *ᵥ b) ∧ ∀ y, P.isFeasible y → P.objective (X *ᵥ b) ≤ P.objective y
  obtain ⟨x₀, hx₀⟩ := hfeas
  have hAXA : A * X * A = A := hMP_spec.1.1
  have hXA_symm : (X * A)ᵀ = X * A := hMP_spec.1.2.2.2
  have hX_feasible : A *ᵥ (X *ᵥ b) = b := by
    -- The pseudoinverse candidate satisfies the linear constraint because `A * X * A = A`.
    calc
      A *ᵥ (X *ᵥ b) = (A * X) *ᵥ b := by rw [← Matrix.mulVec_mulVec b A X]
      _ = (A * X) *ᵥ (A *ᵥ x₀) := by rw [← hx₀]
      _ = ((A * X) * A) *ᵥ x₀ := by rw [← Matrix.mulVec_mulVec x₀ (A * X) A]
      _ = (A * X * A) *ᵥ x₀ := by rfl
      _ = A *ᵥ x₀ := by rw [hAXA]
      _ = b := hx₀
  constructor
  · -- First show that `X *ᵥ b` is a feasible point of the affine constraint set.
    exact hX_feasible
  · intro y hy
    let z : n → ℝ := y - X *ᵥ b
    have hy' : A *ᵥ y = b := by
      simpa [P, MinimumEuclideanNormProblem.isFeasible] using hy
    have hyX : X *ᵥ b = (X * A) *ᵥ y := by
      -- Replace `b` by `A *ᵥ y` because `y` is another feasible point.
      calc
        X *ᵥ b = X *ᵥ (A *ᵥ y) := by rw [← hy']
        _ = (X * A) *ᵥ y := by rw [← Matrix.mulVec_mulVec y X A]
    have hz_kernel : A *ᵥ z = 0 := by
      -- The difference of two feasible points lies in the kernel of `A`.
      calc
        A *ᵥ z = A *ᵥ y - A *ᵥ (X *ᵥ b) := by
          simp [z, Matrix.mulVec_sub]
        _ = b - b := by rw [hy', hX_feasible]
        _ = 0 := by simp
    have hz_projected : (X * A) *ᵥ z = 0 := by
      -- Applying `X` to a kernel vector of `A` still gives zero after multiplication by `X * A`.
      rw [← Matrix.mulVec_mulVec z X A, hz_kernel, Matrix.mulVec_zero]
    have horth : (X *ᵥ b) ⬝ᵥ z = 0 := by
      -- Symmetry of `X * A` turns the kernel statement into orthogonality.
      rw [hyX]
      exact symmetric_mulVec_dotProduct_eq_zero (M := X * A) hXA_symm y z hz_projected
    have hy_decomp : y = X *ᵥ b + z := by
      -- Decompose every feasible point into the canonical candidate plus a kernel part.
      ext i
      simp [z]
    have hy_objective :
        P.objective y = P.objective (X *ᵥ b) + P.objective z := by
      -- Orthogonality removes the cross term in the quadratic objective.
      rw [hy_decomp]
      exact minimumEuclideanNormProblem_objective_add_of_orthogonal
        (P := P) (u := X *ᵥ b) (v := z) horth
    have hz_nonneg : 0 ≤ P.objective z :=
      minimumEuclideanNormProblem_objective_nonneg (P := P) (x := z)
    -- The remaining term is nonnegative, so the pseudoinverse candidate has minimal objective value.
    calc
      P.objective (X *ᵥ b) ≤ P.objective (X *ᵥ b) + P.objective z :=
        le_add_of_nonneg_right hz_nonneg
      _ = P.objective y := by symm; exact hy_objective
end «problem-2»
