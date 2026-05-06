import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-148»
/-
The robust quadratic program minimize & sup_{P ∈ E} ((1)/(2) xᵀ P x + qᵀ x + r); ;
subject to & Ax preceq b array is exactly equivalent to the quadratic program minimize &
(1)/(2) xᵀ (P₀ + γ I) x + qᵀ x + r; ; subject to & Ax preceq b. array
-/
structure RobustQuadraticProgram
    (m : Type*)
    (n : Type*)
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n] where
  uncertaintySet : Set (Matrix n n ℝ)
  P0 : Matrix n n ℝ
  γ : ℝ
  q : n → ℝ
  r : ℝ
  A : Matrix m n ℝ
  b : m → ℝ

def RobustQuadraticProgram.feasible
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    (x : n → ℝ) : Prop :=
  ∀ i, (p.A.mulVec x) i ≤ p.b i

def RobustQuadraticProgram.quadraticValue
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    (P : Matrix n n ℝ)
    (x : n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (P.mulVec x) + dotProduct p.q x + p.r

def RobustQuadraticProgram.robustObjective
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    (x : n → ℝ) : ℝ :=
  sSup ((fun P : Matrix n n ℝ => p.quadraticValue P x) '' p.uncertaintySet)

def RobustQuadraticProgram.equivalentObjective
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    (x : n → ℝ) : ℝ :=
  p.quadraticValue (p.P0 + p.γ • (1 : Matrix n n ℝ)) x

/-
Let x ∈ ℝ^n be the decision variable. Given q ∈ ℝ^n, r ∈ ℝ, A ∈ ℝ^{m \times n}, b ∈ ℝ^m, P₀ ∈ S_ +
^n,
and γ ≥ 0, consider the uncertainty set E = {P ∈ S^n | - γ I preceq P - P₀ preceq γ I}, where S^n is
the set of n \times n real symmetric matrices, S_ + ^n is the cone of symmetric positive
semidefinite
matrices, I is the n \times n identity matrix, and for symmetric matrices X preceq Y means Y - X ∈
S_ + ^n. The inequality Ax preceq b means a_iᵀ x ≤ bᵢ for i = 1, ..., m. Prove that for every x ∈
ℝ^n,
sup_{P ∈ E} (\frac{1}{2} xᵀ P x + qᵀ x + r ight) = \frac{1}{2} xᵀ (P₀ + γ I) x + qᵀ x + r.
-/
theorem robust_quadratic_objective_eq_equivalentObjective
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    [Nonempty n]
    (hP0symm : p.P0.IsSymm)
    (hP0psd : ∀ y : n → ℝ, 0 ≤ dotProduct y (p.P0.mulVec y))
    (hγ : 0 ≤ p.γ)
    (hunc :
      p.uncertaintySet =
        {P : Matrix n n ℝ |
          P.IsSymm ∧
          ∀ y : n → ℝ,
            -p.γ * dotProduct y y ≤ dotProduct y ((P - p.P0).mulVec y) ∧
            dotProduct y ((P - p.P0).mulVec y) ≤ p.γ * dotProduct y y})
    (x : n → ℝ) :
    p.robustObjective x = p.equivalentObjective x := by
  sorry

/-
Let x ∈ ℝ^n be the decision variable. Given q ∈ ℝ^n, r ∈ ℝ, A ∈ ℝ^{m \times n}, b ∈ ℝ^m, P₀ ∈ S_ +
^n,
and γ ≥ 0, consider the uncertainty set E = {P ∈ S^n | - γ I preceq P - P₀ preceq γ I}, where S^n is
the set of n \times n real symmetric matrices, S_ + ^n is the cone of symmetric positive
semidefinite
matrices, I is the n \times n identity matrix, and for symmetric matrices X preceq Y means Y - X ∈
S_ + ^n. The inequality Ax preceq b means a_iᵀ x ≤ bᵢ for i = 1, ..., m. Hence prove that robust
quadratic program so in particular it is a convex QP.
-/
theorem robust_quadratic_program_equivalent_on_feasible_set
    {m n : Type*}
    [Fintype m]
    [DecidableEq m]
    [Fintype n]
    [DecidableEq n]
    (p : RobustQuadraticProgram m n)
    [Nonempty n]
    (hP0symm : p.P0.IsSymm)
    (hP0psd : ∀ y : n → ℝ, 0 ≤ dotProduct y (p.P0.mulVec y))
    (hγ : 0 ≤ p.γ)
    (hunc :
      p.uncertaintySet =
        {P : Matrix n n ℝ |
          P.IsSymm ∧
          ∀ y : n → ℝ,
            -p.γ * dotProduct y y ≤ dotProduct y ((P - p.P0).mulVec y) ∧
            dotProduct y ((P - p.P0).mulVec y) ≤ p.γ * dotProduct y y}) :
    (∀ x : n → ℝ, p.feasible x → p.robustObjective x = p.equivalentObjective x) ∧
    (∀ y : n → ℝ,
      0 ≤ dotProduct y (((p.P0 + p.γ • (1 : Matrix n n ℝ)).mulVec y))) := by
  sorry

end «problem-148»
