import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-132»

-- Exercise_7_17__b_

/- [BLOCK Exercise 7.17-(b) | 18 | defn]
For a set C ⊆ ℝ^n, its polar is defined by
C^circ = {x ∈ ℝ^n | uᵀ x ≤ 1 for all u ∈ C}.
-/
def polar (C : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ u ∈ C, ∑ i, u i * x i ≤ 1}

/- [BLOCK Exercise 7.17-(b) | 19 | defn]
A set C ⊆ ℝ^n is a polyhedron if there exist A ∈ ℝ^m × n and b ∈ ℝ^m such that
C = {x ∈ ℝ^n | Ax ≤ b},
where the inequality is componentwise.
-/
def IsPolyhedron (C : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    C = {x | ∀ i, ∑ j, A i j * x j ≤ b i}

/- [BLOCK Exercise 7.17-(b) | 20 | defn]
A quadratic program is an optimization problem of the form
min_x tfrac12 xᵀ Q x + cᵀ x + r
subject to finitely many affine equality and affine inequality constraints, where Q is symmetric.
-/
structure QuadraticProgram where
  n : ℕ
  meq : ℕ
  mineq : ℕ
  Q : Fin n → Fin n → ℝ
  c : Fin n → ℝ
  r : ℝ
  Aeq : Fin meq → Fin n → ℝ
  beq : Fin meq → ℝ
  Aineq : Fin mineq → Fin n → ℝ
  bineq : Fin mineq → ℝ
  Q_symm : Matrix.IsSymm Q

def QuadraticProgram.objective (P : QuadraticProgram) (x : Fin P.n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, x i * P.Q i j * x j) + (∑ i, P.c i * x i) + P.r

def QuadraticProgram.eqFeasible (P : QuadraticProgram) (x : Fin P.n → ℝ) : Prop :=
  ∀ i, ∑ j, P.Aeq i j * x j = P.beq i

def QuadraticProgram.ineqFeasible (P : QuadraticProgram) (x : Fin P.n → ℝ) : Prop :=
  ∀ i, ∑ j, P.Aineq i j * x j ≤ P.bineq i

def QuadraticProgram.FeasibleSet (P : QuadraticProgram) : Set (Fin P.n → ℝ) :=
  {x | QuadraticProgram.eqFeasible P x ∧ QuadraticProgram.ineqFeasible P x}

/- [BLOCK Exercise 7.17-(b) | 21 | opt_prob]
array{ll}
minimize & ‖x₁-x₂‖_2^2 ;
subject\ to & x₁ ∈ C₁^circ, ;
& x₂ ∈ C₂^circ
array
with variables x₁, x₂ ∈ ℝ^n.
-/
structure PolarDistanceMinimization where
  n : ℕ
  C₁ : Set (Fin n → ℝ)
  C₂ : Set (Fin n → ℝ)

def PolarDistanceMinimization.isFeasible
    (P : PolarDistanceMinimization) (x₁ x₂ : Fin P.n → ℝ) : Prop :=
  x₁ ∈ polar P.C₁ ∧ x₂ ∈ polar P.C₂

def PolarDistanceMinimization.objective
    (P : PolarDistanceMinimization) (x₁ x₂ : Fin P.n → ℝ) : ℝ :=
  ∑ i, (x₁ i - x₂ i) ^ 2

def PolarDistanceMinimization.feasibleSet
    (P : PolarDistanceMinimization) : Set ((Fin P.n → ℝ) × (Fin P.n → ℝ)) :=
  {(x₁, x₂) | P.isFeasible x₁ x₂}

/- [BLOCK Exercise 7.17-(b) | 22 | opt_prob]
array{ll}
minimize & ‖x₁-x₂‖_2^2 ;
subject\ to & A_1ᵀ λ_1 = x₁, ;
& b_1ᵀ λ_1 ≤ 1, ;
& λ_1 succeq 0, ;
& A_2ᵀ λ_2 = x₂, ;
& b_2ᵀ λ_2 ≤ 1, ;
& λ_2 succeq 0
array
with variables x₁, x₂ ∈ ℝ^n, λ_1 ∈ ℝ^m₁, and λ_2 ∈ ℝ^m₂.
-/
structure PolarDistanceQP where
  n : ℕ
  m₁ : ℕ
  m₂ : ℕ
  A₁ : Fin m₁ → Fin n → ℝ
  b₁ : Fin m₁ → ℝ
  A₂ : Fin m₂ → Fin n → ℝ
  b₂ : Fin m₂ → ℝ

def PolarDistanceQP.isFeasible
    (P : PolarDistanceQP)
    (x₁ x₂ : Fin P.n → ℝ)
    (lam₁ : Fin P.m₁ → ℝ)
    (lam₂ : Fin P.m₂ → ℝ) : Prop :=
  (∀ i, ∑ j, P.A₁ j i * lam₁ j = x₁ i) ∧
  (∑ j, P.b₁ j * lam₁ j ≤ 1) ∧
  (∀ j, 0 ≤ lam₁ j) ∧
  (∀ i, ∑ j, P.A₂ j i * lam₂ j = x₂ i) ∧
  (∑ j, P.b₂ j * lam₂ j ≤ 1) ∧
  (∀ j, 0 ≤ lam₂ j)

def PolarDistanceQP.objective
    (P : PolarDistanceQP) (x₁ x₂ : Fin P.n → ℝ) : ℝ :=
  ∑ i, (x₁ i - x₂ i) ^ 2

def PolarDistanceQP.feasibleSet
    (P : PolarDistanceQP) :
    Set ((Fin P.n → ℝ) × (Fin P.n → ℝ) × (Fin P.m₁ → ℝ) × (Fin P.m₂ → ℝ)) :=
  {y | P.isFeasible y.1 y.2.1 y.2.2.1 y.2.2.2}

/- [BLOCK Exercise 7.17-(b) | 23 | thm]
Let the polar of a set C ⊆ ℝ^n be defined by C^{circ}={x ∈ ℝ^n | uᵀ x ≤ 1 for all u ∈ C}. Let C₁={u
∈ ℝ^n | A_1u ≤ b₁} and C₂={v ∈ ℝ^n | A_2v ≤ b₂}, where C₁ and C₂ are nonempty polyhedra, A₁ ∈ ℝ^{m₁
× n}, A₂ ∈ ℝ^{m₂ × n}, b₁ ∈ ℝ^{m₁}, and b₂ ∈ ℝ^{m₂}, and the inequalities are componentwise. Prove
that the optimization problem polar distance minimization is equivalent to the quadratic program
quadratic program reformulation.
-/
theorem polar_distance_minimization_equivalent_to_quadratic_program_reformulation
    (n m₁ m₂ : ℕ)
    (A₁ : Fin m₁ → Fin n → ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Fin m₂ → Fin n → ℝ)
    (b₂ : Fin m₂ → ℝ)
    (hC₁ :
      {u : Fin n → ℝ | ∀ i, ∑ j, A₁ i j * u j ≤ b₁ i} ≠ (∅ : Set (Fin n → ℝ)))
    (hC₂ :
      {v : Fin n → ℝ | ∀ i, ∑ j, A₂ i j * v j ≤ b₂ i} ≠ (∅ : Set (Fin n → ℝ))) :
    let P : PolarDistanceMinimization := {
      n := n
      C₁ := {u : Fin n → ℝ | ∀ i, ∑ j, A₁ i j * u j ≤ b₁ i}
      C₂ := {v : Fin n → ℝ | ∀ i, ∑ j, A₂ i j * v j ≤ b₂ i}
    }
    let QP : PolarDistanceQP := {
      n := n
      m₁ := m₁
      m₂ := m₂
      A₁ := A₁
      b₁ := b₁
      A₂ := A₂
      b₂ := b₂
    }
    ∀ x₁ x₂ : Fin n → ℝ,
      P.isFeasible x₁ x₂ ↔
        ∃ lam₁ : Fin m₁ → ℝ, ∃ lam₂ : Fin m₂ → ℝ,
          QP.isFeasible x₁ x₂ lam₁ lam₂ := by
  sorry

end «problem-132»