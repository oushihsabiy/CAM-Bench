import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-154»

/- [BLOCK Exercise 16.4 | 5 | defn]
For a feasible point x with equality-index set E and inequality-index set I, the active set is
A(x)=Ecup{i∈I:a_iᵀ x=bᵢ}.
It consists of all equality constraints and all inequality constraints that are active at x.
-/
def activeSet {ι : Type*} (equalities inequalities : Set ι) (a : ι → Fin n → ℝ) (b : ι → ℝ)
    (x : Fin n → ℝ) : Set ι :=
  equalities ∪ {i | i ∈ inequalities ∧ ∑ j, a i j * x j = b i}

/- [BLOCK Exercise 16.4 | 6 | defn]
A point x is feasible if it satisfies all constraints of the problem, that is, a_iᵀ x=bᵢ for all i∈E
and a_iᵀ x≥ bᵢ for all i∈I.
-/
def feasiblePoint {n : ℕ} {ι : Type*} (equalities inequalities : Set ι) (a : ι → Fin n → ℝ)
    (b : ι → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i, i ∈ equalities → ∑ j, a i j * x j = b i) ∧
    ∀ i, i ∈ inequalities → ∑ j, a i j * x j ≥ b i

/- [BLOCK Exercise 16.4 | 7 | defn]
A multiplier for a constraint system is a scalar coefficient λ_i associated with constraint i. A
vector of multipliers appears in first-order optimality conditions through a linear combination of
the constraint normals, for example,
∇ f(x)-sum_i λ_i aᵢ=0.
-/
def multiplier (ι : Type*) := ι → ℝ

/- [BLOCK Exercise 16.4 | 8 | defn]
A feasible point x* is a global solution if f(x*)≤ f(x) for every feasible x. It is unique if,
moreover, f(x*)< f(x) for every feasible xne x*.
-/
def isGlobalSolution {n : ℕ} {ι : Type*} (f : (Fin n → ℝ) → ℝ) (equalities inequalities : Set ι)
    (a : ι → Fin n → ℝ) (b : ι → ℝ) (xStar : Fin n → ℝ) : Prop :=
  feasiblePoint equalities inequalities a b xStar ∧
    ∀ x, feasiblePoint equalities inequalities a b x → f xStar ≤ f x

def isUniqueGlobalSolution {n : ℕ} {ι : Type*} (f : (Fin n → ℝ) → ℝ) (equalities inequalities : Set ι)
    (a : ι → Fin n → ℝ) (b : ι → ℝ) (xStar : Fin n → ℝ) : Prop :=
  feasiblePoint equalities inequalities a b xStar ∧
    ∀ x, feasiblePoint equalities inequalities a b x → x ≠ xStar → f xStar < f x

/- [BLOCK Exercise 16.4 | 9 | opt_prob]
Consider the quadratic program
aligned
min_{x ∈ ℝ^n} quad & q(x)=(1)/(2)xᵀ G x + cᵀ x ;
subject to quad & a_iᵀ x = bᵢ, quad i ∈ E, ;
& a_iᵀ x ≥ bᵢ, quad i ∈ I,
aligned
where G ∈ ℝ^{n×n} is symmetric positive semidefinite, c ∈ ℝ^n, and aᵢ ∈ ℝ^n, bᵢ ∈ ℝ for each i ∈ E
cup I.
-/
structure ConvexQuadraticProgram (n : ℕ) (ι : Type*) where
  G : Matrix (Fin n) (Fin n) ℝ
  c : Fin n → ℝ
  equalities : Set ι
  inequalities : Set ι
  a : ι → Fin n → ℝ
  b : ι → ℝ
  G_symmetric : G.IsSymm
  G_posSemidef : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, x i * G i j * x j

def ConvexQuadraticProgram.objective {n : ℕ} {ι : Type*} (P : ConvexQuadraticProgram n ι)
    (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, x i * P.G i j * x j + ∑ i, P.c i * x i

def ConvexQuadraticProgram.isFeasible {n : ℕ} {ι : Type*} (P : ConvexQuadraticProgram n ι)
    (x : Fin n → ℝ) : Prop :=
  feasiblePoint P.equalities P.inequalities P.a P.b x

def ConvexQuadraticProgram.activeSet {n : ℕ} {ι : Type*} (P : ConvexQuadraticProgram n ι)
    (x : Fin n → ℝ) : Set ι :=
  {i | i ∈ P.inequalities ∧ ∑ j, P.a i j * x j = P.b i}

/- [BLOCK Exercise 16.4 | 10 | thm]
Consider the convex quadratic program. Let x* be a feasible point, and define its active set by
A(x*) = E cup { i ∈ I : a_iᵀ x* = bᵢ }. Assume there exist multipliers λ_i* ∈ ℝ for i ∈ A(x*) such
that
Gx* + c - sum_{i ∈ A(x*)} λ_i* aᵢ = 0,
a_iᵀ x* = bᵢ quad for all i ∈ A(x*).
Let A_{A(x*)} be the matrix whose rows are a_iᵀ for i ∈ A(x*), and let the columns of Z form a basis
of
{ d ∈ ℝ^n : A_{A(x*)} d = 0 }.
Assume that Zᵀ G Z is positive definite. Show that x* is the unique global solution of the quadratic
program, namely,
q(x) > q(x*) quad for every feasible x ≠ x*.
-/
theorem unique_global_solution_of_kkt_activeSet_posDef
    {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : ConvexQuadraticProgram n ι) (xStar : Fin n → ℝ) (Z : κ → Fin n → ℝ)
    (lam : multiplier ι)
    (hxFeas : P.isFeasible xStar)
    (hlam_support : ∀ i, i ∉ activeSet P.equalities P.inequalities P.a P.b xStar → lam i = 0)
    (hlam_active_ineq_pos :
      ∀ i, i ∈ P.inequalities →
        i ∈ activeSet P.equalities P.inequalities P.a P.b xStar →
          0 < lam i)
    (hstationary :
      ∀ j, ∑ i, lam i * P.a i j = ∑ k, P.G j k * xStar k + P.c j)
    (hactive_eq :
      ∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar → ∑ j, P.a i j * xStar j = P.b i)
    (hZbasis :
      (∀ d : Fin n → ℝ,
        (∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar → ∑ j, P.a i j * d j = 0) →
        ∃ mu : κ → ℝ, d = fun j => ∑ i, Z i j * mu i) ∧
      (∀ mu : κ → ℝ,
        ∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar →
          ∑ j, P.a i j * (∑ k, Z k j * mu k) = 0) ∧
      (∀ mu : κ → ℝ,
        (∀ j, (∑ i, Z i j * mu i) = 0) →
        mu = 0))
    (hposdef :
      ∀ mu : κ → ℝ, mu ≠ 0 →
        0 < ∑ j, ∑ k, (∑ i, Z i j * mu i) * P.G j k * (∑ i, Z i k * mu i)) :
    isUniqueGlobalSolution P.objective P.equalities P.inequalities P.a P.b xStar := by
  sorry

end «problem-154»
