import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

-- namespace «problem-168»
-- /-
-- For the equality - constrained problem min f(x) subject to Ax = b, the KKT system for the Newton
-- step
-- (δ x, w) is [∇^2 f(x) & Aᵀ; A & 0] [δ x; w] = - [∇ f(x); Ax - b].
-- -/
-- def kktSystem
--     {n m : Type*}
--     [Fintype n] [DecidableEq n]
--     [Fintype m] [DecidableEq m]
--     (hess : Matrix n n ℝ)
--     (A : Matrix m n ℝ)
--     (grad : n → ℝ)
--     (x : n → ℝ)
--     (b : m → ℝ) :
--     Matrix (Sum n m) (Sum n m) ℝ × (Sum n m → ℝ) :=
--   let K : Matrix (Sum n m) (Sum n m) ℝ :=
--     Matrix.fromBlocks hess Aᵀ A 0
--   let rhs : Sum n m → ℝ :=
--     Sum.elim
--       (fun i => -grad i)
--       (fun j => -(A.mulVec x j - b j))
--   (K, rhs)

-- /-
-- For a twice differentiable equality - constrained problem, a Newton step is a pair (δ x, w) that
-- solves the KKT linearization of the first - order optimality conditions at the current point.
-- -/
-- def newtonStep
--     {n m : Type*}
--     [Fintype n] [DecidableEq n]
--     [Fintype m] [DecidableEq m]
--     (hess : Matrix n n ℝ)
--     (A : Matrix m n ℝ)
--     (grad : n → ℝ)
--     (x : n → ℝ)
--     (b : m → ℝ)
--     (Δx : n → ℝ)
--     (w : m → ℝ) : Prop :=
--   let system := kktSystem hess A grad x b
--   let K := system.1
--   let rhs := system.2
--   K.mulVec (Sum.elim Δx w) = rhs

-- def separableEqualityNewtonStepOpCount (n : ℕ) : ℕ :=
--   6 * n + 8

-- /-
-- Consider the optimization problem minimize ∑_{i = 1}^n fᵢ(xᵢ) subject to ∑_{i = 1}^n xᵢ = 1, with
-- decision variable x = (x₁, …, xₙ) ∈ ℝ^n, where each fᵢ: ℝ → ℝ is twice continuously differentiable
-- and satisfies fᵢ''(z) ≥ m > 0 for all z ∈ ℝ, i = 1, …, n.
-- -/
-- structure SeparableEqualityConstrainedProblem where
--   n : ℕ
--   f : Fin n → ℝ → ℝ
--   objective : (Fin n → ℝ) → ℝ := fun x => ∑ i, f i (x i)
--   feasible : (Fin n → ℝ) → Prop := fun x => (∑ i, x i) = 1
--   m : ℝ
--   m_pos : 0 < m
--   f_contDiff : ∀ i, ContDiff ℝ 2 (f i)
--   hess_lower_bound : ∀ i z, m ≤ deriv (deriv (f i)) z

-- /-
-- Consider the separable equality - constrained problem. Let D = diag(f₁''(x₁), ..., fₙ''(xₙ)), let
-- 1∈ℝ^n
-- be the all - ones vector, and let g∈ℝ^n be the ∇of the objective at x. A Newton step (δ x, w) is
-- defined by the KKT system [ D & 1; 1ᵀ & 0 ] [ δ x; w ] = [ - g; 0 ]. Prove that, by exploiting this
-- structure, a Newton step can be computed using O(n) arithmetic operations.
-- -/
-- theorem newtonStep_computable_in_linear_time
--     (P : SeparableEqualityConstrainedProblem)
--     (x : Fin P.n → ℝ)
--     (D : Matrix (Fin P.n) (Fin P.n) ℝ)
--     (g : Fin P.n → ℝ)
--     (hDdiag : ∀ i j, D i j = if i = j then deriv (deriv (P.f i)) (x i) else 0)
--     (hDpos : ∀ i, 0 < D i i)
--     (hg : ∀ i, g i = deriv (P.f i) (x i))
--     (hx : P.feasible x)
--     : let wScalar : ℝ := -((∑ i : Fin P.n, g i / D i i) / (∑ i : Fin P.n, (1 : ℝ) / D i i))
--       let w : Fin 1 → ℝ := fun _ => wScalar
--       let dx : Fin P.n → ℝ := fun i => -(g i + wScalar) / D i i
--       newtonStep D (fun _ _ => 1) g x (fun _ => 1) dx w ∧
--       ∃ C : ℕ, separableEqualityNewtonStepOpCount P.n ≤ C * P.n + C := by
--   sorry

-- end «problem-168»
namespace «problem-168»
/-
For the equality - constrained problem min f(x) subject to Ax = b, the KKT system for the Newton
step
(δ x, w) is [∇^2 f(x) & Aᵀ; A & 0] [δ x; w] = - [∇ f(x); Ax - b].
-/
def kktSystem
    {n m : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (hess : Matrix n n ℝ)
    (A : Matrix m n ℝ)
    (grad : n → ℝ)
    (x : n → ℝ)
    (b : m → ℝ) :
    Matrix (Sum n m) (Sum n m) ℝ × (Sum n m → ℝ) :=
  let K : Matrix (Sum n m) (Sum n m) ℝ :=
    Matrix.fromBlocks hess Aᵀ A 0
  let rhs : Sum n m → ℝ :=
    Sum.elim
      (fun i => -grad i)
      (fun j => -(A.mulVec x j - b j))
  (K, rhs)

/-
For a twice differentiable equality - constrained problem, a Newton step is a pair (δ x, w) that
solves the KKT linearization of the first - order optimality conditions at the current point.
-/
def newtonStep
    {n m : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (hess : Matrix n n ℝ)
    (A : Matrix m n ℝ)
    (grad : n → ℝ)
    (x : n → ℝ)
    (b : m → ℝ)
    (Δx : n → ℝ)
    (w : m → ℝ) : Prop :=
  let system := kktSystem hess A grad x b
  let K := system.1
  let rhs := system.2
  K.mulVec (Sum.elim Δx w) = rhs

def separableEqualityNewtonStepOpCount (n : ℕ) : ℕ :=
  6 * n + 8

/-
Consider the optimization problem minimize ∑_{i = 1}^n fᵢ(xᵢ) subject to ∑_{i = 1}^n xᵢ = 1, with
decision variable x = (x₁, …, xₙ) ∈ ℝ^n, where each fᵢ: ℝ → ℝ is twice continuously differentiable
and satisfies fᵢ''(z) ≥ m > 0 for all z ∈ ℝ, i = 1, …, n.
-/
structure SeparableEqualityConstrainedProblem where
  n : ℕ
  f : Fin n → ℝ → ℝ
  objective : (Fin n → ℝ) → ℝ := fun x => ∑ i, f i (x i)
  feasible : (Fin n → ℝ) → Prop := fun x => (∑ i, x i) = 1
  m : ℝ
  m_pos : 0 < m
  f_contDiff : ∀ i, ContDiff ℝ 2 (f i)
  hess_lower_bound : ∀ i z, m ≤ deriv (deriv (f i)) z

/-
Consider the separable equality - constrained problem. Let D = diag(f₁''(x₁), ..., fₙ''(xₙ)), let
1∈ℝ^n
be the all - ones vector, and let g∈ℝ^n be the ∇of the objective at x. A Newton step (δ x, w) is
defined by the KKT system [ D & 1; 1ᵀ & 0 ] [ δ x; w ] = [ - g; 0 ]. Prove that, by exploiting this
structure, a Newton step can be computed using O(n) arithmetic operations.
-/
theorem newtonStep_computable_in_linear_time
    (P : SeparableEqualityConstrainedProblem)
    (x : Fin P.n → ℝ)
    (D : Matrix (Fin P.n) (Fin P.n) ℝ)
    (g : Fin P.n → ℝ)
    (hDdiag : ∀ i j, D i j = if i = j then deriv (deriv (P.f i)) (x i) else 0)
    (hDpos : ∀ i, 0 < D i i)
    (hg : ∀ i, g i = deriv (P.f i) (x i))
    (hx : (∑ i : Fin P.n, x i) = 1)
    : let wScalar : ℝ := -((∑ i : Fin P.n, g i / D i i) / (∑ i : Fin P.n, (1 : ℝ) / D i i))
      let w : Fin 1 → ℝ := fun _ => wScalar
      let dx : Fin P.n → ℝ := fun i => -(g i + wScalar) / D i i
      newtonStep D (fun _ _ => 1) g x (fun _ => 1) dx w ∧
      ∃ C : ℕ, separableEqualityNewtonStepOpCount P.n ≤ C * P.n + C := by
  sorry

end «problem-168»
