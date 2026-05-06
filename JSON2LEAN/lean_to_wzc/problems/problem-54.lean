import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-54»

def l2Norm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (v i) ^ 2)

/- [BLOCK Exercise 7.15 | 25 | defn]
A set C ⊆ ℝ^n is a polyhedron if there exist a matrix A ∈ ℝ^{m × n} and a vector b ∈ ℝ^m such that
C = {x ∈ ℝ^n | Ax ≤ b},
where the inequality is interpreted componentwise.
-/
def IsPolyhedron {n : ℕ} (C : Set (Fin n → ℝ)) : Prop :=
  ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℝ, ∃ b : Fin m → ℝ,
    C = {x | ∀ i : Fin m, (∑ j : Fin n, A i j * x j) ≤ b i}

/- [BLOCK Exercise 7.15 | 26 | defn]
For the problem
min_x f₀(x) quad subject to quad fᵢ(x) ≤ 0, hⱼ(x)=0,
with Lagrangian
L(x,λ,nu)=f₀(x)+sum_i λ_i fᵢ(x)+sum_j nu_j hⱼ(x),
the Lagrange dual problem is
max_{λ ≥ 0,nu} g(λ,nu),
where
g(λ,nu)=∈f_x L(x,λ,nu).
-/
def LagrangeDualProblem
    {n m p : ℕ}
    (f0 : (Fin n → ℝ) → ℝ)
    (f : Fin m → (Fin n → ℝ) → ℝ)
    (h : Fin p → (Fin n → ℝ) → ℝ) :
    Set ((Fin m → ℝ) × (Fin p → ℝ)) :=
  let g : ((Fin m → ℝ) × (Fin p → ℝ)) → ℝ :=
    fun yz =>
      sInf
        (Set.range fun x : Fin n → ℝ =>
          f0 x + (∑ i : Fin m, yz.1 i * f i x) + ∑ j : Fin p, yz.2 j * h j x)
  { yz : (Fin m → ℝ) × (Fin p → ℝ) |
      (∀ i : Fin m, 0 ≤ yz.1 i) ∧
        ∀ yz' : (Fin m → ℝ) × (Fin p → ℝ), (∀ i : Fin m, 0 ≤ yz'.1 i) → g yz' ≤ g yz }

/- [BLOCK Exercise 7.15 | 27 | defn]
Given the optimization problem
min_x f₀(x) quad subject to quad fᵢ(x) ≤ 0, hⱼ(x)=0,
its Lagrangian is the function
L(x,λ,nu)=f₀(x)+sum_i λ_i fᵢ(x)+sum_j nu_j hⱼ(x),
where λ_i ≥ 0 and nu_j ∈ ℝ.
-/
def Lagrangian
    {n m p : ℕ}
    (f0 : (Fin n → ℝ) → ℝ)
    (f : Fin m → (Fin n → ℝ) → ℝ)
    (h : Fin p → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ)
    (lam : Fin m → ℝ)
    (nu : Fin p → ℝ) : ℝ :=
  f0 x + ∑ i : Fin m, lam i * f i x + ∑ j : Fin p, nu j * h j x

/- [BLOCK Exercise 7.15 | 28 | defn]
Dual variables are the Lagrange multipliers associated with the constraints of a primal problem:
nonnegative multipliers for inequality constraints and unrestricted multipliers for equality
constraints.
-/
def DualVariables (m p : ℕ) : Set ((Fin m → ℝ) × (Fin p → ℝ)) :=
  {y | 0 ≤ y.1}

/- [BLOCK Exercise 7.15 | 29 | opt_prob]
Consider the primal problem
array{ll}
minimize & -log det B ;
subject\ to & ‖yᵢ‖_2 + a_iᵀ d ≤ bᵢ, quad i=1,ldots,m, ;
& Ba_i = yᵢ, quad i=1,ldots,m,
array
with variables B ∈ S^n, d ∈ ℝ^n, and yᵢ ∈ ℝ^n for i=1,ldots,m, where -log det B is defined for B ∈
S_{++}^n.
-/
structure PrimalLogDetProblem (n m : ℕ) where
  a : Fin m → (Fin n → ℝ)
  b : Fin m → ℝ

def PrimalLogDetProblem.IsFeasible
    {n m : ℕ} (P : PrimalLogDetProblem n m)
    (B : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ)
    (y : Fin m → (Fin n → ℝ)) : Prop :=
  B.IsSymm ∧
  B.PosDef ∧
  (∀ i : Fin m, l2Norm (y i) + ∑ j : Fin n, P.a i j * d j ≤ P.b i) ∧
  ∀ i : Fin m, (fun k : Fin n => ∑ j : Fin n, B k j * P.a i j) = y i

def PrimalLogDetProblem.objective
    {n m : ℕ} (_P : PrimalLogDetProblem n m)
    (B : Matrix (Fin n) (Fin n) ℝ) : EReal := by
  classical
  exact
    if h : B.PosDef then
      ((-Real.log (Matrix.det B) : ℝ) : EReal)
    else
      ⊤

def PrimalLogDetProblem.constraintSet
    {n m : ℕ} (P : PrimalLogDetProblem n m) :
    Set (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) × (Fin m → (Fin n → ℝ))) :=
  {x | P.IsFeasible x.1 x.2.1 x.2.2}

/- [BLOCK Exercise 7.15 | 30 | thm]
Let C = {x ∈ ℝ^n | a_iᵀ x ≤ bᵢ,\ i=1,ldots,m}, where aᵢ ∈ ℝ^n and bᵢ ∈ ℝ for i=1,ldots,m, and assume
that C is a nonempty bounded polyhedron. Let S^n denote the set of real symmetric n × n matrices.
Consider the primal log-det problem
array{ll}
minimize & -log det B ;
subject\ to & ‖yᵢ‖_2 + a_iᵀ d ≤ bᵢ, quad i=1,ldots,m, ;
& Ba_i = yᵢ, quad i=1,ldots,m,
array
with variables B ∈ S^n, d ∈ ℝ^n, and yᵢ ∈ ℝ^n for i=1,ldots,m, where -log det B is defined for B ∈
S_{++}^n. Prove that its Lagrange dual problem is
array{ll}
maximize & log det≤ft(sum_{i=1}^m nu_i a_iᵀ) + n - sum_{i=1}^m bᵢ λ_i ;
subject\ to & λ_i ≥ 0, quad i=1,ldots,m, ;
& ‖nu_i‖_2 ≤ λ_i, quad i=1,ldots,m, ;
& sum_{i=1}^m λ_i aᵢ = 0, ;
& sum_{i=1}^m nu_i a_iᵀ ∈ S_{++}^n,
array
with dual variables λ_i ∈ ℝ and nu_i ∈ ℝ^n for i=1,ldots,m.
-/
theorem primal_log_det_dual_problem_formulation
    {n m : ℕ}
    (a : Fin m → (Fin n → ℝ))
    (b : Fin m → ℝ)
    (C : Set (Fin n → ℝ))
    (hC :
      C = {x | ∀ i : Fin m, (∑ j : Fin n, a i j * x j) ≤ b i})
    (hpoly : IsPolyhedron (n := n) C)
    (hnonempty : C.Nonempty)
    (hbounded : Bornology.IsBounded C) :
    let P : PrimalLogDetProblem n m := { a := a, b := b }
    ∃ f0 : (Fin ((n * n) + (n + m * n)) → ℝ) → ℝ,
      ∃ f : Fin m → (Fin ((n * n) + (n + m * n)) → ℝ) → ℝ,
        ∃ h : Fin (m * n) → (Fin ((n * n) + (n + m * n)) → ℝ) → ℝ,
          LagrangeDualProblem f0 f h =
            { yz : (Fin m → ℝ) × (Fin (m * n) → ℝ) |
                (∀ i : Fin m, 0 ≤ yz.1 i) ∧
                let nu : Fin m → Fin n → ℝ :=
                  fun i j =>
                    yz.2 ((Fintype.equivFinOfCardEq (α := Fin m × Fin n) (by simp)) (i, j))
                let M : Matrix (Fin n) (Fin n) ℝ :=
                  fun r s => ∑ i : Fin m, nu i r * P.a i s
                (∀ i : Fin m, l2Norm (nu i) ≤ yz.1 i) ∧
                (∀ j : Fin n, (∑ i : Fin m, yz.1 i * P.a i j) = 0) ∧
                M.PosDef ∧
                ∀ yz' : (Fin m → ℝ) × (Fin (m * n) → ℝ),
                  (∀ i : Fin m, 0 ≤ yz'.1 i) →
                  let nu' : Fin m → Fin n → ℝ :=
                    fun i j =>
                      yz'.2 ((Fintype.equivFinOfCardEq (α := Fin m × Fin n) (by simp)) (i, j))
                  let M' : Matrix (Fin n) (Fin n) ℝ :=
                    fun r s => ∑ i : Fin m, nu' i r * P.a i s
                  (∀ i : Fin m, l2Norm (nu' i) ≤ yz'.1 i) →
                  (∀ j : Fin n, (∑ i : Fin m, yz'.1 i * P.a i j) = 0) →
                  M'.PosDef →
                    Real.log (Matrix.det M') + n - ∑ i : Fin m, P.b i * yz'.1 i ≤
                      Real.log (Matrix.det M) + n - ∑ i : Fin m, P.b i * yz.1 i } := by
  sorry

end «problem-54»
