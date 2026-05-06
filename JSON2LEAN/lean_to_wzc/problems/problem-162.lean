import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-162»
/-
Let A = (A_{ij})∈ ℝ^{n×n} satisfy A_{ij} > 0 for all i, j = 1, ..., n, and let u, v∈ ℝ^n satisfy uᵢ
>
0 and vᵢ > 0 for all i = 1, ..., n. Define α_i = uᵢ vᵢ for i = 1, ..., n. Consider the optimization
problem minimize & prod_{i = 1}^n (\sum_{j = 1}^n A_{ij}xⱼ)^{α_i}; subject to &
prod_{i = 1}^n xᵢ^{α_i} = 1, array over x∈ ℝ^n with xᵢ > 0 for all i = 1, ..., n.
-/
open scoped BigOperators

structure PositiveMatrixProductMinimization (n : ℕ) where
  A : Fin n → Fin n → ℝ
  u : Fin n → ℝ
  v : Fin n → ℝ
  A_pos : ∀ i j, 0 < A i j
  u_pos : ∀ i, 0 < u i
  v_pos : ∀ i, 0 < v i

def PositiveMatrixProductMinimization.alpha {n : ℕ}
    (P : PositiveMatrixProductMinimization n) : Fin n → ℝ :=
  fun i => P.u i * P.v i

def PositiveMatrixProductMinimization.is_feasible {n : ℕ}
    (P : PositiveMatrixProductMinimization n) (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ ∏ i, Real.rpow (x i) (P.alpha i) = 1

def PositiveMatrixProductMinimization.objective {n : ℕ}
    (P : PositiveMatrixProductMinimization n) (x : Fin n → ℝ) : ℝ :=
  ∏ i, Real.rpow (∑ j, P.A i j * x j) (P.alpha i)

/-
positive matrix product minimization. For y∈ ℝ^n, let diag(y) denote the diagonal matrix with
diagonal entries y₁, ..., yₙ, and let Aᵀ denote the ᵀ of A. Using a solution x of this problem,
define D₁ = diag(u)diag(Ax)^{- 1}, D₂ = diag(u)^{- 1}diag(x), where Ax is the usual matrix - vector
product. Show that D₁ and D₂ are positive diagonal matrices satisfying (D_1AD_2)u = u, (D_1AD_2)ᵀ v
= v, by expressing the above problem as a convex optimization problem and deriving the optimality
conditions.
-/
theorem positive_diagonal_scaling_from_optimal_solution
    {n : ℕ} (P : PositiveMatrixProductMinimization n) (x : Fin n → ℝ)
    (hx : P.is_feasible x)
    (hopt :
      ∀ y, P.is_feasible y → P.objective x ≤ P.objective y) :
    let D₁ : Fin n → ℝ := fun i => P.u i / (∑ j, P.A i j * x j)
    let D₂ : Fin n → ℝ := fun j => x j / P.u j
    (∀ i, 0 < D₁ i) ∧
    (∀ j, 0 < D₂ j) ∧
    (∀ i, D₁ i * (∑ j, P.A i j * (D₂ j * P.u j)) = P.u i) ∧
    (∀ j, ∑ i, D₁ i * P.A i j * D₂ j * P.v i = P.v j) := by
  sorry

end «problem-162»
