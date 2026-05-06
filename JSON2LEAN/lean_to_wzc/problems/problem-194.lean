import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-194»

def l2Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i) ^ 2)

/- [BLOCK Exercise 18.9 | 4 | opt_prob]
Let Aₖ ∈ ℝ^{m × n}, cₖ ∈ ℝ^m, and Delta_k ∈ ℝ with Delta_k ≥ 0. Consider the problem
min_{v ∈ ℝ^n} ‖Aₖ v + cₖ‖_2^2
quad subject to quad
‖v‖_2 ≤ 0.8Delta_k.
Here
Range(A_kᵀ)={A_kᵀ y : y ∈ ℝ^m}.
-/
structure LeastSquaresTrustRegionProblem where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  c : Fin m → ℝ
  Δ : ℝ
  Δ_nonneg : 0 ≤ Δ
  transposeRange : Set (Fin n → ℝ) := Set.range A.transpose.mulVec

def LeastSquaresTrustRegionProblem.objective (p : LeastSquaresTrustRegionProblem) :
    (Fin p.n → ℝ) → ℝ :=
  fun v => l2Norm (p.A.mulVec v + p.c) ^ 2

def LeastSquaresTrustRegionProblem.feasibleSet (p : LeastSquaresTrustRegionProblem) :
    Set (Fin p.n → ℝ) :=
  {v | l2Norm v ≤ (0.8 : ℝ) * p.Δ}

def LeastSquaresTrustRegionProblem.residual (p : LeastSquaresTrustRegionProblem) (v : Fin p.n → ℝ) :
    Fin p.m → ℝ :=
  fun i => (∑ j, p.A i j * v j) + p.c i

/- [BLOCK Exercise 18.9 | 5 | thm]
Let Aₖ ∈ ℝ^{m × n}, cₖ ∈ ℝ^m, and Delta_k ∈ ℝ with Delta_k ≥ 0. Consider the least-squares
trust-region problem
min_{v ∈ ℝ^n} ‖Aₖ v + cₖ‖_2^2
quad subject to quad
‖v‖_2 ≤ 0.8Delta_k.
Here Range(A_kᵀ)={A_kᵀ y : y ∈ ℝ^m}. Show that this problem has at least one solution vₖ such that
vₖ ∈ Range(A_kᵀ).
-/
theorem exists_solution_in_transposeRange (p : LeastSquaresTrustRegionProblem) :
    ∃ v : Fin p.n → ℝ,
      v ∈ p.feasibleSet ∧
      v ∈ p.transposeRange ∧
      ∀ w : Fin p.n → ℝ, w ∈ p.feasibleSet → p.objective v ≤ p.objective w := by
  sorry

end «problem-194»
