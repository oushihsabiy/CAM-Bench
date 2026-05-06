import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-59»
/-
Consider the optimization problem [ begin{} text{minimize} & x^T A x + 2 b^T x text{subject to} &
x^T x le 1, end{} ] with variable (x in mathbf{R}^n). Do not assume that (A succeq 0).
-/
structure QuadraticTrustRegionProblem (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  A_symm : A.IsSymm
  b : Fin n → ℝ

def QuadraticTrustRegionProblem.objective {n : ℕ} (p : QuadraticTrustRegionProblem n) :
    (Fin n → ℝ) → ℝ :=
  fun x => dotProduct x (p.A *ᵥ x) + 2 * dotProduct p.b x

def QuadraticTrustRegionProblem.feasibleSet {n : ℕ} (_p : QuadraticTrustRegionProblem n) :
    Set (Fin n → ℝ) :=
  {x | dotProduct x x ≤ 1}

def QuadraticTrustRegionProblem.isFeasible {n : ℕ} (_p : QuadraticTrustRegionProblem n)
    (x : Fin n → ℝ) : Prop :=
  dotProduct x x ≤ 1

/-
Let (n in mathbf{N}), let (A in mathbf{S}^n) be a real symmetric (n \times n) matrix, and let (b
in mathbf{R}^n). Let (I) denote the (n \times n) identity matrix, let (|x |_2 = (x^T x)^{1/2})
for (x in mathbf{R}^n), and for (M in mathbf{S}^n), let (M succeq 0) mean that (M) is positive
semidefinite. Consider the quadratic trust - region problem. Prove that if (x) is a global minimizer
of this problem, then there exists (lambda in mathbf{R}) such that (|x |_2 leq 1, lambda geq 0, A
+ lambda I succeq 0, (A + lambda I)x = - b, lambda bigl(1 - |x |_2^2 bigr) = 0.)
-/
theorem trust_region_global_minimizer_exists_kkt_multiplier
    {n : ℕ} (p : QuadraticTrustRegionProblem n) (x : Fin n → ℝ)
    (h_min :
      x ∈ p.feasibleSet ∧
        ∀ y : Fin n → ℝ, y ∈ p.feasibleSet → p.objective x ≤ p.objective y) :
    ∃ lam : ℝ,
      x ∈ p.feasibleSet ∧
      0 ≤ lam ∧
      (p.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      ((p.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x = (fun i => -p.b i)) ∧
      lam * (1 - dotProduct x x) = 0 := by
  sorry

end «problem-59»
