import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-181»

def l2Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i) ^ 2)

/-
Let A ∈ 𝕊_ {+ +}^n, b ∈ ℝ^n, and Δ > 0, where 𝕊_ + + ^n denotes the set of all n × n real symmetric
positive definite matrices. Consider the quadratic optimization problem

min_(x ∈ ℝ^n) x^T A x + 2 b^T x s. t. ‖x‖_2 ≤ Δ.
-/
structure QuadraticBallConstrainedProblem (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  b : Fin n → ℝ
  Δ : ℝ
  symm : A.IsSymm
  posDef : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (A.mulVec x)
  delta_pos : 0 < Δ

def QuadraticBallConstrainedProblem.feasible {n : ℕ}
    (p : QuadraticBallConstrainedProblem n) (x : Fin n → ℝ) : Prop :=
  l2Norm x ≤ p.Δ

def QuadraticBallConstrainedProblem.objective {n : ℕ}
    (p : QuadraticBallConstrainedProblem n) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (p.A.mulVec x) + 2 * dotProduct p.b x

/-
Let quadratic ball - constrained problem. Let x_0 = - A^ - 1b. Prove that if ‖x_0‖_2 ≤ Δ, then the
optimal solution is x^* = x_0, and write down the corresponding expression for the optimal value of
the optimization problem.
-/
theorem unconstrained_minimizer_is_optimal_when_feasible
    {n : ℕ} (p : QuadraticBallConstrainedProblem n) (x₀ : Fin n → ℝ)
    (hx₀ : x₀ = -(p.A⁻¹.mulVec p.b))
    (hfeas : p.feasible x₀) :
    IsMinOn p.objective {x | p.feasible x} x₀ ∧
      p.objective x₀ = -dotProduct p.b (p.A⁻¹.mulVec p.b) := by
  sorry

/-
Let quadratic ball - constrained problem. Let x_0 = - A^ - 1b. Prove that if ‖x_0‖_2 > Δ, then there
exists a unique λ^* > 0 such that ‖(A + λ^* I)^ - 1 b‖_2 = Δ, and the optimal solution is x^* = - (A
+ λ^*
I)^ - 1 b, and write down the corresponding expression for the optimal value of the optimization
problem.
-/
theorem boundary_case_has_shifted_inverse_characterization
    {n : ℕ} (p : QuadraticBallConstrainedProblem n) (x₀ : Fin n → ℝ)
    (hx₀ : x₀ = -(p.A⁻¹.mulVec p.b))
    (houtside : p.Δ < l2Norm x₀) :
    ∃! lam : ℝ,
      0 < lam ∧
      l2Norm (((p.A + lam • 1)⁻¹).mulVec p.b) = p.Δ ∧
      IsMinOn p.objective {x | p.feasible x} (-(((p.A + lam • 1)⁻¹).mulVec p.b)) ∧
      p.objective (-(((p.A + lam • 1)⁻¹).mulVec p.b)) =
        -dotProduct p.b (((p.A + lam • 1)⁻¹).mulVec p.b) -
          lam * p.Δ ^ 2 := by
  sorry

end «problem-181»
