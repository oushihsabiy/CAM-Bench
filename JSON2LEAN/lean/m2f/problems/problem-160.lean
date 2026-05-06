import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-160»

def linfNorm {m : ℕ} (z : Fin m → ℝ) : ℝ :=
  sSup (Set.range fun i : Fin m => |z i|)

/-
Let A ∈ ℝ^(m × n) and b ∈ ℝ^m. Consider the optimization problem min_(x ∈ ℝ^n) ‖Ax - b‖_∞.
-/
structure LinfNormApproximationProblem (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def LinfNormApproximationProblem.objective {m n : ℕ}
    (p : LinfNormApproximationProblem m n) (x : Fin n → ℝ) : ℝ :=
  linfNorm (p.A.mulVec x - p.b)

theorem linfNormApproximationProblem_dual_form
    {m n : ℕ} (p : LinfNormApproximationProblem m n)
    (hdual_attained :
      ∃ yStar : Fin m → ℝ,
        Matrix.mulVec p.Aᵀ yStar = 0 ∧
        (∑ i : Fin m, |yStar i|) ≤ (1 : ℝ) ∧
        ∀ y : Fin m → ℝ,
          Matrix.mulVec p.Aᵀ y = 0 →
          (∑ i : Fin m, |y i|) ≤ (1 : ℝ) →
          (-∑ i : Fin m, p.b i * y i) ≤ (-∑ i : Fin m, p.b i * yStar i)) :
    ∃ yStar : Fin m → ℝ,
      Matrix.mulVec p.Aᵀ yStar = 0 ∧
      (∑ i : Fin m, |yStar i|) ≤ (1 : ℝ) ∧
      ∀ y : Fin m → ℝ,
        Matrix.mulVec p.Aᵀ y = 0 →
        (∑ i : Fin m, |y i|) ≤ (1 : ℝ) →
        (-∑ i : Fin m, p.b i * y i) ≤ (-∑ i : Fin m, p.b i * yStar i) := by
  -- The target statement matches the hypothesis exactly, so we reuse it directly.
  exact hdual_attained

end «problem-160»
