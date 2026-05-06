import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-95»
/-
For given A ∈ S_{+ +}^m and B ∈ ℝ^{m × n}, consider the semidefinite program minimize & tr X;
subject
to & [ A & B; Bᵀ & X ] succeq 0, with variable X ∈ S^n.
-/
structure TraceMinimizationSDP (m n : ℕ) where
  A : Matrix (Fin m) (Fin m) ℝ
  A_symm : Aᵀ = A
  A_posDef : Matrix.PosDef A
  B : Matrix (Fin m) (Fin n) ℝ

def TraceMinimizationSDP.blockMatrix {m n : ℕ} (P : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks P.A P.B P.Bᵀ X

def TraceMinimizationSDP.isFeasible {m n : ℕ} (P : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Xᵀ = X ∧ Matrix.PosSemidef (P.blockMatrix X)

theorem traceMinimizationSDP_solution
    {m n : ℕ} (P : TraceMinimizationSDP m n) :
    P.isFeasible (P.Bᵀ * P.A⁻¹ * P.B) ∧
      ∀ X : Matrix (Fin n) (Fin n) ℝ,
        P.isFeasible X →
          Matrix.trace (P.Bᵀ * P.A⁻¹ * P.B) ≤ Matrix.trace X := by
  sorry

/-
Exercise 3.12 | 7 | thm

Let Sⁿ be the space of n × n real symmetric matrices, let S₊₊ᵐ be the set of m × m real symmetric
positive definite matrices, and write M ⪰ 0 for a symmetric positive semidefinite matrix M. For
given A ∈ S₊₊ᵐ and B ∈ ℝ^{m×n}, consider the trace minimization semidefinite program. Conclude that
the function (A, B) ↦ tr(BᵀA⁻¹B) is convex on {(A, B) | A ∈ S₊₊ᵐ, B ∈ ℝ^{m×n}}.
-/
theorem trace_btranspose_inv_mul_b_convex_on
    {m n : ℕ} :
    ConvexOn ℝ
      {p : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ |
        p.1.IsSymm ∧ Matrix.PosDef p.1}
      (fun p => Matrix.trace (p.2ᵀ * p.1⁻¹ * p.2)) := by
  sorry

end «problem-95»
