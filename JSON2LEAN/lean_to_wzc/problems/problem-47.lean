import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-47»
/-
Exercise 3.13 | 11 | thm

Let Sⁿ be the set of n × n real symmetric matrices, S₊₊ⁿ ⊂ Sⁿ the set of real symmetric positive
definite matrices, and for M, N ∈ Sⁿ, let M ≼ N mean that N − M is positive semidefinite. Let I
denote the n × n identity matrix, and let tr denote the trace.

For A, B ∈ S₊₊ⁿ, define
H(A, B) = 2(A⁻¹ + B⁻¹)⁻¹.

Show that
X = (A⁻¹ + B⁻¹)⁻¹
solves the semidefinite program
trace-maximization semidefinite program.

Let
R = [A⁻¹  I; B⁻¹  −I].

Verify that R is nonsingular, and apply the congruence transformation defined by R to the matrix
inequality above to obtain
Rᵀ[X  X; X  X]R ≼ Rᵀ[A  0; 0  B]R.
-/
theorem harmonic_mean_matrix_solves_trace_maximization_sdp
    {n : ℕ}
    (A B X : Matrix (Fin n) (Fin n) ℝ)
    (hA_symm : A.IsSymm)
    (hB_symm : B.IsSymm)
    (hA_pos : A.PosDef)
    (hB_pos : B.PosDef)
    (hX : X = (A⁻¹ + B⁻¹)⁻¹) :
    X.IsSymm ∧
      (Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin n) ℝ)
        (0 : Matrix (Fin n) (Fin n) ℝ) B -
        Matrix.fromBlocks X X X X).PosSemidef ∧
      (∀ Y : Matrix (Fin n) (Fin n) ℝ,
        Y.IsSymm →
          (Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin n) ℝ)
            (0 : Matrix (Fin n) (Fin n) ℝ) B -
            Matrix.fromBlocks Y Y Y Y).PosSemidef →
          Matrix.trace Y ≤ Matrix.trace X) ∧
      let R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
        Matrix.fromBlocks A⁻¹ (1 : Matrix (Fin n) (Fin n) ℝ) B⁻¹
          (-1 : Matrix (Fin n) (Fin n) ℝ)
      R.det ≠ 0 ∧
        (R.transpose * Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin n) ℝ)
            (0 : Matrix (Fin n) (Fin n) ℝ) B * R -
          R.transpose * Matrix.fromBlocks X X X X * R).PosSemidef := by
  sorry

/- [BLOCK Exercise 3.13 | 12 | thm]
Let S^n be the set of n × n real symmetric matrices, S_{++}^n ⊂ S^n the set of real symmetric
positive definite matrices, and for M,N ∈ S^n, let M preceq N mean that N-M is positive
semidefinite. Let I denote the n × n identity matrix, and let tr denote the trace.
For A,B ∈ S_{++}^n, define
H(A,B)=2(A^{-1}+B^{-1})^{-1}.
Assuming that X=(A^{-1}+B^{-1})^{-1}
solves the semidefinite program
trace-maximization semidefinite program, conclude that the function
(A,B) mapsto tr((A^{-1}+B^{-1})^{-1})
on S_{++}^n × S_{++}^n is concave.
-/
theorem trace_harmonic_mean_concave
    {n : ℕ} :
    ∀ A₁ B₁ A₂ B₂ : Matrix (Fin n) (Fin n) ℝ,
      ∀ t : ℝ,
        0 ≤ t →
        t ≤ 1 →
        A₁.IsSymm →
        B₁.IsSymm →
        A₂.IsSymm →
        B₂.IsSymm →
        A₁.PosDef →
        B₁.PosDef →
        A₂.PosDef →
        B₂.PosDef →
        (Matrix.trace
            ((((t • A₁ + (1 - t) • A₂)⁻¹ + (t • B₁ + (1 - t) • B₂)⁻¹)⁻¹))) ≥
          t * Matrix.trace ((A₁⁻¹ + B₁⁻¹)⁻¹) +
            (1 - t) * Matrix.trace ((A₂⁻¹ + B₂⁻¹)⁻¹) := by
  sorry
end «problem-47»
