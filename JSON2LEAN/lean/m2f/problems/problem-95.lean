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

/-- The Schur-complement candidate `Bᵀ A⁻¹ B` is positive semidefinite. -/
lemma traceMinimizationSDP_candidate_posSemidef
    {m n : ℕ} (P : TraceMinimizationSDP m n) :
    Matrix.PosSemidef (P.Bᵀ * P.A⁻¹ * P.B) := by
  letI : Invertible P.A := P.A_posDef.isUnit.invertible
  -- Conjugating the positive-semidefinite inverse by `B` produces the candidate matrix.
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (P.A_posDef.inv.posSemidef.conjTranspose_mul_mul_same P.B)

/-- The Schur-complement candidate satisfies the SDP feasibility constraints. -/
lemma traceMinimizationSDP_candidate_feasible
    {m n : ℕ} (P : TraceMinimizationSDP m n) :
    P.isFeasible (P.Bᵀ * P.A⁻¹ * P.B) := by
  letI : Invertible P.A := P.A_posDef.isUnit.invertible
  refine ⟨?_, ?_⟩
  · -- Symmetry follows because every positive-semidefinite real matrix is Hermitian.
    have hCandidate :=
      traceMinimizationSDP_candidate_posSemidef P
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hCandidate.isHermitian.eq
  · -- Route correction: apply the built-in Schur-complement theorem instead of expanding entries.
    have hSchurZero :
        Matrix.PosSemidef
          ((P.Bᵀ * P.A⁻¹ * P.B) - P.Bᴴ * P.A⁻¹ * P.B) := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.PosSemidef.zero :
          Matrix.PosSemidef (0 : Matrix (Fin n) (Fin n) ℝ))
    have hBlocks :
        Matrix.PosSemidef
          (Matrix.fromBlocks P.A P.B P.Bᴴ (P.Bᵀ * P.A⁻¹ * P.B)) :=
      (Matrix.PosDef.fromBlocks₁₁ P.B (P.Bᵀ * P.A⁻¹ * P.B) P.A_posDef).2 hSchurZero
    simpa [TraceMinimizationSDP.blockMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hBlocks

/-- Any feasible block matrix forces the Schur-complement trace lower bound. -/
lemma traceMinimizationSDP_trace_bound_of_blockPosSemidef
    {m n : ℕ} (P : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hBlock : Matrix.PosSemidef (P.blockMatrix X)) :
    Matrix.trace (P.Bᵀ * P.A⁻¹ * P.B) ≤ Matrix.trace X := by
  letI : Invertible P.A := P.A_posDef.isUnit.invertible
  -- Route correction: use the Schur complement of the feasible block matrix directly.
  have hSchur :
      Matrix.PosSemidef (X - P.Bᵀ * P.A⁻¹ * P.B) := by
    have hBlocks :
        Matrix.PosSemidef (Matrix.fromBlocks P.A P.B P.Bᴴ X) := by
      simpa [TraceMinimizationSDP.blockMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using
        hBlock
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosDef.fromBlocks₁₁ P.B X P.A_posDef).1 hBlocks
  -- The trace of a positive-semidefinite real matrix is nonnegative.
  have hTrace_nonneg : 0 ≤ Matrix.trace (X - P.Bᵀ * P.A⁻¹ * P.B) :=
    Matrix.PosSemidef.trace_nonneg hSchur
  have hTrace_sub :
      0 ≤ Matrix.trace X - Matrix.trace (P.Bᵀ * P.A⁻¹ * P.B) := by
    simpa [Matrix.trace_sub] using hTrace_nonneg
  exact sub_nonneg.mp hTrace_sub

theorem traceMinimizationSDP_solution
    {m n : ℕ} (P : TraceMinimizationSDP m n) :
    P.isFeasible (P.Bᵀ * P.A⁻¹ * P.B) ∧
      ∀ X : Matrix (Fin n) (Fin n) ℝ,
        P.isFeasible X →
          Matrix.trace (P.Bᵀ * P.A⁻¹ * P.B) ≤ Matrix.trace X := by
  constructor
  · -- The canonical Schur-complement candidate is feasible.
    exact traceMinimizationSDP_candidate_feasible P
  · intro X hX
    rcases hX with ⟨_, hBlock⟩
    -- Any feasible `X` dominates the candidate because its Schur complement is PSD.
    exact traceMinimizationSDP_trace_bound_of_blockPosSemidef P X hBlock

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
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    constructor
    · -- The matrix-valued first coordinate stays symmetric under convex combinations.
      exact (hx.1.smul a).add (hy.1.smul b)
    · -- A convex combination of positive-definite real matrices is positive definite.
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hy.2
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        exact (hx.2.smul ha_pos).add_posSemidef (hy.2.posSemidef.smul hb)
  · intro x hx y hy a b ha hb hab
    let Px : TraceMinimizationSDP m n :=
      { A := x.1
        A_symm := hx.1.eq
        A_posDef := hx.2
        B := x.2 }
    let Py : TraceMinimizationSDP m n :=
      { A := y.1
        A_symm := hy.1.eq
        A_posDef := hy.2
        B := y.2 }
    have hAcombo_symm : (a • x.1 + b • y.1).IsSymm :=
      (hx.1.smul a).add (hy.1.smul b)
    have hAcombo_posDef : Matrix.PosDef (a • x.1 + b • y.1) := by
      -- The combined instance remains in the positive-definite domain.
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hy.2
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        exact (hx.2.smul ha_pos).add_posSemidef (hy.2.posSemidef.smul hb)
    let Pxy : TraceMinimizationSDP m n :=
      { A := a • x.1 + b • y.1
        A_symm := hAcombo_symm.eq
        A_posDef := hAcombo_posDef
        B := a • x.2 + b • y.2 }
    let Sx : Matrix (Fin n) (Fin n) ℝ := x.2ᵀ * x.1⁻¹ * x.2
    let Sy : Matrix (Fin n) (Fin n) ℝ := y.2ᵀ * y.1⁻¹ * y.2
    have hFeasX : Px.isFeasible Sx := traceMinimizationSDP_candidate_feasible Px
    have hFeasY : Py.isFeasible Sy := traceMinimizationSDP_candidate_feasible Py
    have hFeasCombo :
        Pxy.isFeasible (a • Sx + b • Sy) := by
      refine ⟨?_, ?_⟩
      · -- Symmetry of the witness follows from symmetry of the endpoint witnesses.
        rcases hFeasX with ⟨hSx_symm, _⟩
        rcases hFeasY with ⟨hSy_symm, _⟩
        simp [Sx, Sy, Matrix.transpose_add, Matrix.transpose_smul, hSx_symm, hSy_symm]
      · -- Route correction: combine the endpoint feasible block matrices linearly.
        rcases hFeasX with ⟨_, hBlockX⟩
        rcases hFeasY with ⟨_, hBlockY⟩
        have hCombo :
            Matrix.PosSemidef
              (a • Px.blockMatrix Sx + b • Py.blockMatrix Sy) := by
          exact (hBlockX.smul ha).add (hBlockY.smul hb)
        have hBlockEq :
            a • Px.blockMatrix Sx + b • Py.blockMatrix Sy =
              Pxy.blockMatrix (a • Sx + b • Sy) := by
          simp [Px, Py, Pxy, Sx, Sy, TraceMinimizationSDP.blockMatrix,
            Matrix.fromBlocks_smul, Matrix.fromBlocks_add, Matrix.transpose_add,
            Matrix.transpose_smul]
        rw [hBlockEq] at hCombo
        exact hCombo
    have hOptimalCombo := traceMinimizationSDP_solution Pxy
    have hBound :=
      hOptimalCombo.2 (a • Sx + b • Sy) hFeasCombo
    -- Compare the optimal trace with the trace of the convexly combined feasible witness.
    calc
      Matrix.trace ((a • x.2 + b • y.2)ᵀ * (a • x.1 + b • y.1)⁻¹ * (a • x.2 + b • y.2))
          = Matrix.trace (Pxy.Bᵀ * Pxy.A⁻¹ * Pxy.B) := by
              simp [Pxy]
      _ ≤ Matrix.trace (a • Sx + b • Sy) := hBound
      _ = a * Matrix.trace Sx + b * Matrix.trace Sy := by
            rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
      _ = a • Matrix.trace (x.2ᵀ * x.1⁻¹ * x.2) + b • Matrix.trace (y.2ᵀ * y.1⁻¹ * y.2) := by
            simp [Sx, Sy, smul_eq_mul]

end «problem-95»
