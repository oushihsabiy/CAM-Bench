import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-183»
/-
A semidefinite program is an optimization problem of the form minimize & cᵀ z; subject to & F₀ +
\sum_{j = 1}^p zⱼ Fⱼ succeq 0, array where the decision variable is z ∈ ℝ^p and each Fⱼ ∈ S^m.
-/
open Matrix

structure SemidefiniteProgram (p m : ℕ) where
  c : Fin p → ℝ
  F0 : Matrix (Fin m) (Fin m) ℝ
  F : Fin p → Matrix (Fin m) (Fin m) ℝ
  F0_symm : F0.IsSymm
  F_symm : ∀ j, (F j).IsSymm

/- The linear objective function of a semidefinite program evaluated at z. -/
def SemidefiniteProgram.objective {p m: ℕ} (P: SemidefiniteProgram p m) (z: Fin p → ℝ): ℝ :=
  ∑ j, P.c j * z j

/- The affine matrix appearing in the semidefinite constraint. -/
structure LinearMatrixInequality (p m: ℕ) where
  F0 : Matrix (Fin m) (Fin m) ℝ
  F: Fin p → Matrix (Fin m) (Fin m) ℝ
  F0_symm: F0.IsSymm
  F_symm: ∀ j, (F j).IsSymm

def LinearMatrixInequality.matrix {p m : ℕ} (L : LinearMatrixInequality p m) (z: Fin p → ℝ):
    Prop:=
  PosSemidef (L.F0 + ∑ j, z j • L.F j)

/-
For a symmetric block matrix M = [ A & B; Bᵀ & C ] with A succ 0, the Schur complement of A in M is
C - Bᵀ A^{- 1} B. Moreover, M succeq 0 if and only if C - Bᵀ A^{- 1} B succeq 0.
-/
structure MaxQuadraticFormMinimization (n m K : ℕ) where
  F0 : Matrix (Fin m) (Fin m) ℝ
  F : Fin n → Matrix (Fin m) (Fin m) ℝ
  c : Fin K → Fin m → ℝ
  F0_symm : F0.IsSymm
  F_symm : ∀ j, (F j).IsSymm
  K_pos : 1 ≤ K

/-
The affine matrix F(x) = F₀ + ∑_{j = 1}^n xⱼ Fⱼ appearing in the constraint.
-/
def MaxQuadraticFormMinimization.matrix (P : MaxQuadraticFormMinimization n m K)
    (x : Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  P.F0 + ∑ j, x j • P.F j

/-
The objective value max_{i = 1, …, K} cᵢᵀF(x)⁻¹cᵢ.
-/
def MaxQuadraticFormMinimization.objective (P : MaxQuadraticFormMinimization n m K)
    (x : Fin n → ℝ) : ℝ :=
  let i0 : Fin K := ⟨0, Nat.succ_le_iff.mp P.K_pos⟩
  Finset.fold max
    (dotProduct (P.c i0) ((P.matrix x)⁻¹.mulVec (P.c i0)))
    (fun i => dotProduct (P.c i) ((P.matrix x)⁻¹.mulVec (P.c i)))
    Finset.univ

/-
The feasibility condition F(x) ≻ 0.
-/
def MaxQuadraticFormMinimization.feasible (P : MaxQuadraticFormMinimization n m K)
    (x : Fin n → ℝ) : Prop :=
  Matrix.PosDef (P.matrix x)

/-- A `1 × 1` real matrix is positive semidefinite exactly when its unique entry is nonnegative. -/
lemma posSemidef_finOne_const_iff (r : ℝ) :
    PosSemidef (((fun _ _ : Fin 1 => r) : Matrix (Fin 1) (Fin 1) ℝ)) ↔ 0 ≤ r := by
  -- Reduce the constant `1 × 1` matrix to a diagonal matrix.
  have hdiag :
      (((fun _ _ : Fin 1 => r) : Matrix (Fin 1) (Fin 1) ℝ))
        = Matrix.diagonal (fun _ : Fin 1 => r) := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    simp [Matrix.diagonal, hij]
  rw [hdiag, Matrix.posSemidef_diagonal_iff]
  simp

/-- For feasible `x`, each block semidefinite constraint is equivalent to the corresponding
Schur-complement upper bound. -/
lemma blockConstraint_iff_score_le {n m K : ℕ} (P : MaxQuadraticFormMinimization n m K)
    {x : Fin n → ℝ} (hx : P.feasible x) (i : Fin K) (t : ℝ) :
    PosSemidef
      (fromBlocks
        (P.matrix x)
        (fun a : Fin m => fun _ : Fin 1 => P.c i a)
        (fun _ : Fin 1 => fun b : Fin m => P.c i b)
        (fun _ _ : Fin 1 => t)) ↔
      dotProduct (P.c i) ((P.matrix x)⁻¹.mulVec (P.c i)) ≤ t := by
  let B : Matrix (Fin m) (Fin 1) ℝ := Matrix.replicateCol (Fin 1) (P.c i)
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => t
  -- Rewrite the off-diagonal block as the conjugate transpose required by the Schur complement.
  have hconj : Bᴴ = Matrix.replicateRow (Fin 1) (P.c i) := by
    ext u v
    simp [B, Matrix.replicateCol, Matrix.replicateRow]
  let _ : Invertible (P.matrix x) := hx.isUnit.invertible
  -- Collapse the Schur complement to its unique scalar entry.
  have hentry :
      Bᴴ * (P.matrix x)⁻¹ * B
        =
          (((fun _ _ : Fin 1 =>
              dotProduct (P.c i) ((P.matrix x)⁻¹.mulVec (P.c i))) :
            Matrix (Fin 1) (Fin 1) ℝ)) := by
    rw [hconj]
    rw [show Matrix.replicateRow (Fin 1) (P.c i) * (P.matrix x)⁻¹ * B
        = Matrix.replicateRow (Fin 1) (P.c i) * ((P.matrix x)⁻¹ * B) by rw [Matrix.mul_assoc]]
    have hmul :=
      congrArg (fun M => Matrix.replicateRow (Fin 1) (P.c i) * M)
        (by
          simpa [B] using
            (Matrix.replicateCol_mulVec (ι := Fin 1) ((P.matrix x)⁻¹) (P.c i)).symm)
    exact hmul.trans <| by
      ext u v
      exact
        Matrix.replicateRow_mul_replicateCol_apply
          (ι := Fin 1) (v := P.c i) (w := (P.matrix x)⁻¹.mulVec (P.c i)) u v
  have hschur :
      D - Bᴴ * (P.matrix x)⁻¹ * B
        =
          (((fun _ _ : Fin 1 =>
              t - dotProduct (P.c i) ((P.matrix x)⁻¹.mulVec (P.c i))) :
            Matrix (Fin 1) (Fin 1) ℝ)) := by
    rw [hentry]
    ext u v
    simp [D]
  -- Apply the Schur-complement equivalence and translate the `1 × 1` PSD condition to a scalar.
  change
    PosSemidef (fromBlocks (P.matrix x) B (Matrix.replicateRow (Fin 1) (P.c i)) D) ↔
      dotProduct (P.c i) ((P.matrix x)⁻¹.mulVec (P.c i)) ≤ t
  rw [show Matrix.replicateRow (Fin 1) (P.c i) = Bᴴ by simpa using hconj.symm]
  rw [Matrix.PosDef.fromBlocks₁₁ (A := P.matrix x) (B := B) (D := D) hx]
  rw [hschur, posSemidef_finOne_const_iff]
  constructor <;> intro h <;> linarith

/-- The objective is the least upper bound of the finitely many Schur-complement scores. -/
lemma objective_isLeast_upperBounds {n m K : ℕ} (P : MaxQuadraticFormMinimization n m K)
    (x : Fin n → ℝ) :
    IsLeast
      {t : ℝ | ∀ i : Fin K, dotProduct (P.c i) ((P.matrix x)⁻¹.mulVec (P.c i)) ≤ t}
      (P.objective x) := by
  let i0 : Fin K := ⟨0, Nat.succ_le_iff.mp P.K_pos⟩
  let score : Fin K → ℝ := fun i => dotProduct (P.c i) ((P.matrix x)⁻¹.mulVec (P.c i))
  refine ⟨?_, ?_⟩
  · -- Each score is bounded above by the fold-max objective.
    intro i
    have hi :
        score i
          ≤ Finset.fold max (score i0) score Finset.univ := by
      exact
        (Finset.le_fold_max (s := Finset.univ) (b := score i0) (f := score) (c := score i)).2 <|
          Or.inr ⟨i, by simp, le_rfl⟩
    simpa [MaxQuadraticFormMinimization.objective, i0, score] using hi
  · -- Any common upper bound of the scores also bounds the fold-max objective.
    intro t ht
    have hfold :
        Finset.fold max (score i0) score Finset.univ ≤ t := by
      refine
        (Finset.fold_max_le (s := Finset.univ) (b := score i0) (f := score) (c := t)).2
          ⟨ht i0, ?_⟩
      intro i hi
      exact ht i
    simpa [MaxQuadraticFormMinimization.objective, i0, score] using hfold

/-
Let max quadratic - form minimization. Prove that this problem is equivalent to the semidefinite
program minimize & t; subject to & [ F(x) & cᵢ; c_iᵀ & t ] succeq 0, i = 1, ..., K, array with
variables x∈ℝ^n and t∈ℝ.
-/
theorem maxQuadraticFormMinimization_equiv_semidefinite_program
    {n m K : ℕ} (P : MaxQuadraticFormMinimization n m K) :
    ∃ (sdpFeasible : (Fin n → ℝ) → ℝ → Prop),
      (∀ (x : Fin n → ℝ) (t : ℝ),
        sdpFeasible x t ↔
          ∀ i : Fin K,
            PosSemidef
              (fromBlocks
                (P.matrix x)
                (fun a : Fin m => fun _ : Fin 1 => P.c i a)
                (fun _ : Fin 1 => fun b : Fin m => P.c i b)
                (fun _ _ : Fin 1 => t))) ∧
      (∀ (x : Fin n → ℝ),
        P.feasible x →
          P.objective x =
            sInf {t : ℝ | sdpFeasible x t}) := by
  refine
    ⟨fun x t =>
      ∀ i : Fin K,
        PosSemidef
          (fromBlocks
            (P.matrix x)
            (fun a : Fin m => fun _ : Fin 1 => P.c i a)
            (fun _ : Fin 1 => fun b : Fin m => P.c i b)
            (fun _ _ : Fin 1 => t)),
      ?_, ?_⟩
  · -- The chosen SDP feasibility predicate is exactly the block-PSD system from the statement.
    intro x t
    rfl
  · -- For feasible `x`, identify feasible `t` with the upper bounds of the Schur scores.
    intro x hx
    let score : Fin K → ℝ := fun i => dotProduct (P.c i) ((P.matrix x)⁻¹.mulVec (P.c i))
    have hset :
        {t : ℝ |
            ∀ i : Fin K,
              PosSemidef
                (fromBlocks
                  (P.matrix x)
                  (fun a : Fin m => fun _ : Fin 1 => P.c i a)
                  (fun _ : Fin 1 => fun b : Fin m => P.c i b)
                  (fun _ _ : Fin 1 => t))}
          =
        {t : ℝ | ∀ i : Fin K, score i ≤ t} := by
      ext t
      simp [score, blockConstraint_iff_score_le, hx]
    -- The objective is the least element of the upper-bound set, hence equals its infimum.
    rw [hset]
    simpa [score] using (objective_isLeast_upperBounds P x).csInf_eq.symm

end «problem-183»
