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
  sorry

end «problem-183»