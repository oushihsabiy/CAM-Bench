import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-151»
/-
A semidefinite program is an optimization problem in which the decision variables are subject to
affine matrix inequalities of the form A₀ + \sum_{i = 1}^p zᵢ Aᵢ succeq 0, and the objective
function
is affine in the variables.
-/
structure SemidefiniteProgram (n p : ℕ) where
  A : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ
  c : Fin p → ℝ
  d : ℝ

def SemidefiniteProgram.lmi {n p : ℕ} (S : SemidefiniteProgram n p) (z : Fin p → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  S.A 0 + ∑ i : Fin p, z i • S.A i.succ

def SemidefiniteProgram.objective {n p : ℕ} (S : SemidefiniteProgram n p) (z : Fin p → ℝ) : ℝ :=
  ∑ i : Fin p, S.c i * z i + S.d

structure SchurComplementSemidefiniteProgram (m n : ℕ) where
  F : (Fin n → ℝ) → Matrix (Fin m) (Fin m) ℝ

def SchurComplementSemidefiniteProgram.blockMatrix {m n : ℕ}
    (P : SchurComplementSemidefiniteProgram m n) (x : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.fromBlocks (P.F x) 1 1 (t • (1 : Matrix (Fin m) (Fin m) ℝ))

def SchurComplementSemidefiniteProgram.isFeasible {m n : ℕ}
    (P : SchurComplementSemidefiniteProgram m n) (x : Fin n → ℝ) (t : ℝ) : Prop :=
  Matrix.PosDef (P.F x) ∧ Matrix.PosSemidef (P.blockMatrix x t)

def SchurComplementSemidefiniteProgram.objective {m n : ℕ}
    (_P : SchurComplementSemidefiniteProgram m n) (_x : Fin n → ℝ) (t : ℝ) : ℝ :=
  t

def unitBallQuadraticValues {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) : Set ℝ :=
  {q : ℝ | ∃ c : Fin m → ℝ, c ⬝ᵥ c ≤ 1 ∧ c ⬝ᵥ M.mulVec c = q}

def unitBallQuadraticSup {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  sSup (unitBallQuadraticValues M)

/-
Let m, n ∈ ℕ. For each i = 0, 1, ..., n, let Fᵢ ∈ S^m, where S^m is the set of m × m real symmetric
matrices. For x = (x₁, ..., xₙ) ∈ ℝ^n, define F(x) = F₀ + \sum_{i = 1}^n xᵢ Fᵢ. Let dom f = {x ∈ ℝ^n
|
F(x)succ 0}, where F(x)succ 0 means that F(x) is positive definite. Assume m > 0, so the unit ball is
not the degenerate zero-dimensional case in which the LMI no longer constrains t. Prove the stronger
epigraph-level Schur-complement equivalence: for every x and t, the inequality
sup_{‖c‖_2 ≤ 1} cᵀ F(x)^{-1} c ≤ t is equivalent to the block LMI
[F(x) I; I tI] ⪰ 0. Consequently, the exact objective-value formulation, the epigraph formulation,
and the semidefinite program have the same infimum.
-/
theorem schurComplement_equivalent_to_unit_ball_quadratic_form_minimization
    (m n : ℕ)
    (F : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ)
    (hm : 0 < m)
    (hFsymm : ∀ i : Fin (n + 1), (F i).IsSymm) :
    let P : SchurComplementSemidefiniteProgram m n :=
      { F := fun x => F 0 + ∑ i : Fin n, x i • F i.succ }
    (∀ x : Fin n → ℝ, ∀ t : ℝ,
      Matrix.PosDef (P.F x) →
        (unitBallQuadraticSup ((P.F x)⁻¹) ≤ t ↔ P.isFeasible x t)) ∧
    ({t : ℝ | ∃ x : Fin n → ℝ,
      Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) ≤ t} =
      {t : ℝ | ∃ x : Fin n → ℝ, P.isFeasible x t}) ∧
    sInf
        {r : ℝ | ∃ x : Fin n → ℝ,
          Matrix.PosDef (P.F x) ∧
          unitBallQuadraticSup ((P.F x)⁻¹) = r} =
      sInf
        {t : ℝ | ∃ x : Fin n → ℝ,
          Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) ≤ t} ∧
    sInf
        {r : ℝ | ∃ x : Fin n → ℝ,
          Matrix.PosDef (P.F x) ∧
          unitBallQuadraticSup ((P.F x)⁻¹) = r} =
      sInf
        {t : ℝ | ∃ x : Fin n → ℝ,
          P.isFeasible x t} := by
  sorry


end «problem-151»
