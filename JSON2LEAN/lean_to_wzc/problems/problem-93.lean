import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-93»
/-
A function f: C₁ × C₂ → ℝ cup {+ ∞} is jointly convex in (x, y) if, for all (x₁, y₁), (x₂, y₂) ∈ C₁
×
C₂ and all θ ∈ [0, 1], f(θ x₁ + (1 - θ)x₂, θ y₁ + (1 - θ)y₂) ≤ θ f(x₁, y₁) + (1 - θ)f(x₂, y₂).
-/
def JointlyConvex
    {E₁ E₂ : Type*}
    [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    (C₁ : Set E₁) (C₂ : Set E₂) (f : E₁ × E₂ → EReal) : Prop :=
  ∀ ⦃x₁ x₂ : E₁⦄, x₁ ∈ C₁ → x₂ ∈ C₁ →
    ∀ ⦃y₁ y₂ : E₂⦄, y₁ ∈ C₂ → y₂ ∈ C₂ →
    ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
      f (θ • x₁ + (1 - θ) • x₂, θ • y₁ + (1 - θ) • y₂) ≤
        θ * f (x₁, y₁) + (1 - θ) * f (x₂, y₂)

/-
A semidefinite program is an optimization problem in which the decision variable is a symmetric
matrix, the objective function is linear in the decision variables, and the constraints include a
linear matrix inequality of the form F₀ + sum_i = 1^p xᵢ Fᵢ succeq 0.
-/
structure SemidefiniteProgram (n p : ℕ) where
  X : Matrix (Fin n) (Fin n) ℝ
  symmetric : Xᵀ = X
  objective : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ
  F0 : Matrix (Fin n) (Fin n) ℝ
  F0_symm : F0.IsSymm
  x : Fin p → ℝ
  F : Fin p → Matrix (Fin n) (Fin n) ℝ
  F_symm : ∀ i, (F i).IsSymm

def SemidefiniteProgram.lmiMatrix {n p : ℕ} (sdp : SemidefiniteProgram n p) :
    Matrix (Fin n) (Fin n) ℝ :=
  sdp.F0 + ∑ i : Fin p, sdp.x i • sdp.F i

def SemidefiniteProgram.isFeasible {n p : ℕ} (sdp : SemidefiniteProgram n p) : Prop :=
  sdp.X = sdp.lmiMatrix ∧ sdp.X.PosSemidef

def SemidefiniteProgram.objectiveValue {n p : ℕ} (sdp : SemidefiniteProgram n p) : ℝ :=
  sdp.objective sdp.X

structure TraceMinimizationSDP (m n : ℕ) where
  A : Matrix (Fin m) (Fin m) ℝ
  A_isSymm : A.IsSymm
  A_posDef : A.PosDef
  B : Matrix (Fin m) (Fin n) ℝ
  X : Matrix (Fin n) (Fin n) ℝ
  X_isSymm : X.IsSymm
  feasible : (Matrix.fromBlocks A B B.transpose X).PosSemidef

def TraceMinimizationSDP.objective {m n : ℕ} (p : TraceMinimizationSDP m n) : ℝ :=
  Matrix.trace p.X

def TraceMinimizationSDP.blockMatrix {m n : ℕ} (p : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks p.A p.B p.B.transpose X

def TraceMinimizationSDP.isFeasible {m n : ℕ} (p : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsSymm ∧ (p.blockMatrix X).PosSemidef

/-
For A ≻ 0, the Schur-complement epigraph condition
[ A  B; Bᵀ  X ] ⪰ 0 represents trace(Bᵀ A⁻¹ B) ≤ trace(X). Consequently the function
(A,B) ↦ trace(Bᵀ A⁻¹ B) is jointly convex on positive-definite A and arbitrary B. The equality
case X = Bᵀ A⁻¹ B is also recorded to rule out a one-sided or vacuous SDP formulation.
-/
theorem trace_Bt_Ainv_B_jointlyConvex_and_sdp_epigraph :
    JointlyConvex
      {A : Matrix (Fin m) (Fin m) ℝ | A.IsSymm ∧ A.PosDef}
      (Set.univ : Set (Matrix (Fin m) (Fin n) ℝ))
      (fun p : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ =>
        ((Matrix.trace (p.2ᵀ * p.1⁻¹ * p.2) : ℝ) : EReal)) ∧
    (∀ (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
        (X : Matrix (Fin n) (Fin n) ℝ),
      A.PosDef →
      A.IsSymm →
      X.IsSymm →
      (Matrix.fromBlocks A B B.transpose X).PosSemidef →
        Matrix.trace (Bᵀ * A⁻¹ * B) ≤ Matrix.trace X) ∧
    (∀ (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ),
      A.PosDef →
      A.IsSymm →
        (Bᵀ * A⁻¹ * B).IsSymm ∧
        (Matrix.fromBlocks A B B.transpose (Bᵀ * A⁻¹ * B)).PosSemidef) := by
  sorry

end «problem-93»
