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
/-- The Schur complement of a positive semidefinite block matrix gives the trace bound. -/
lemma trace_Bt_Ainv_B_le_trace_of_fromBlocks_posSemidef
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef)
    (hBlock : (Matrix.fromBlocks A B B.transpose X).PosSemidef) :
    Matrix.trace (Bᵀ * A⁻¹ * B) ≤ Matrix.trace X := by
  -- Introduce the inverse of the positive-definite leading block so the Schur complement theorem applies.
  letI : Invertible A := hA.isUnit.invertible
  -- The Schur complement is positive semidefinite because the full block matrix is.
  have hSchur : (X - Bᵀ * A⁻¹ * B).PosSemidef := by
    simpa using (Matrix.PosDef.fromBlocks₁₁ (B := B) (D := X) hA).mp hBlock
  -- Taking traces preserves nonnegativity on positive semidefinite matrices, which is exactly the desired inequality.
  have hTraceNonneg : 0 ≤ Matrix.trace (X - Bᵀ * A⁻¹ * B) :=
    Matrix.PosSemidef.trace_nonneg hSchur
  rw [Matrix.trace_sub] at hTraceNonneg
  linarith

/-- The exact Schur-complement witness is symmetric and makes the block matrix positive semidefinite. -/
lemma Bt_Ainv_B_isSymm_and_fromBlocks_posSemidef
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.PosDef) :
    (Bᵀ * A⁻¹ * B).IsSymm ∧
      (Matrix.fromBlocks A B B.transpose (Bᵀ * A⁻¹ * B)).PosSemidef := by
  -- The quadratic term is positive semidefinite because positive definiteness is preserved under inversion and congruence.
  have hQuadPosSemidef : (Bᵀ * A⁻¹ * B).PosSemidef := by
    simpa using (hA.inv.posSemidef.conjTranspose_mul_mul_same B)
  -- Over `ℝ`, Hermitian and symmetric coincide, so the witness matrix is symmetric.
  have hInvSymm : (A⁻¹).IsSymm := by
    simpa using hA.inv.isHermitian.eq
  have hQuadSymm : (Bᵀ * A⁻¹ * B).IsSymm := by
    rw [Matrix.IsSymm]
    calc
      (Bᵀ * A⁻¹ * B)ᵀ = Bᵀ * ((A⁻¹)ᵀ * B) := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = Bᵀ * (A⁻¹ * B) := by rw [hInvSymm.eq]
      _ = Bᵀ * A⁻¹ * B := by
        exact (Matrix.mul_assoc Bᵀ A⁻¹ B).symm
  -- The Schur complement is exactly zero for the equality-case witness.
  letI : Invertible A := hA.isUnit.invertible
  have hSchurZero : ((Bᵀ * A⁻¹ * B) - Bᵀ * A⁻¹ * B).PosSemidef := by
    simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
  have hBlock : (Matrix.fromBlocks A B B.transpose (Bᵀ * A⁻¹ * B)).PosSemidef := by
    simpa using (Matrix.PosDef.fromBlocks₁₁ (B := B) (D := Bᵀ * A⁻¹ * B) hA).mpr hSchurZero
  exact ⟨hQuadSymm, hBlock⟩

/-- A strict convex combination of positive-definite matrices is positive definite. -/
lemma strict_convexCombination_posDef
    {m : ℕ}
    (A₁ A₂ : Matrix (Fin m) (Fin m) ℝ)
    (hA₁ : A₁.PosDef)
    (hA₂ : A₂.PosDef)
    {θ : ℝ}
    (hθ_pos : 0 < θ)
    (hθ_lt : θ < 1) :
    (θ • A₁ + (1 - θ) • A₂).PosDef := by
  -- Scale each positive-definite matrix by a strictly positive coefficient.
  have hScaled₁ : (θ • A₁).PosDef := hA₁.smul hθ_pos
  have hScaled₂ : ((1 - θ) • A₂).PosDef := hA₂.smul (sub_pos.mpr hθ_lt)
  -- Then add the two positive-definite pieces.
  exact hScaled₁.add hScaled₂

/-- Positive semidefiniteness is preserved under convex combinations of block matrices. -/
lemma fromBlocks_convexCombination_posSemidef
    {m n : ℕ}
    (A₁ A₂ : Matrix (Fin m) (Fin m) ℝ)
    (B₁ B₂ : Matrix (Fin m) (Fin n) ℝ)
    (X₁ X₂ : Matrix (Fin n) (Fin n) ℝ)
    (hBlock₁ : (Matrix.fromBlocks A₁ B₁ B₁.transpose X₁).PosSemidef)
    (hBlock₂ : (Matrix.fromBlocks A₂ B₂ B₂.transpose X₂).PosSemidef)
    {θ : ℝ}
    (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) :
    (Matrix.fromBlocks
      (θ • A₁ + (1 - θ) • A₂)
      (θ • B₁ + (1 - θ) • B₂)
      (θ • B₁ + (1 - θ) • B₂).transpose
      (θ • X₁ + (1 - θ) • X₂)).PosSemidef := by
  -- The PSD cone is closed under nonnegative scaling and addition.
  have hConvex :
      (θ • Matrix.fromBlocks A₁ B₁ B₁.transpose X₁ +
        (1 - θ) • Matrix.fromBlocks A₂ B₂ B₂.transpose X₂).PosSemidef := by
    exact (hBlock₁.smul hθ₀).add (hBlock₂.smul (sub_nonneg.mpr hθ₁))
  -- Expand the block-matrix algebra to identify the result with the desired convex combination.
  simpa [Matrix.fromBlocks_smul, Matrix.fromBlocks_add, Matrix.transpose_add,
    Matrix.transpose_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hConvex

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
  constructor
  · -- Prove joint convexity by lifting the epigraph through convexity of the PSD cone.
    intro A₁ A₂ hA₁_mem hA₂_mem B₁ B₂ _ _ θ hθ₀ hθ₁
    rcases hA₁_mem with ⟨_, hA₁⟩
    rcases hA₂_mem with ⟨_, hA₂⟩
    let X₁ : Matrix (Fin n) (Fin n) ℝ := B₁ᵀ * A₁⁻¹ * B₁
    let X₂ : Matrix (Fin n) (Fin n) ℝ := B₂ᵀ * A₂⁻¹ * B₂
    let Aθ : Matrix (Fin m) (Fin m) ℝ := θ • A₁ + (1 - θ) • A₂
    let Bθ : Matrix (Fin m) (Fin n) ℝ := θ • B₁ + (1 - θ) • B₂
    let Xθ : Matrix (Fin n) (Fin n) ℝ := θ • X₁ + (1 - θ) • X₂
    -- Use the exact Schur-complement witnesses for the two endpoints.
    have hWitness₁ : X₁.IsSymm ∧ (Matrix.fromBlocks A₁ B₁ B₁.transpose X₁).PosSemidef := by
      simpa [X₁] using Bt_Ainv_B_isSymm_and_fromBlocks_posSemidef A₁ B₁ hA₁
    have hWitness₂ : X₂.IsSymm ∧ (Matrix.fromBlocks A₂ B₂ B₂.transpose X₂).PosSemidef := by
      simpa [X₂] using Bt_Ainv_B_isSymm_and_fromBlocks_posSemidef A₂ B₂ hA₂
    have hBlock₁ : (Matrix.fromBlocks A₁ B₁ B₁.transpose X₁).PosSemidef := hWitness₁.2
    have hBlock₂ : (Matrix.fromBlocks A₂ B₂ B₂.transpose X₂).PosSemidef := hWitness₂.2
    -- Convexity of the PSD cone gives a feasible block matrix for the averaged data.
    have hBlockθ : (Matrix.fromBlocks Aθ Bθ Bθ.transpose Xθ).PosSemidef := by
      simpa [Aθ, Bθ, Xθ] using
        fromBlocks_convexCombination_posSemidef A₁ A₂ B₁ B₂ X₁ X₂ hBlock₁ hBlock₂ hθ₀ hθ₁
    -- The leading block stays positive definite; the endpoints are handled by simplification.
    have hAθ : Aθ.PosDef := by
      by_cases hθ_zero : θ = 0
      · subst hθ_zero
        simp [Aθ, hA₂]
      · by_cases hθ_one : θ = 1
        · subst hθ_one
          simp [Aθ, hA₁]
        · exact
            strict_convexCombination_posDef A₁ A₂ hA₁ hA₂
              (lt_of_le_of_ne hθ₀ (by simpa [eq_comm] using hθ_zero))
              (lt_of_le_of_ne hθ₁ hθ_one)
    -- Apply the trace bound to the averaged block matrix.
    have hTraceReal : Matrix.trace (Bθᵀ * Aθ⁻¹ * Bθ) ≤ Matrix.trace Xθ :=
      trace_Bt_Ainv_B_le_trace_of_fromBlocks_posSemidef Aθ Bθ Xθ hAθ hBlockθ
    have hTraceExpanded :
        Matrix.trace (Bθᵀ * Aθ⁻¹ * Bθ) ≤
          θ * Matrix.trace X₁ + (1 - θ) * Matrix.trace X₂ := by
      simpa [Xθ, Aθ, Bθ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using hTraceReal
    -- Convert the real inequality to `EReal` after expanding the traces of the endpoint witnesses.
    have hTraceEReal :
        (((Matrix.trace (Bθᵀ * Aθ⁻¹ * Bθ) : ℝ) : EReal)) ≤
          (θ : EReal) * (((Matrix.trace X₁ : ℝ) : EReal)) +
            ((1 - θ : ℝ) : EReal) * (((Matrix.trace X₂ : ℝ) : EReal)) := by
      calc
        (((Matrix.trace (Bθᵀ * Aθ⁻¹ * Bθ) : ℝ) : EReal)) ≤
            (((θ * Matrix.trace X₁ + (1 - θ) * Matrix.trace X₂ : ℝ) : EReal)) :=
          EReal.coe_le_coe_iff.mpr hTraceExpanded
        _ = (θ : EReal) * (((Matrix.trace X₁ : ℝ) : EReal)) +
              ((1 - θ : ℝ) : EReal) * (((Matrix.trace X₂ : ℝ) : EReal)) := by
          rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    simpa [X₁, X₂, Aθ, Bθ, Xθ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hTraceEReal
  constructor
  · -- Read the trace inequality directly from the Schur complement.
    intro A B X hA _ _ hBlock
    exact trace_Bt_Ainv_B_le_trace_of_fromBlocks_posSemidef A B X hA hBlock
  · -- The equality-case witness is the exact Schur-complement block matrix.
    intro A B hA _
    exact Bt_Ainv_B_isSymm_and_fromBlocks_posSemidef A B hA

end «problem-93»
