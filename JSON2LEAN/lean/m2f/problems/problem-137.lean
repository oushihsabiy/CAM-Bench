import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-137»

/- [BLOCK chapter2 Ex.2.11-(b) | 9 | defn]
A function f : C₁ × C₂ → ℝ cup {+∞} is jointly convex in (x,y) if, for all (x₁,y₁),(x₂,y₂) ∈ C₁
× C₂ and all θ ∈ [0,1],
f(θ x₁+(1-θ)x₂,θ y₁+(1-θ)y₂) ≤ θ f(x₁,y₁)+(1-θ)f(x₂,y₂).
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

/- [BLOCK chapter2 Ex.2.11-(b) | 10 | defn]
A semidefinite program is an optimization problem in which the decision variable is a symmetric
matrix, the objective function is linear in the decision variables, and the constraints include a
linear matrix inequality of the form F₀ + sum_i=1^p xᵢ Fᵢ succeq 0.
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
  
def SemidefiniteProgram.matrix {n p : ℕ} (sdp : SemidefiniteProgram n p) :
    Matrix (Fin n) (Fin n) ℝ :=
  sdp.F0 + ∑ i : Fin p, sdp.x i • sdp.F i

def SemidefiniteProgram.lmiMatrix {n p : ℕ} (sdp : SemidefiniteProgram n p) :
    Matrix (Fin n) (Fin n) ℝ :=
  sdp.X

def SemidefiniteProgram.objectiveValue {n p : ℕ} (sdp : SemidefiniteProgram n p) : ℝ :=
  sdp.objective sdp.X

def SemidefiniteProgram.IsFeasible {n p : ℕ} (sdp : SemidefiniteProgram n p) : Prop :=
  sdp.X = sdp.matrix ∧ sdp.X.PosSemidef

/- [BLOCK chapter2 Ex.2.11-(b) | 11 | opt_prob]
Let A ∈ S_++^m and B ∈ ℝ^m × n. Consider the semidefinite program with decision variable X
∈ S^n:
min_X ∈ S^n Tr(X)
quad
subject to
quad
(
A & B ; B^→p & X
) succeq 0.
-/
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

def TraceMinimizationSDP.objFun {m n : ℕ} (_p : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace X

/- [BLOCK chapter2 Ex.2.11-(b) | 12 | thm]
Let S^n be the set of all n × n real symmetric matrices, and let S_{++}^m be the set of all m × m
real symmetric positive definite matrices. Given A ∈ S_{++}^m and B ∈ ℝ^{m × n}, consider the trace
minimization semidefinite program. Define the function f(A,B)=Tr(B^→p A^{-1}B), with domain domf =
S_{++}^m × ℝ^{m × n}. Prove that the function f(A,B) is jointly convex in the pair of variables
(A,B) on domf.
-/
theorem trace_Bt_Ainv_B_jointlyConvex :
    JointlyConvex
      {A : Matrix (Fin m) (Fin m) ℝ | A.IsSymm ∧ A.PosDef}
      (Set.univ : Set (Matrix (Fin m) (Fin n) ℝ))
      (fun p : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ =>
        ((Matrix.trace (p.2ᵀ * p.1⁻¹ * p.2) : ℝ) : EReal)) := by
  intro A₁ A₂ hA₁ hA₂ B₁ B₂ _ _ θ hθ₀ hθ₁
  rcases hA₁ with ⟨hA₁_symm, hA₁_posDef⟩
  rcases hA₂ with ⟨hA₂_symm, hA₂_posDef⟩
  set a : ℝ := θ
  set b : ℝ := 1 - θ
  set Aθ : Matrix (Fin m) (Fin m) ℝ := a • A₁ + b • A₂
  set Bθ : Matrix (Fin m) (Fin n) ℝ := a • B₁ + b • B₂
  set S₁ : Matrix (Fin n) (Fin n) ℝ := B₁ᵀ * A₁⁻¹ * B₁
  set S₂ : Matrix (Fin n) (Fin n) ℝ := B₂ᵀ * A₂⁻¹ * B₂
  set Sθ : Matrix (Fin n) (Fin n) ℝ := a • S₁ + b • S₂
  have ha_nonneg : 0 ≤ a := by
    simpa [a] using hθ₀
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    linarith
  have hAθ_posDef : Aθ.PosDef := by
    -- One convex coefficient may vanish, so we keep the positive-definite part on the side
    -- with strictly positive weight and add the other side as positive semidefinite.
    by_cases hθ_eq_one : θ = 1
    · simpa [Aθ, a, b, hθ_eq_one] using hA₁_posDef
    · have hb_pos : 0 < b := by
        dsimp [b]
        have hθ_lt_one : θ < 1 := lt_of_le_of_ne hθ₁ hθ_eq_one
        linarith
      have hA₁_psd : (a • A₁).PosSemidef := by
        exact hA₁_posDef.posSemidef.smul ha_nonneg
      have hA₂_pd : (b • A₂).PosDef := by
        exact hA₂_posDef.smul hb_pos
      simpa [Aθ] using Matrix.PosDef.posSemidef_add hA₁_psd hA₂_pd
  have hAθ_symm : Aθ.IsSymm := by
    -- The convex combination stays in the symmetric cone because transpose commutes with
    -- both addition and scalar multiplication over `ℝ`.
    exact (hA₁_symm.smul a).add (hA₂_symm.smul b)
  have hBlock₁ : (Matrix.fromBlocks A₁ B₁ B₁ᵀ S₁).PosSemidef := by
    -- Route correction: instead of expanding the inverse expression directly, use the
    -- Schur-complement equivalence with zero Schur complement at the canonical witness `S₁`.
    letI : Invertible A₁ := hA₁_posDef.isUnit.invertible
    have hSchur₁ : (S₁ - B₁ᴴ * A₁⁻¹ * B₁).PosSemidef := by
      simpa [S₁, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosDef.fromBlocks₁₁ (A := A₁) B₁ S₁ hA₁_posDef).2 hSchur₁
  have hBlock₂ : (Matrix.fromBlocks A₂ B₂ B₂ᵀ S₂).PosSemidef := by
    -- The second endpoint satisfies the same Schur-complement certificate.
    letI : Invertible A₂ := hA₂_posDef.isUnit.invertible
    have hSchur₂ : (S₂ - B₂ᴴ * A₂⁻¹ * B₂).PosSemidef := by
      simpa [S₂, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosDef.fromBlocks₁₁ (A := A₂) B₂ S₂ hA₂_posDef).2 hSchur₂
  have hBlockθ : (Matrix.fromBlocks Aθ Bθ Bθᵀ Sθ).PosSemidef := by
    -- Feasibility is preserved by convex combinations because positive semidefinite matrices
    -- are closed under nonnegative scaling and addition.
    have hScaled₁ : (a • Matrix.fromBlocks A₁ B₁ B₁ᵀ S₁).PosSemidef := hBlock₁.smul ha_nonneg
    have hScaled₂ : (b • Matrix.fromBlocks A₂ B₂ B₂ᵀ S₂).PosSemidef := hBlock₂.smul hb_nonneg
    simpa [Aθ, Bθ, Sθ, Matrix.fromBlocks_smul, Matrix.fromBlocks_add,
      Matrix.transpose_smul, Matrix.transpose_add] using hScaled₁.add hScaled₂
  have hSchurθ : (Sθ - Bθᵀ * Aθ⁻¹ * Bθ).PosSemidef := by
    -- Applying the Schur-complement equivalence to the mixed feasible block matrix extracts
    -- the positive semidefinite slack `Sθ - Bθᵀ Aθ⁻¹ Bθ`.
    letI : Invertible Aθ := hAθ_posDef.isUnit.invertible
    have hSchur :=
      (Matrix.PosDef.fromBlocks₁₁ (A := Aθ) Bθ Sθ hAθ_posDef).1 <|
        by simpa [Aθ, Bθ, Sθ, Matrix.conjTranspose_eq_transpose_of_trivial] using hBlockθ
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hSchur
  have hTrace_nonneg : 0 ≤ Matrix.trace (Sθ - Bθᵀ * Aθ⁻¹ * Bθ) := by
    -- The Schur-complement slack is positive semidefinite, so its trace is nonnegative.
    exact Matrix.PosSemidef.trace_nonneg hSchurθ
  have hTrace_bound :
      Matrix.trace (Bθᵀ * Aθ⁻¹ * Bθ) ≤ Matrix.trace Sθ := by
    -- Expanding the trace of the slack converts positivity into the desired real inequality.
    rw [Matrix.trace_sub] at hTrace_nonneg
    linarith
  have hReal :
      Matrix.trace (Bθᵀ * Aθ⁻¹ * Bθ) ≤
        a * Matrix.trace S₁ + b * Matrix.trace S₂ := by
    -- The trace objective is linear, so the trace of the convex feasible witness is the
    -- corresponding convex combination of the endpoint objective values.
    simpa [Sθ, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using hTrace_bound
  -- The proof stays in `ℝ` until the last line; the `EReal` goal is just the coercion of the
  -- already established real inequality.
  exact (EReal.coe_le_coe_iff).2 <| by
    simpa [Aθ, Bθ, S₁, S₂, a, b, EReal.coe_mul, EReal.coe_add] using hReal

end «problem-137»
