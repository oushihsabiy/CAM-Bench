import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-94»

/-
A mapping f: S_{+ +}^n → S^n is matrix convex if for all X, Y ∈ S_{+ +}^n and all θ ∈ [0, 1], f(θ X
+
(1 - θ)Y) ≤ θ f(X) + (1 - θ)f(Y), where A ≤ B means that B - A is positive semidefinite.
-/
def MatrixConvex
    (f : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ ⦃X : Matrix (Fin n) (Fin n) ℝ⦄, X.IsSymm → X.PosDef → (f X).IsSymm) ∧
  ∀ ⦃X Y : Matrix (Fin n) (Fin n) ℝ⦄,
    X.IsSymm → X.PosDef → Y.IsSymm → Y.PosDef →
    ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
      (θ • X + (1 - θ) • Y).IsSymm ∧
      (θ • X + (1 - θ) • Y).PosDef ∧
      (θ • f X + (1 - θ) • f Y - f (θ • X + (1 - θ) • Y)).PosSemidef

/-- A real convex combination of positive-definite matrices is positive definite. -/
lemma posDef_convexCombination
    {n : ℕ}
    {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • X + b • Y).PosDef := by
  -- Separate the degenerate weight `a = 0`, since then the combination is exactly `Y`.
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hY
  · -- Otherwise the `a • X` part is positive definite and the `b • Y` part is positive semidefinite.
    have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    exact (hX.smul ha_pos).add_posSemidef (hY.posSemidef.smul hb)

/-- The inverse map satisfies the Jensen PSD inequality on positive-definite real matrices. -/
lemma inv_convexCombination_posSemidef
    {n : ℕ}
    {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ((a • X⁻¹ + b • Y⁻¹) - (a • X + b • Y)⁻¹).PosSemidef := by
  let I : Matrix (Fin n) (Fin n) ℝ := 1
  have hXblock : (Matrix.fromBlocks X⁻¹ I Iᴴ X).PosSemidef := by
    -- The Schur complement of `[X⁻¹  I; I  X]` is zero.
    letI := hX.isUnit.invertible
    have hZero : (X⁻¹ - I * X⁻¹ * Iᴴ).PosSemidef := by
      simpa [I] using (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
    exact (Matrix.PosDef.fromBlocks₂₂ (A := X⁻¹) (B := I) (hD := hX)).2 hZero
  have hYblock : (Matrix.fromBlocks Y⁻¹ I Iᴴ Y).PosSemidef := by
    -- The same Schur-complement computation works for `Y`.
    letI := hY.isUnit.invertible
    have hZero : (Y⁻¹ - I * Y⁻¹ * Iᴴ).PosSemidef := by
      simpa [I] using (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
    exact (Matrix.PosDef.fromBlocks₂₂ (A := Y⁻¹) (B := I) (hD := hY)).2 hZero
  have hCombo :
      (a • Matrix.fromBlocks X⁻¹ I Iᴴ X +
        b • Matrix.fromBlocks Y⁻¹ I Iᴴ Y).PosSemidef := by
    -- PSD matrices remain PSD under nonnegative scaling and addition.
    exact (hXblock.smul ha).add (hYblock.smul hb)
  have hIcombo : a • I + b • I = I := by
    -- The off-diagonal block stays equal to the identity because the weights sum to `1`.
    calc
      a • I + b • I = (a + b) • I := by rw [add_smul]
      _ = I := by rw [hab, one_smul]
  have hIhcombo : a • Iᴴ + b • Iᴴ = Iᴴ := by
    simpa [I] using hIcombo
  have hComboBlocks :
      a • Matrix.fromBlocks X⁻¹ I Iᴴ X + b • Matrix.fromBlocks Y⁻¹ I Iᴴ Y =
        Matrix.fromBlocks (a • X⁻¹ + b • Y⁻¹) I Iᴴ (a • X + b • Y) := by
    -- Regroup the convex combination blockwise using linearity of `fromBlocks`.
    calc
      a • Matrix.fromBlocks X⁻¹ I Iᴴ X + b • Matrix.fromBlocks Y⁻¹ I Iᴴ Y =
          Matrix.fromBlocks (a • X⁻¹) (a • I) (a • Iᴴ) (a • X) +
            Matrix.fromBlocks (b • Y⁻¹) (b • I) (b • Iᴴ) (b • Y) := by
              rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_smul]
      _ = Matrix.fromBlocks (a • X⁻¹ + b • Y⁻¹) (a • I + b • I) (a • Iᴴ + b • Iᴴ)
            (a • X + b • Y) := by
              rw [Matrix.fromBlocks_add]
      _ = Matrix.fromBlocks (a • X⁻¹ + b • Y⁻¹) I Iᴴ (a • X + b • Y) := by
              rw [hIcombo, hIhcombo]
  have hBottom : (a • X + b • Y).PosDef :=
    posDef_convexCombination hX hY ha hb hab
  letI := hBottom.isUnit.invertible
  have hSchur :
      ((a • X⁻¹ + b • Y⁻¹) - I * (a • X + b • Y)⁻¹ * Iᴴ).PosSemidef := by
    -- Read the Schur complement off from the convexly combined block matrix.
    have hCombinedBlocks :
        (Matrix.fromBlocks (a • X⁻¹ + b • Y⁻¹) I Iᴴ (a • X + b • Y)).PosSemidef := by
      rw [← hComboBlocks]
      exact hCombo
    exact (Matrix.PosDef.fromBlocks₂₂
      (A := a • X⁻¹ + b • Y⁻¹) (B := I) (hD := hBottom)).1 hCombinedBlocks
  -- Finally simplify the identity blocks in the Schur complement.
  simpa [I] using hSchur

/-
Let S^n be the space of real symmetric n × n matrices, and let S_{+ +}^n = {X ∈ S^n: X is positive
definite}. For X ∈ S_{+ +}^n, define f(X) = X^{- 1}. A mapping f: S_{+ +}^n → S^n is matrix convex
if
for all X, Y ∈ S_{+ +}^n and all θ ∈ [0, 1], f(θ X + (1 - θ)Y) ≤ θ f(X) + (1 - θ)f(Y), where A ≤ B
means
that B - A is positive semidefinite. Show that the mapping f: S_{+ +}^n → S^n defined by f(X) = X^{-
1}
is matrix convex on S_{+ +}^n. The statement includes the boundary cases θ = 0 and θ = 1 and the
zero-dimensional case; it also explicitly records that the positive-definite cone is closed under
the convex combination used in the Jensen inequality, so the inverse is only evaluated on its
intended positive-definite domain.
-/
theorem inverse_matrixConvex {n : ℕ} :
    MatrixConvex (fun X : Matrix (Fin n) (Fin n) ℝ => X⁻¹) := by
  constructor
  · intro X hXsymm _hXpos
    -- Symmetry is preserved by matrix inversion on symmetric real matrices.
    rw [Matrix.IsSymm]
    simpa [hXsymm.eq] using (Matrix.transpose_nonsing_inv (A := X))
  · intro X Y hXsymm hXpos hYsymm hYpos θ hθ0 hθ1
    have hOneSub : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    have hWeights : θ + (1 - θ) = 1 := by ring
    constructor
    · -- A linear combination of symmetric matrices is symmetric.
      exact (hXsymm.smul θ).add (hYsymm.smul (1 - θ))
    constructor
    · -- Positive-definite matrices stay positive definite under convex combination.
      exact posDef_convexCombination hXpos hYpos hθ0 hOneSub hWeights
    · -- The Jensen gap is PSD by the Schur-complement block-matrix argument.
      exact inv_convexCombination_posSemidef hXpos hYpos hθ0 hOneSub hWeights



end «problem-94»
