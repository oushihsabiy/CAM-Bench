import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-57»

-- Exercise_3_20__c_

/- [BLOCK Exercise 3.20-(c) | 10 | thm]
Let m,n ∈ ℕ, and let Aᵢ ∈ S^m for i=0,1,dots,n, where S^m is the set of real symmetric m imes m
matrices. Define X(x)=A₀+x₁A_1+·s+x_nA_n, x=(x₁,dots,xₙ)∈ ℝ^n, and define f(x)=trigl(X(x)^{-1}igr)
on the domain dom f={x∈ ℝ^n | X(x)succ 0}, where X(x)succ 0 means that X(x) is positive definite. A
function g on a convex set C⊆ ℝ^n is convex if for all x,y∈ C and all heta∈[0,1], one has g( heta
x+(1- heta)y)≤ heta g(x)+(1- heta)g(y). Prove that f is convex on dom f.
-/
open Matrix

/-- The affine matrix map `x ↦ A 0 + ∑ i, x i • A i.succ` preserves convex combinations. -/
lemma matrixAffine_eval_smul_add
    {m n : ℕ}
    (A : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ)
    {x y : Fin n → ℝ} {a b : ℝ} (hab : a + b = 1) :
    A 0 + ∑ i : Fin n, ((a • x + b • y) i) • A i.succ =
      a • (A 0 + ∑ i : Fin n, (x i) • A i.succ) +
        b • (A 0 + ∑ i : Fin n, (y i) • A i.succ) := by
  -- Expand the pointwise affine combination and then regroup the matrix terms.
  let SX : Matrix (Fin m) (Fin m) ℝ := ∑ i : Fin n, (x i) • A i.succ
  let SY : Matrix (Fin m) (Fin m) ℝ := ∑ i : Fin n, (y i) • A i.succ
  calc
    A 0 + ∑ i : Fin n, ((a • x + b • y) i) • A i.succ
      = A 0 + ∑ i : Fin n, ((a * x i) • A i.succ + (b * y i) • A i.succ) := by
          simp [Pi.smul_apply, add_smul]
    _ = A 0 + ∑ i : Fin n, (a • ((x i) • A i.succ) + b • ((y i) • A i.succ)) := by
          simp [smul_smul]
    _ = A 0 + (a • SX + b • SY) := by
          simp [SX, SY, Finset.sum_add_distrib, Finset.smul_sum]
    _ = (a • A 0 + b • A 0) + (a • SX + b • SY) := by
          calc
            A 0 + (a • SX + b • SY) = (a + b) • A 0 + (a • SX + b • SY) := by
              rw [hab, one_smul]
            _ = (a • A 0 + b • A 0) + (a • SX + b • SY) := by
              rw [add_smul]
    _ = (a • A 0 + a • SX) + (b • A 0 + b • SY) := by ac_rfl
    _ = a • (A 0 + SX) + b • (A 0 + SY) := by rw [smul_add, smul_add]
    _ = a • (A 0 + ∑ i : Fin n, (x i) • A i.succ) +
          b • (A 0 + ∑ i : Fin n, (y i) • A i.succ) := by
          simp [SX, SY]

/-- A convex combination of positive-definite real matrices is positive definite. -/
lemma posDef_convexCombination
    {m : ℕ}
    {X Y : Matrix (Fin m) (Fin m) ℝ}
    (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • X + b • Y).PosDef := by
  -- If `a = 0`, the combination is exactly `Y`; otherwise use a positive `a` and a PSD `b • Y`.
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hY
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    exact (hX.smul ha_pos).add_posSemidef (hY.posSemidef.smul hb)

/-- Inversion is matrix convex along positive-definite real segments, in the PSD order. -/
lemma inv_convexCombination_posSemidef
    {m : ℕ}
    {X Y : Matrix (Fin m) (Fin m) ℝ}
    (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ((a • X⁻¹ + b • Y⁻¹) - (a • X + b • Y)⁻¹).PosSemidef := by
  let I : Matrix (Fin m) (Fin m) ℝ := 1
  have hXblock : (Matrix.fromBlocks X⁻¹ I Iᴴ X).PosSemidef := by
    -- The Schur complement of `[X⁻¹  I; I  X]` is zero, so the block matrix is PSD.
    letI := hX.isUnit.invertible
    have hZero :
        (X⁻¹ - I * X⁻¹ * Iᴴ).PosSemidef := by
      simpa [I] using (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin m) (Fin m) ℝ).PosSemidef)
    exact (Matrix.PosDef.fromBlocks₂₂ (A := X⁻¹) (B := I) (hD := hX)).2 hZero
  have hYblock : (Matrix.fromBlocks Y⁻¹ I Iᴴ Y).PosSemidef := by
    -- The same Schur-complement computation gives the `Y` block matrix.
    letI := hY.isUnit.invertible
    have hZero :
        (Y⁻¹ - I * Y⁻¹ * Iᴴ).PosSemidef := by
      simpa [I] using (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin m) (Fin m) ℝ).PosSemidef)
    exact (Matrix.PosDef.fromBlocks₂₂ (A := Y⁻¹) (B := I) (hD := hY)).2 hZero
  have hCombo :
      (a • Matrix.fromBlocks X⁻¹ I Iᴴ X +
        b • Matrix.fromBlocks Y⁻¹ I Iᴴ Y).PosSemidef := by
    -- Positive semidefiniteness is preserved by nonnegative scaling and addition.
    exact (hXblock.smul ha).add (hYblock.smul hb)
  have hIcombo : a • I + b • I = I := by
    -- The off-diagonal block remains the identity because the coefficients sum to `1`.
    calc
      a • I + b • I = (a + b) • I := by rw [add_smul]
      _ = I := by rw [hab, one_smul]
  have hIhcombo : a • Iᴴ + b • Iᴴ = Iᴴ := by
    simpa [I] using hIcombo
  have hComboBlocks :
      a • Matrix.fromBlocks X⁻¹ I Iᴴ X + b • Matrix.fromBlocks Y⁻¹ I Iᴴ Y =
        Matrix.fromBlocks (a • X⁻¹ + b • Y⁻¹) I Iᴴ (a • X + b • Y) := by
    -- `fromBlocks` is linear in each block, so regroup the convex combination blockwise.
    calc
      a • Matrix.fromBlocks X⁻¹ I Iᴴ X + b • Matrix.fromBlocks Y⁻¹ I Iᴴ Y
          = Matrix.fromBlocks (a • X⁻¹) (a • I) (a • Iᴴ) (a • X) +
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
    -- Apply the Schur-complement characterization to the convexly combined block matrix.
    have hCombinedBlocks :
        (Matrix.fromBlocks (a • X⁻¹ + b • Y⁻¹) I Iᴴ (a • X + b • Y)).PosSemidef := by
      rw [← hComboBlocks]
      exact hCombo
    exact (Matrix.PosDef.fromBlocks₂₂
      (A := a • X⁻¹ + b • Y⁻¹) (B := I) (hD := hBottom)).1 hCombinedBlocks
  simpa [I] using hSchur

theorem trace_inv_matrix_affine_convexOn
    {m n : ℕ}
    (A : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, IsSymm (A i)) :
    let domf : Set (Fin n → ℝ) := {x : Fin n → ℝ | PosDef (A 0 + ∑ i : Fin n, (x i) • A i.succ)}
    let f : (Fin n → ℝ) → ℝ :=
      fun x => Matrix.trace ((A 0 + ∑ i : Fin n, (x i) • A i.succ)⁻¹)
    ConvexOn ℝ domf f := by
  -- The argument uses only positivity on the chosen domain points, but the exercise includes symmetry.
  let _ := hA
  -- Introduce the affine matrix map explicitly so the convexity proof can be written once.
  let X : (Fin n → ℝ) → Matrix (Fin m) (Fin m) ℝ :=
    fun x => A 0 + ∑ i : Fin n, (x i) • A i.succ
  change ConvexOn ℝ {x : Fin n → ℝ | PosDef (X x)} (fun x => Matrix.trace ((X x)⁻¹))
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    -- The positive-definite domain is convex because `X` is affine and PD matrices are convex.
    change PosDef (X (a • x + b • y))
    rw [show X (a • x + b • y) = a • X x + b • X y by
      simpa [X] using matrixAffine_eval_smul_add A (x := x) (y := y) hab]
    exact posDef_convexCombination hx hy ha hb hab
  · intro x hx y hy a b ha hb hab
    -- The Jensen step comes from matrix convexity of inversion plus trace monotonicity on PSDs.
    change Matrix.trace ((X (a • x + b • y))⁻¹) ≤
      a • Matrix.trace ((X x)⁻¹) + b • Matrix.trace ((X y)⁻¹)
    rw [show X (a • x + b • y) = a • X x + b • X y by
      simpa [X] using matrixAffine_eval_smul_add A (x := x) (y := y) hab]
    have hInvPSD :
        ((a • (X x)⁻¹ + b • (X y)⁻¹) - (a • X x + b • X y)⁻¹).PosSemidef :=
      inv_convexCombination_posSemidef hx hy ha hb hab
    have hTrace_nonneg :
        0 ≤ Matrix.trace
          ((a • (X x)⁻¹ + b • (X y)⁻¹) - (a • X x + b • X y)⁻¹) :=
      Matrix.PosSemidef.trace_nonneg hInvPSD
    have hTrace_le :
        Matrix.trace ((a • X x + b • X y)⁻¹) ≤
          Matrix.trace (a • (X x)⁻¹ + b • (X y)⁻¹) := by
      simpa [Matrix.trace_sub] using hTrace_nonneg
    calc
      Matrix.trace ((a • X x + b • X y)⁻¹)
          ≤ Matrix.trace (a • (X x)⁻¹ + b • (X y)⁻¹) := hTrace_le
      _ = a * Matrix.trace ((X x)⁻¹) + b * Matrix.trace ((X y)⁻¹) := by
            rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
      _ = a • Matrix.trace ((X x)⁻¹) + b • Matrix.trace ((X y)⁻¹) := by
            simp [smul_eq_mul]

end «problem-57»
