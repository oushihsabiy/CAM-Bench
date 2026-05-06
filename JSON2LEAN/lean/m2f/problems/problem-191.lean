import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-191»

/- [BLOCK Exercise 14.3-(a) | 18 | thm]
Let m,n ∈ ℕ. For i=1,ldots,m, let Kᵢ ∈ ℝ^{n×n} be given symmetric positive semidefinite matrices, Kᵢ
= K_iᵀ succeq 0, and define, for x=(x₁,ldots,xₘ) ∈ ℝ^m, K(x)=sum_{i=1}^m xᵢ Kᵢ. Let f ∈ ℝ^n be
fixed, and define E(x,f)=(1)/(2) fᵀ K(x)^{-1} f for all x ∈ ℝ^m such that K(x) succ 0. Show that
E(x,f) is a convex function of x on the set {x ∈ ℝ^m | K(x) succ 0}.
-/
open scoped BigOperators

/-- The matrix map `x ↦ ∑ i, x i • K i` sends convex combinations in the coefficient vector to
the corresponding convex combinations of matrices. -/
lemma compliance_matrix_sum_smul_add
    {m n : ℕ}
    (K : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin m → ℝ) (a b : ℝ) :
    (∑ i, ((a • x + b • y) i) • K i) =
      a • (∑ i, x i • K i) + b • (∑ i, y i • K i) := by
  -- Expand the pointwise convex combination entrywise inside the matrix-valued sum.
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  -- Regroup the resulting sum into the two scalar multiples of the endpoint matrices.
  calc
    (∑ i, (a * x i + b * y i) • K i)
        = ∑ i, ((a * x i) • K i + (b * y i) • K i) := by
            simp only [add_smul]
    _ = ∑ i, (a * x i) • K i + ∑ i, (b * y i) • K i := by
          rw [Finset.sum_add_distrib]
    _ = ∑ i, a • (x i • K i) + ∑ i, b • (y i • K i) := by
          simp only [smul_smul]
    _ = a • (∑ i, x i • K i) + b • (∑ i, y i • K i) := by
          rw [Finset.smul_sum, Finset.smul_sum]

/-- A convex combination of positive-definite real matrices is again positive definite. -/
lemma posDef_convexCombination
    {n : ℕ}
    {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • X + b • Y).PosDef := by
  -- If one coefficient vanishes, the convex combination is just the other endpoint.
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hY
  -- Otherwise the `X` part stays positive definite, and the `Y` part only needs to stay PSD.
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hXscaled : (a • X).PosDef := hX.smul ha_pos
    have hYscaled : (b • Y).PosSemidef := hY.posSemidef.smul hb
    simpa using hXscaled.add_posSemidef hYscaled

/-- The fixed one-column block witness rewrites the Schur-complement trace into the inverse
quadratic form `fᵀ M f`. -/
lemma compliance_block_trace_eq
    {n : ℕ}
    (f : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace
        ((Matrix.replicateCol (Fin 1) f)ᵀ * M * Matrix.replicateCol (Fin 1) f) =
      dotProduct f (M.mulVec f) := by
  -- Cycle the trace until the replicated column and row are adjacent to the matrix product.
  rw [Matrix.trace_mul_cycle (A := (Matrix.replicateCol (Fin 1) f)ᵀ)
    (B := M) (C := Matrix.replicateCol (Fin 1) f)]
  rw [Matrix.trace_mul_cycle (A := Matrix.replicateCol (Fin 1) f)
    (B := (Matrix.replicateCol (Fin 1) f)ᵀ) (C := M)]
  -- Rewrite the product with the fixed column as a replicated copy of `M.mulVec f`.
  rw [← Matrix.replicateCol_mulVec, Matrix.transpose_replicateCol]
  -- The trace of the resulting rank-one matrix is the desired dot product.
  simpa [dotProduct_comm] using
    (Matrix.trace_replicateCol_mul_replicateRow
      (ι := Fin 1) (a := M.mulVec f) (b := f))

/-- The inverse quadratic form associated to a fixed vector is convex on the positive-definite
cone. -/
lemma compliance_quadratic_convexCombination_le
    {n : ℕ}
    (f : Fin n → ℝ)
    {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    dotProduct f (((a • X + b • Y)⁻¹).mulVec f) ≤
      a * dotProduct f (X⁻¹.mulVec f) + b * dotProduct f (Y⁻¹.mulVec f) := by
  let B : Matrix (Fin n) (Fin 1) ℝ := Matrix.replicateCol (Fin 1) f
  let Sx : Matrix (Fin 1) (Fin 1) ℝ := Bᵀ * X⁻¹ * B
  let Sy : Matrix (Fin 1) (Fin 1) ℝ := Bᵀ * Y⁻¹ * B
  let Aθ : Matrix (Fin n) (Fin n) ℝ := a • X + b • Y
  let Sθ : Matrix (Fin 1) (Fin 1) ℝ := a • Sx + b • Sy
  have hAθ : Aθ.PosDef := by
    -- The averaged leading block stays positive definite, so the Schur complement is defined.
    simpa [Aθ] using posDef_convexCombination hX hY ha hb hab
  have hSchurX : (Sx - Bᵀ * X⁻¹ * B).PosSemidef := by
    -- The endpoint witness has zero Schur complement.
    simpa [Sx] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef)
  have hSchurY : (Sy - Bᵀ * Y⁻¹ * B).PosSemidef := by
    -- The second endpoint satisfies the same exact witness identity.
    simpa [Sy] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef)
  have hBlockX : (Matrix.fromBlocks X B Bᵀ Sx).PosSemidef := by
    -- Apply the Schur-complement equivalence to package the `X` endpoint as a PSD block matrix.
    letI : Invertible X := hX.isUnit.invertible
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosDef.fromBlocks₁₁ (A := X) B Sx hX).mpr hSchurX
  have hBlockY : (Matrix.fromBlocks Y B Bᵀ Sy).PosSemidef := by
    -- The same block construction works for the `Y` endpoint.
    letI : Invertible Y := hY.isUnit.invertible
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosDef.fromBlocks₁₁ (A := Y) B Sy hY).mpr hSchurY
  have hBcombine : a • B + b • B = B := by
    -- The fixed block column does not move under averaging because `a + b = 1`.
    rw [← add_smul, hab, one_smul]
  have hBtcombine : a • Bᵀ + b • Bᵀ = Bᵀ := by
    -- The same averaging identity holds for the transposed block row.
    rw [← add_smul, hab, one_smul]
  have hBlockθ : (Matrix.fromBlocks Aθ B Bᵀ Sθ).PosSemidef := by
    -- Positive semidefinite block witnesses are stable under convex combinations.
    have hScaledX : (a • Matrix.fromBlocks X B Bᵀ Sx).PosSemidef := hBlockX.smul ha
    have hScaledY : (b • Matrix.fromBlocks Y B Bᵀ Sy).PosSemidef := hBlockY.smul hb
    simpa [Aθ, Sθ, Matrix.fromBlocks_smul, Matrix.fromBlocks_add, hBcombine, hBtcombine,
      Matrix.transpose_add, Matrix.transpose_smul] using hScaledX.add hScaledY
  have hSchurθ : (Sθ - Bᵀ * Aθ⁻¹ * B).PosSemidef := by
    -- The averaged feasible block matrix yields a PSD Schur-complement slack.
    letI : Invertible Aθ := hAθ.isUnit.invertible
    have hSchur :=
      (Matrix.PosDef.fromBlocks₁₁ (A := Aθ) B Sθ hAθ).mp <|
        by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hBlockθ
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hSchur
  have hTraceNonneg : 0 ≤ Matrix.trace (Sθ - Bᵀ * Aθ⁻¹ * B) := by
    -- Taking traces preserves nonnegativity on positive-semidefinite real matrices.
    exact Matrix.PosSemidef.trace_nonneg hSchurθ
  have hTraceLe : Matrix.trace (Bᵀ * Aθ⁻¹ * B) ≤ Matrix.trace Sθ := by
    -- Expanding the trace of the Schur-complement slack produces the desired scalar inequality.
    rw [Matrix.trace_sub] at hTraceNonneg
    linarith
  have hTraceLe' :
      Matrix.trace (Bᵀ * Aθ⁻¹ * B) ≤
        a * Matrix.trace (Bᵀ * X⁻¹ * B) + b * Matrix.trace (Bᵀ * Y⁻¹ * B) := by
    -- The `1 × 1` witness matrix `Sθ` is the linear convex combination of the endpoint traces.
    simpa [Sθ, Sx, Sy, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, mul_add, add_mul,
      mul_assoc, mul_left_comm, mul_comm] using hTraceLe
  -- Translate the trace inequality back to the original quadratic forms.
  have hTraceAθ :
      Matrix.trace (Bᵀ * Aθ⁻¹ * B) = dotProduct f (Aθ⁻¹.mulVec f) := by
    simpa [B] using compliance_block_trace_eq f Aθ⁻¹
  have hTraceX :
      Matrix.trace (Bᵀ * X⁻¹ * B) = dotProduct f (X⁻¹.mulVec f) := by
    simpa [B] using compliance_block_trace_eq f X⁻¹
  have hTraceY :
      Matrix.trace (Bᵀ * Y⁻¹ * B) = dotProduct f (Y⁻¹.mulVec f) := by
    simpa [B] using compliance_block_trace_eq f Y⁻¹
  rw [hTraceAθ, hTraceX, hTraceY] at hTraceLe'
  simpa [Aθ] using hTraceLe'

theorem complianceEnergy_convexOn
    {m n : ℕ}
    (K : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hKsymm : ∀ i, (K i).IsSymm)
    (hKpsd : ∀ i, Matrix.PosSemidef (K i))
    (f : Fin n → ℝ) :
    ConvexOn ℝ
      {x : Fin m → ℝ | Matrix.PosDef (∑ i, x i • K i)}
      (fun x => (1 / 2 : ℝ) * dotProduct f (((∑ i, x i • K i)⁻¹).mulVec f)) := by
  let A : (Fin m → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun x => ∑ i, x i • K i
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    -- Rewrite the matrix generated by the convex combination of coefficient vectors.
    have hAcombo : A (a • x + b • y) = a • A x + b • A y := by
      simpa [A] using compliance_matrix_sum_smul_add K x y a b
    -- The positive-definite cone is convex, so the admissible coefficient set is convex.
    change Matrix.PosDef (A (a • x + b • y))
    rw [hAcombo]
    exact posDef_convexCombination hx hy ha hb hab
  · intro x hx y hy a b ha hb hab
    -- Rewrite the matrix-valued affine map before applying matrix-cone convexity.
    have hAcombo : A (a • x + b • y) = a • A x + b • A y := by
      simpa [A] using compliance_matrix_sum_smul_add K x y a b
    have hQuad :
        dotProduct f (((a • A x + b • A y)⁻¹).mulVec f) ≤
          a * dotProduct f ((A x)⁻¹.mulVec f) + b * dotProduct f ((A y)⁻¹.mulVec f) := by
      -- Apply the fixed-vector Schur-complement convexity lemma on the positive-definite cone.
      exact compliance_quadratic_convexCombination_le f hx hy ha hb hab
    have hScaled :
        (1 / 2 : ℝ) * dotProduct f (((a • A x + b • A y)⁻¹).mulVec f) ≤
          (1 / 2 : ℝ) *
            (a * dotProduct f ((A x)⁻¹.mulVec f) + b * dotProduct f ((A y)⁻¹.mulVec f)) :=
      mul_le_mul_of_nonneg_left hQuad (by norm_num)
    -- Multiply the Jensen inequality by the nonnegative constant `1 / 2` and expand the RHS.
    change
      (1 / 2 : ℝ) * dotProduct f (((A (a • x + b • y))⁻¹).mulVec f) ≤
        a * ((1 / 2 : ℝ) * dotProduct f ((A x)⁻¹.mulVec f)) +
          b * ((1 / 2 : ℝ) * dotProduct f ((A y)⁻¹.mulVec f))
    rw [hAcombo]
    simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hScaled

end «problem-191»
