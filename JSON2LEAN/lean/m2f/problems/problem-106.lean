import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-106»
/-
Let S_{+ +}^n be the set of real symmetric positive - definite n×n matrices. Define f(X) = tr(X^{-
1}).
Prove that f is convex on S_{+ +}^n.
-/

/-- A real positive-definite matrix is symmetric because conjugation is trivial over `ℝ`. -/
lemma isSymm_of_posDef_real {n : Type} {X : Matrix n n ℝ} (hX : X.PosDef) : X.IsSymm := by
  -- Convert Hermitian symmetry into ordinary symmetry using the trivial star on `ℝ`.
  simpa [Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hX.isHermitian

/-- The cone of real positive-definite matrices is convex. -/
lemma convex_setOf_posDef (n : Type) [Fintype n] [DecidableEq n] :
    Convex ℝ {X : Matrix n n ℝ | X.PosDef} := by
  intro X hX Y hY a b ha hb hab
  -- Split off the degenerate weights so the remaining case has strictly positive scalars.
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by nlinarith
    simpa [ha0, hb1] using hY
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by nlinarith
    simpa [hb0, ha1] using hX
  -- Route correction: `PosDef.smul` needs strict positivity, so the interior case is handled
  -- after excluding the zero-weight boundary cases.
  have ha' : 0 < a := lt_of_le_of_ne ha fun h => ha0 h.symm
  have hb' : 0 < b := lt_of_le_of_ne hb fun h => hb0 h.symm
  exact (hX.smul ha').add (hY.smul hb')

/-- The Schur-complement argument giving matrix convexity of inversion on the positive-definite cone. -/
lemma inv_convexCombination_posSemidef
    {n : Type} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℝ} (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ((a • X⁻¹ + b • Y⁻¹) - (a • X + b • Y)⁻¹).PosSemidef := by
  have hXY : (a • X + b • Y).PosDef := convex_setOf_posDef n hX hY ha hb hab
  letI := hX.isUnit.invertible
  have hBlockX : (Matrix.fromBlocks X⁻¹ (1 : Matrix n n ℝ) 1 X).PosSemidef := by
    -- The Schur complement is zero, so the `X` block matrix is positive semidefinite.
    simpa using
      (Matrix.PosDef.fromBlocks₂₂ (A := X⁻¹) (B := (1 : Matrix n n ℝ)) (hD := hX)).2
        (by simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℝ).PosSemidef))
  letI := hY.isUnit.invertible
  have hBlockY : (Matrix.fromBlocks Y⁻¹ (1 : Matrix n n ℝ) 1 Y).PosSemidef := by
    -- The same Schur-complement computation works for `Y`.
    simpa using
      (Matrix.PosDef.fromBlocks₂₂ (A := Y⁻¹) (B := (1 : Matrix n n ℝ)) (hD := hY)).2
        (by simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℝ).PosSemidef))
  have hBlock :
      (Matrix.fromBlocks (a • X⁻¹ + b • Y⁻¹) (1 : Matrix n n ℝ)
        ((1 : Matrix n n ℝ)ᴴ) (a • X + b • Y)).PosSemidef := by
    -- Take the convex combination of the two PSD block matrices.
    have hOne : a • (1 : Matrix n n ℝ) + b • (1 : Matrix n n ℝ) = 1 := by
      simpa [hab] using (add_smul a b (1 : Matrix n n ℝ)).symm
    have hWeighted :
        (a • Matrix.fromBlocks X⁻¹ (1 : Matrix n n ℝ) 1 X
          + b • Matrix.fromBlocks Y⁻¹ (1 : Matrix n n ℝ) 1 Y).PosSemidef :=
      (hBlockX.smul ha).add (hBlockY.smul hb)
    simpa [Matrix.fromBlocks_add, Matrix.fromBlocks_smul, hOne] using hWeighted
  letI := hXY.isUnit.invertible
  -- Apply the Schur-complement characterization one last time to read off the target matrix.
  simpa using
    (Matrix.PosDef.fromBlocks₂₂
      (A := a • X⁻¹ + b • Y⁻¹) (B := (1 : Matrix n n ℝ)) (hD := hXY)).1 hBlock

/-- Taking traces of the PSD inverse gap yields the Jensen inequality for `trace ∘ inv`. -/
lemma trace_inv_convexCombination_le
    {n : Type} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℝ} (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Matrix.trace ((a • X + b • Y)⁻¹) ≤ Matrix.trace (a • X⁻¹ + b • Y⁻¹) := by
  have hPSD := inv_convexCombination_posSemidef hX hY ha hb hab
  -- Nonnegativity of the trace converts the PSD statement into the required inequality.
  have hTraceNonneg :
      0 ≤ Matrix.trace (((a • X⁻¹ + b • Y⁻¹) - (a • X + b • Y)⁻¹)) :=
    Matrix.PosSemidef.trace_nonneg hPSD
  simpa [Matrix.trace_sub, sub_nonneg] using hTraceNonneg

theorem trace_inv_convexOn_posDef
    (n : Type) [Fintype n] [DecidableEq n] :
    ConvexOn ℝ
      {X : Matrix n n ℝ | X.IsSymm ∧ X.PosDef}
      (fun X => Matrix.trace X⁻¹) := by
  refine ⟨?_, ?_⟩
  · intro X hX Y hY a b ha hb hab
    -- The explicit symmetry hypothesis is redundant once positive definiteness is known.
    have hXY : (a • X + b • Y).PosDef := convex_setOf_posDef n hX.2 hY.2 ha hb hab
    exact ⟨isSymm_of_posDef_real hXY, hXY⟩
  · intro X hX Y hY a b ha hb hab
    -- First obtain the trace inequality coming from the Schur-complement PSD gap.
    have hTrace :=
      trace_inv_convexCombination_le hX.2 hY.2 ha hb hab
    calc
      Matrix.trace ((a • X + b • Y)⁻¹)
          ≤ Matrix.trace (a • X⁻¹ + b • Y⁻¹) := hTrace
      _ = a • Matrix.trace X⁻¹ + b • Matrix.trace Y⁻¹ := by
            simp [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]

end «problem-106»
