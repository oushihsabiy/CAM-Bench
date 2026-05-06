import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open scoped MatrixOrder
open Filter
open scoped BigOperators

namespace «problem-18»
/-
For a cone $K ⊆ 𝕊^n$, its dual cone is defined by $$K^*: = {Y ∈ 𝕊^n | ⟨ Y, X ⟩ ≥ 0 for all X ∈ K}.
$$
-/
def dualCone {n : ℕ}
    (K : Set (Matrix (Fin n) (Fin n) ℝ)) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {Y | Y.IsSymm ∧ ∀ X, X ∈ K → Matrix.trace (Y * X) ≥ 0}

/-
A cone $K$ in an inner - product space is called self - dual if $K^* = K$, where $$K^*: = {y | ⟨ y,
x ⟩
≥ 0 for all x ∈ K}. $$
-/
def IsSelfDualCone {n : ℕ}
    (K : Set (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  dualCone K = K

/-
Let 𝕊^n be the vector space consisting of all n × n real symmetric matrices, with inner product
defined by ⟨ X, Y⟩: = tr(XY), ∀ X, Y ∈ 𝕊^n. Define the positive semidefinite cone 𝕊_ + ^n: = {X ∈
𝕊^n
| X ⪰ 0}, where X ⪰ 0 means that X is a positive semidefinite matrix. For any cone K ⊆ 𝕊^n, its dual
cone is defined by K^*: = {Y ∈ 𝕊^n | ⟨ Y, X⟩ ≥ 0, ∀ X ∈ K}. Prove that (𝕊_ + ^n)^* = 𝕊_ + ^n. That
is,
𝕊_ + ^n is a self - dual cone.
-/
/-- Over `ℝ`, the displayed symmetric quadratic-form predicate is exactly positive semidefiniteness. -/
lemma mem_psdPredicate_iff_posSemidef {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    (X.IsSymm ∧ ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (X.mulVec v)) ↔ X.PosSemidef := by
  -- Rewrite the ad hoc predicate into the standard Hermitian PSD characterization.
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨hSymm, hQuadratic⟩
    constructor
    · simpa [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]
        using hSymm
    · simpa using hQuadratic
  · rintro ⟨hHermitian, hQuadratic⟩
    constructor
    · simpa [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]
        using hHermitian
    · simpa using hQuadratic

/-- Testing against a rank-one matrix recovers the corresponding quadratic form. -/
lemma trace_mul_vecMulVec_self_eq_dotProduct {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Matrix.trace (A * Matrix.vecMulVec v v) = dotProduct v (A.mulVec v) := by
  -- Multiply first so the trace becomes the dot product of the resulting rank-one matrix.
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  simpa using (dotProduct_comm (A.mulVec v) v)

/-- The trace pairing of two real positive semidefinite matrices is nonnegative. -/
lemma trace_mul_nonneg_of_posSemidef {n : ℕ}
    {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ Matrix.trace (Y * X) := by
  -- Factor `Y` as `Bᴴ * B`, then cyclically move the trace to a visibly PSD matrix.
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  have htrace : 0 ≤ Matrix.trace (B * X * star B) := by
    simpa using (hX.mul_mul_conjTranspose_same B).trace_nonneg
  rw [Matrix.trace_mul_cycle B X (star B)] at htrace
  simpa using htrace

theorem psdCone_isSelfDual {n : ℕ} :
    IsSelfDualCone
      {X : Matrix (Fin n) (Fin n) ℝ |
        X.IsSymm ∧ ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (X.mulVec v)} := by
  let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {X : Matrix (Fin n) (Fin n) ℝ |
      X.IsSymm ∧ ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (X.mulVec v)}
  suffices hK : dualCone K = K by
    simpa [IsSelfDualCone, K] using hK
  ext Y
  constructor
  · intro hY
    have hYpsd : Y.PosSemidef := by
      -- Test the dual inequality on rank-one PSD matrices to recover every quadratic form.
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
      · simpa [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]
          using hY.1
      · intro v
        have hvpsd : (Matrix.vecMulVec v v).PosSemidef := by
          simpa using Matrix.posSemidef_vecMulVec_self_star v
        have hvK : Matrix.vecMulVec v v ∈ K := by
          simpa [K] using (mem_psdPredicate_iff_posSemidef (Matrix.vecMulVec v v)).2 hvpsd
        have htrace : 0 ≤ Matrix.trace (Y * Matrix.vecMulVec v v) := hY.2 _ hvK
        simpa [trace_mul_vecMulVec_self_eq_dotProduct] using htrace
    -- Convert back from the standard PSD API to the displayed set predicate.
    simpa [K] using (mem_psdPredicate_iff_posSemidef Y).2 hYpsd
  · intro hY
    have hYpsd : Y.PosSemidef := (mem_psdPredicate_iff_posSemidef Y).1 (by simpa [K] using hY)
    constructor
    · simpa [K] using hY.1
    · intro X hX
      have hXpsd : X.PosSemidef := (mem_psdPredicate_iff_posSemidef X).1 (by simpa [K] using hX)
      -- The trace pairing is nonnegative because both matrices are PSD.
      exact trace_mul_nonneg_of_posSemidef hXpsd hYpsd
end «problem-18»
