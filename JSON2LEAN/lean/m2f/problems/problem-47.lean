import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-47»
/-
Exercise 3.13 | 11 | thm

Let Sⁿ be the set of n × n real symmetric matrices, S₊₊ⁿ ⊂ Sⁿ the set of real symmetric positive
definite matrices, and for M, N ∈ Sⁿ, let M ≼ N mean that N − M is positive semidefinite. Let I
denote the n × n identity matrix, and let tr denote the trace.

For A, B ∈ S₊₊ⁿ, define
H(A, B) = 2(A⁻¹ + B⁻¹)⁻¹.

Show that
X = (A⁻¹ + B⁻¹)⁻¹
solves the semidefinite program
trace-maximization semidefinite program.

Let
R = [A⁻¹  I; B⁻¹  −I].

Verify that R is nonsingular, and apply the congruence transformation defined by R to the matrix
inequality above to obtain
Rᵀ[X  X; X  X]R ≼ Rᵀ[A  0; 0  B]R.
-/
theorem harmonic_mean_matrix_solves_trace_maximization_sdp
    {n : ℕ}
    (A B X : Matrix (Fin n) (Fin n) ℝ)
    (hA_symm : A.IsSymm)
    (hB_symm : B.IsSymm)
    (hA_pos : A.PosDef)
    (hB_pos : B.PosDef)
    (hX : X = (A⁻¹ + B⁻¹)⁻¹) :
    X.IsSymm ∧
      (Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin n) ℝ)
        (0 : Matrix (Fin n) (Fin n) ℝ) B -
        Matrix.fromBlocks X X X X).PosSemidef ∧
      (∀ Y : Matrix (Fin n) (Fin n) ℝ,
        Y.IsSymm →
          (Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin n) ℝ)
            (0 : Matrix (Fin n) (Fin n) ℝ) B -
            Matrix.fromBlocks Y Y Y Y).PosSemidef →
          Matrix.trace Y ≤ Matrix.trace X) ∧
      let R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
        Matrix.fromBlocks A⁻¹ (1 : Matrix (Fin n) (Fin n) ℝ) B⁻¹
          (-1 : Matrix (Fin n) (Fin n) ℝ)
      R.det ≠ 0 ∧
        (R.transpose * Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin n) ℝ)
            (0 : Matrix (Fin n) (Fin n) ℝ) B * R -
          R.transpose * Matrix.fromBlocks X X X X * R).PosSemidef := by
  classical
  let S : Matrix (Fin n) (Fin n) ℝ := A⁻¹ + B⁻¹
  let R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
    Matrix.fromBlocks A⁻¹ (1 : Matrix (Fin n) (Fin n) ℝ) B⁻¹
      (-1 : Matrix (Fin n) (Fin n) ℝ)
  let slack (Y : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
    Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin n) ℝ)
        (0 : Matrix (Fin n) (Fin n) ℝ) B -
      Matrix.fromBlocks Y Y Y Y
  -- The harmonic-mean inverse sum is positive definite and symmetric.
  have hS_pos : S.PosDef := by
    dsimp [S]
    exact hA_pos.inv.add hB_pos.inv
  have hS_symm : S.IsSymm := by
    dsimp [S]
    simpa using hA_symm.inv.add hB_symm.inv
  letI := hA_pos.isUnit.invertible
  letI := hB_pos.isUnit.invertible
  letI := hS_pos.isUnit.invertible
  have hA_add_B_pos : (A + B).PosDef := hA_pos.add hB_pos
  -- The target matrix is the inverse of a symmetric matrix, hence symmetric.
  have hX_symm : X.IsSymm := by
    rw [hX]
    simpa [S] using hS_symm.inv
  -- Multiplying the block slack on the right by `R` performs the first elimination step.
  have hSlack_mul_R (Y : Matrix (Fin n) (Fin n) ℝ) :
      slack Y * R =
        Matrix.fromBlocks (1 - Y * S) A (1 - Y * S) (-B) := by
    dsimp [slack, R, S]
    rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    constructor
    · simp [sub_eq_add_neg, add_mul, mul_add]
      abel_nf
    constructor
    · simp
    constructor
    · simp [sub_eq_add_neg, add_mul, mul_add]
      abel_nf
    · simp
  -- A second multiplication by `Rᵀ` diagonalizes the transformed slack.
  have hCongruence (Y : Matrix (Fin n) (Fin n) ℝ) :
      R.transpose * slack Y * R =
        Matrix.fromBlocks (S - S * Y * S) (0 : Matrix (Fin n) (Fin n) ℝ)
          (0 : Matrix (Fin n) (Fin n) ℝ) (A + B) := by
    dsimp [R]
    rw [Matrix.fromBlocks_transpose]
    rw [show
      (Matrix.fromBlocks A⁻¹ᵀ B⁻¹ᵀ (1 : Matrix (Fin n) (Fin n) ℝ)ᵀ
          (-1 : Matrix (Fin n) (Fin n) ℝ)ᵀ :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
        Matrix.fromBlocks A⁻¹ B⁻¹ (1 : Matrix (Fin n) (Fin n) ℝ)
          (-1 : Matrix (Fin n) (Fin n) ℝ) by
      simp [hA_symm.inv.eq, hB_symm.inv.eq]]
    rw [Matrix.mul_assoc, hSlack_mul_R, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj]
    constructor
    · simp [S, sub_eq_add_neg, add_mul, mul_add, mul_assoc]
      abel_nf
    constructor
    · simp
    constructor
    · simp
    · simp
  -- The diagonalized slack at `X` collapses to a block diagonal PSD matrix.
  have hS_mul_X_mul_S : S * X * S = S := by
    calc
      S * X * S = (S * X) * S := by rw [Matrix.mul_assoc]
      _ = (S * S⁻¹) * S := by rw [hX]
      _ = 1 * S := by rw [Matrix.mul_inv_of_invertible]
      _ = S := by simp
  have hBlock_psd :
      (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) ℝ)
          (0 : Matrix (Fin n) (Fin n) ℝ) (0 : Matrix (Fin n) (Fin n) ℝ)
          (A + B)).PosSemidef := by
    letI := hA_add_B_pos.isUnit.invertible
    have hZeroSchur :
        ((0 : Matrix (Fin n) (Fin n) ℝ) -
          (0 : Matrix (Fin n) (Fin n) ℝ) * (A + B)⁻¹ *
            (0 : Matrix (Fin n) (Fin n) ℝ)ᴴ).PosSemidef := by
      simpa using Matrix.PosSemidef.zero
    exact (Matrix.PosDef.fromBlocks₂₂ (A := (0 : Matrix (Fin n) (Fin n) ℝ))
      (B := (0 : Matrix (Fin n) (Fin n) ℝ)) (hD := hA_add_B_pos)).2
      hZeroSchur
  have hTransformed_slack_X : (R.transpose * slack X * R).PosSemidef := by
    have hTopZero : S - S * X * S = 0 := by
      rw [hS_mul_X_mul_S, sub_self]
    rw [hCongruence X, hTopZero]
    simpa using hBlock_psd
  -- `R` is invertible by a Schur-complement argument, so the original slack is also PSD.
  have hR_unit : IsUnit R := by
    letI : Invertible (-1 : Matrix (Fin n) (Fin n) ℝ) := by
      refine ⟨-1, ?_, ?_⟩ <;> simp
    have hNegOneInv : ((-1 : Matrix (Fin n) (Fin n) ℝ)⁻¹) = -1 := by
      rw [Matrix.nonsing_inv_eq_ringInverse]
      simpa using (Ring.inverse_unit (-1 : (Matrix (Fin n) (Fin n) ℝ)ˣ))
    have hSchur :
        IsUnit (A⁻¹ - (1 : Matrix (Fin n) (Fin n) ℝ) *
          ⅟(-1 : Matrix (Fin n) (Fin n) ℝ) * B⁻¹) := by
      rw [Matrix.invOf_eq_nonsing_inv, hNegOneInv]
      simpa [S, sub_eq_add_neg] using hS_pos.isUnit
    dsimp [R]
    exact (Matrix.isUnit_fromBlocks_iff_of_invertible₂₂
      (A := A⁻¹) (B := (1 : Matrix (Fin n) (Fin n) ℝ))
      (C := B⁻¹) (D := (-1 : Matrix (Fin n) (Fin n) ℝ))).2 hSchur
  have hSlack_X_psd : (slack X).PosSemidef := by
    have hStarCongruence : (star R * slack X * R).PosSemidef := by
      simpa [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using hTransformed_slack_X
    exact
      (Matrix.IsUnit.posSemidef_star_left_conjugate_iff
        (U := R) (x := slack X) hR_unit).mp hStarCongruence
  -- Feasible slacks stay PSD after conjugation by `R`, and the top-left block is `S * (X - Y) * S`.
  have hTrace_bound :
      ∀ Y : Matrix (Fin n) (Fin n) ℝ,
        Y.IsSymm → (slack Y).PosSemidef → Matrix.trace Y ≤ Matrix.trace X := by
    intro Y hY_symm hY_slack
    let _ := hY_symm
    have hTransformed_Y : (R.transpose * slack Y * R).PosSemidef := by
      have hConjugated := hY_slack.conjTranspose_mul_mul_same R
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hConjugated
    have hTopLeft_psd : (S - S * Y * S).PosSemidef := by
      have hDiagonal_psd :
          (Matrix.fromBlocks (S - S * Y * S) (0 : Matrix (Fin n) (Fin n) ℝ)
            (0 : Matrix (Fin n) (Fin n) ℝ) (A + B)).PosSemidef := by
        simpa [hCongruence Y] using hTransformed_Y
      simpa using hDiagonal_psd.submatrix Sum.inl
    have hCongruence_psd : (S * (X - Y) * S).PosSemidef := by
      have hRewrite : S - S * Y * S = S * (X - Y) * S := by
        calc
          S - S * Y * S = S * X * S - S * Y * S := by rw [hS_mul_X_mul_S]
          _ = S * (X - Y) * S := by
            rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      simpa [hRewrite] using hTopLeft_psd
    have hDiff_psd : (X - Y).PosSemidef := by
      have hStarCongruence : (S * (X - Y) * star S).PosSemidef := by
        simpa [Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_eq_transpose_of_trivial, hS_symm.eq] using hCongruence_psd
      exact
        (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
          (U := S) (x := X - Y) hS_pos.isUnit).mp hStarCongruence
    have hTrace_nonneg : 0 ≤ Matrix.trace (X - Y) := Matrix.PosSemidef.trace_nonneg hDiff_psd
    simpa [Matrix.trace_sub] using hTrace_nonneg
  have hR_det_ne : R.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det R).mp hR_unit).ne_zero
  have hTransformed_difference :
      (R.transpose * Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin n) ℝ)
          (0 : Matrix (Fin n) (Fin n) ℝ) B * R -
        R.transpose * Matrix.fromBlocks X X X X * R).PosSemidef := by
    simpa [slack, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      using hTransformed_slack_X
  refine ⟨hX_symm, hSlack_X_psd, hTrace_bound, ?_⟩
  change R.det ≠ 0 ∧
      (R.transpose * Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin n) ℝ)
          (0 : Matrix (Fin n) (Fin n) ℝ) B * R -
        R.transpose * Matrix.fromBlocks X X X X * R).PosSemidef
  exact ⟨hR_det_ne, hTransformed_difference⟩

/- [BLOCK Exercise 3.13 | 12 | thm]
Let S^n be the set of n × n real symmetric matrices, S_{++}^n ⊂ S^n the set of real symmetric
positive definite matrices, and for M,N ∈ S^n, let M preceq N mean that N-M is positive
semidefinite. Let I denote the n × n identity matrix, and let tr denote the trace.
For A,B ∈ S_{++}^n, define
H(A,B)=2(A^{-1}+B^{-1})^{-1}.
Assuming that X=(A^{-1}+B^{-1})^{-1}
solves the semidefinite program
trace-maximization semidefinite program, conclude that the function
(A,B) mapsto tr((A^{-1}+B^{-1})^{-1})
on S_{++}^n × S_{++}^n is concave.
-/
theorem trace_harmonic_mean_concave
    {n : ℕ} :
    ∀ A₁ B₁ A₂ B₂ : Matrix (Fin n) (Fin n) ℝ,
      ∀ t : ℝ,
        0 ≤ t →
        t ≤ 1 →
        A₁.IsSymm →
        B₁.IsSymm →
        A₂.IsSymm →
        B₂.IsSymm →
        A₁.PosDef →
        B₁.PosDef →
        A₂.PosDef →
        B₂.PosDef →
        (Matrix.trace
            ((((t • A₁ + (1 - t) • A₂)⁻¹ + (t • B₁ + (1 - t) • B₂)⁻¹)⁻¹))) ≥
          t * Matrix.trace ((A₁⁻¹ + B₁⁻¹)⁻¹) +
            (1 - t) * Matrix.trace ((A₂⁻¹ + B₂⁻¹)⁻¹) := by
  intro A₁ B₁ A₂ B₂ t ht_nonneg ht_le_one hA₁_symm hB₁_symm hA₂_symm hB₂_symm
    hA₁_pos hB₁_pos hA₂_pos hB₂_pos
  by_cases ht_zero : t = 0
  · -- The endpoint case collapses to the second input pair by direct simplification.
    simp [ht_zero]
  · let Aₜ : Matrix (Fin n) (Fin n) ℝ := t • A₁ + (1 - t) • A₂
    let Bₜ : Matrix (Fin n) (Fin n) ℝ := t • B₁ + (1 - t) • B₂
    let X₁ : Matrix (Fin n) (Fin n) ℝ := (A₁⁻¹ + B₁⁻¹)⁻¹
    let X₂ : Matrix (Fin n) (Fin n) ℝ := (A₂⁻¹ + B₂⁻¹)⁻¹
    let Xₜ : Matrix (Fin n) (Fin n) ℝ := (Aₜ⁻¹ + Bₜ⁻¹)⁻¹
    let Y : Matrix (Fin n) (Fin n) ℝ := t • X₁ + (1 - t) • X₂
    have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (by simpa [eq_comm] using ht_zero)
    have h_one_sub_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht_le_one
    -- The mixed inputs remain symmetric because symmetry is preserved by convex combinations.
    have hAₜ_symm : Aₜ.IsSymm := by
      simpa [Aₜ] using (hA₁_symm.smul t).add (hA₂_symm.smul (1 - t))
    have hBₜ_symm : Bₜ.IsSymm := by
      simpa [Bₜ] using (hB₁_symm.smul t).add (hB₂_symm.smul (1 - t))
    -- The nonzero weight gives a genuinely positive contribution from the first endpoint.
    have hAₜ_pos : Aₜ.PosDef := by
      exact (hA₁_pos.smul ht_pos).add_posSemidef ((hA₂_pos.posSemidef).smul h_one_sub_nonneg)
    have hBₜ_pos : Bₜ.PosDef := by
      exact (hB₁_pos.smul ht_pos).add_posSemidef ((hB₂_pos.posSemidef).smul h_one_sub_nonneg)
    -- The SDP theorem provides symmetry, feasibility, and trace optimality at each endpoint.
    have hSdp₁ :=
      harmonic_mean_matrix_solves_trace_maximization_sdp
        A₁ B₁ X₁ hA₁_symm hB₁_symm hA₁_pos hB₁_pos rfl
    have hSdp₂ :=
      harmonic_mean_matrix_solves_trace_maximization_sdp
        A₂ B₂ X₂ hA₂_symm hB₂_symm hA₂_pos hB₂_pos rfl
    have hSdpₜ :=
      harmonic_mean_matrix_solves_trace_maximization_sdp
        Aₜ Bₜ Xₜ hAₜ_symm hBₜ_symm hAₜ_pos hBₜ_pos rfl
    rcases hSdp₁ with ⟨hX₁_symm, hSlack₁_psd, _, _⟩
    rcases hSdp₂ with ⟨hX₂_symm, hSlack₂_psd, _, _⟩
    rcases hSdpₜ with ⟨_, _, hTraceₜ, _⟩
    -- The convex combination of optimal endpoint solutions is still symmetric.
    have hY_symm : Y.IsSymm := by
      simpa [Y] using (hX₁_symm.smul t).add (hX₂_symm.smul (1 - t))
    -- The mixed slack is exactly the same convex combination of the endpoint slacks.
    have hSlackY_eq :
        (Matrix.fromBlocks Aₜ (0 : Matrix (Fin n) (Fin n) ℝ)
            (0 : Matrix (Fin n) (Fin n) ℝ) Bₜ -
          Matrix.fromBlocks Y Y Y Y) =
          t •
            (Matrix.fromBlocks A₁ (0 : Matrix (Fin n) (Fin n) ℝ)
                (0 : Matrix (Fin n) (Fin n) ℝ) B₁ -
              Matrix.fromBlocks X₁ X₁ X₁ X₁) +
            (1 - t) •
              (Matrix.fromBlocks A₂ (0 : Matrix (Fin n) (Fin n) ℝ)
                  (0 : Matrix (Fin n) (Fin n) ℝ) B₂ -
                Matrix.fromBlocks X₂ X₂ X₂ X₂) := by
      ext i j <;> rcases i with i | i <;> rcases j with j | j <;>
        simp [Aₜ, Bₜ, Y, sub_eq_add_neg, smul_eq_mul] <;> ring
    -- PSD is preserved under nonnegative scaling and addition, so the candidate is feasible.
    have hSlackY_psd :
        (Matrix.fromBlocks Aₜ (0 : Matrix (Fin n) (Fin n) ℝ)
            (0 : Matrix (Fin n) (Fin n) ℝ) Bₜ -
          Matrix.fromBlocks Y Y Y Y).PosSemidef := by
      rw [hSlackY_eq]
      exact (hSlack₁_psd.smul ht_nonneg).add (hSlack₂_psd.smul h_one_sub_nonneg)
    -- Testing the mixed optimizer against the feasible point `Y` gives the desired bound.
    have hTraceY :
        Matrix.trace Y = t * Matrix.trace X₁ + (1 - t) * Matrix.trace X₂ := by
      calc
        Matrix.trace Y = Matrix.trace (t • X₁ + (1 - t) • X₂) := by rfl
        _ = Matrix.trace (t • X₁) + Matrix.trace ((1 - t) • X₂) := by
          rw [Matrix.trace_add]
        _ = t * Matrix.trace X₁ + (1 - t) * Matrix.trace X₂ := by
          rw [Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    have hOptimal : Matrix.trace Y ≤ Matrix.trace Xₜ := hTraceₜ Y hY_symm hSlackY_psd
    rw [hTraceY] at hOptimal
    simpa [X₁, X₂, Xₜ] using hOptimal
end «problem-47»
