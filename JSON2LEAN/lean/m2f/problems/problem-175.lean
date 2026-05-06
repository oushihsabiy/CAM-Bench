import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-175»

/- [BLOCK Exercise 6.3 | 1 | thm]
Let sₖ,yₖ∈ ℝ^n, let Bₖ∈ ℝ^{n×n} be invertible, and let Hₖ=Bₖ^{-1}. Assume s_kᵀ Bₖ s_kne 0 and y_kᵀ
s_kne 0, and define ρ_k=(y_kᵀ sₖ)^{-1}. Let B_{k+1}=Bₖ-(Bₖ sₖ s_kᵀ Bₖ)/(s_kᵀ Bₖ sₖ)+(yₖ y_kᵀ)/(y_kᵀ
sₖ) and H_{k+1}=(I-ρ_k sₖ y_kᵀ)Hₖ(I-ρ_k yₖ s_kᵀ)+ρ_k sₖ s_kᵀ, where I is the n× n identity matrix.
Show that H_{k+1}=B_{k+1}^{-1}.
-/
open Matrix

theorem bfgs_inverse_update_is_inverse
    {n : Type*} [Fintype n] [DecidableEq n]
    (sk yk : n → ℝ) (Bk Hk : Matrix n n ℝ)
    (hBk_inv : IsUnit Bk.det)
    (hHk : Hk = Bk⁻¹)
    (hskBkSk : (dotProduct sk (Bk *ᵥ sk)) ≠ 0)
    (hykTsk : (dotProduct yk sk) ≠ 0) :
    let ρk : ℝ := (dotProduct yk sk)⁻¹
    let Bk1 : Matrix n n ℝ :=
      Bk
        - ((dotProduct sk (Bk *ᵥ sk))⁻¹ : ℝ) • ((Bk * Matrix.vecMulVec sk sk) * Bk)
        + ((dotProduct yk sk)⁻¹ : ℝ) • Matrix.vecMulVec yk yk
    let Hk1 : Matrix n n ℝ :=
      (((1 : Matrix n n ℝ) - ρk • Matrix.vecMulVec sk yk) * Hk *
        ((1 : Matrix n n ℝ) - ρk • Matrix.vecMulVec yk sk))
        + ρk • Matrix.vecMulVec sk sk
    Hk1 = Bk1⁻¹ := by
  dsimp
  subst Hk
  set ρ : ℝ := (dotProduct yk sk)⁻¹
  set β : ℝ := dotProduct sk (Bk *ᵥ sk)
  set δ : ℝ := dotProduct yk (Bk⁻¹ *ᵥ yk)
  set p : n → ℝ := Bk *ᵥ sk
  set r : n → ℝ := yk ᵥ* Bk⁻¹
  set t : n → ℝ := sk ᵥ* Bk
  set Bk1 : Matrix n n ℝ :=
    Bk - β⁻¹ • ((Bk * Matrix.vecMulVec sk sk) * Bk) + ρ • Matrix.vecMulVec yk yk
    with hBk1
  set Hk1 : Matrix n n ℝ :=
    (((1 : Matrix n n ℝ) - ρ • Matrix.vecMulVec sk yk) * Bk⁻¹ *
      ((1 : Matrix n n ℝ) - ρ • Matrix.vecMulVec yk sk))
      + ρ • Matrix.vecMulVec sk sk
    with hHk1
  change Hk1 = Bk1⁻¹
  -- The inverse formula is proved by checking that the direct BFGS update has `Hk1` as a right inverse.
  refine (Matrix.inv_eq_right_inv ?_).symm
  change Bk1 * Hk1 = 1
  have hρ_mul : ρ * dotProduct yk sk = 1 := by
    -- This is the normalization coming from `ρ = (y_kᵀ s_k)⁻¹`.
    simpa [ρ] using inv_mul_cancel₀ hykTsk
  have hρ_mul' : dotProduct yk sk * ρ = 1 := by
    simpa [mul_comm] using hρ_mul
  have hβ_row : dotProduct t sk = β := by
    -- This identifies the scalar in the rank-one `Bk` correction with the corresponding row-vector pairing.
    simpa [β, t] using (Matrix.dotProduct_mulVec sk Bk sk).symm
  have hδ_row : dotProduct r yk = δ := by
    -- This is the only scalar involving the inverse matrix that survives the expansion.
    simpa [δ, r] using (Matrix.dotProduct_mulVec yk Bk⁻¹ yk).symm
  have ht_mul_inv : t ᵥ* Bk⁻¹ = sk := by
    -- The `skᵀ Bk` row cancels against `Bk⁻¹`.
    simpa [t] using congrArg (fun M : Matrix n n ℝ => sk ᵥ* M) (Matrix.mul_nonsing_inv Bk hBk_inv)
  have hyk_left : yk ᵥ* ((1 : Matrix n n ℝ) - ρ • Matrix.vecMulVec sk yk) = 0 := by
    -- The left BFGS correction annihilates `yk` because `ρ * (y_kᵀ s_k) = 1`.
    ext i
    calc
      (yk ᵥ* ((1 : Matrix n n ℝ) - ρ • Matrix.vecMulVec sk yk)) i
          = yk i - ρ * (dotProduct yk sk * yk i) := by
              simp [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_smul,
                Matrix.vecMul_vecMulVec]
      _ = yk i - (ρ * dotProduct yk sk) * yk i := by ring
      _ = 0 := by rw [hρ_mul]; ring
  have hyk_mul_Hk1 : yk ᵥ* Hk1 = sk := by
    -- After the annihilation above, only the explicit `ρ • s_k s_kᵀ` correction remains.
    rw [hHk1, Matrix.vecMul_add]
    rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hyk_left]
    simp
    ext i
    calc
      (yk ᵥ* (ρ • Matrix.vecMulVec sk sk)) i = ρ * (dotProduct yk sk * sk i) := by
        simp [Matrix.vecMul_smul, Matrix.vecMul_vecMulVec]
      _ = (ρ * dotProduct yk sk) * sk i := by ring
      _ = sk i := by rw [hρ_mul, one_mul]
  have ht_left :
      t ᵥ* ((1 : Matrix n n ℝ) - ρ • Matrix.vecMulVec sk yk) = t - (ρ * β) • yk := by
    -- Pushing the `skᵀ Bk` row through the first correction produces the expected rank-one term.
    ext i
    simp [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_smul, Matrix.vecMul_vecMulVec,
      hβ_row, mul_assoc]
  have ht_mid :
      t ᵥ* (((1 : Matrix n n ℝ) - ρ • Matrix.vecMulVec sk yk) * Bk⁻¹) =
        sk - (ρ * β) • r := by
    -- Cancelling `Bk` against `Bk⁻¹` leaves the inverse row `r = y_kᵀ Bk⁻¹`.
    rw [← Matrix.vecMul_vecMul, ht_left, Matrix.sub_vecMul, Matrix.smul_vecMul]
    simp [r, ht_mul_inv]
  have ht_mul_Hk1 :
      t ᵥ* Hk1 = -(ρ * β) • r + (β * (ρ ^ 2 * δ + ρ)) • sk := by
    -- Expanding the second correction isolates the only remaining inverse scalar `δ`.
    rw [hHk1, Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ht_mid]
    ext i
    have hdot :
        dotProduct (sk - (ρ * β) • r) yk = dotProduct yk sk - (ρ * β) * δ := by
      rw [sub_dotProduct, smul_dotProduct, hδ_row]
      simp [dotProduct_comm, mul_assoc]
    simp [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_smul, Matrix.vecMul_vecMulVec,
      hdot, hβ_row]
    have hρi : sk i * ρ * dotProduct yk sk = sk i := by
      calc
        sk i * ρ * dotProduct yk sk = sk i * (ρ * dotProduct yk sk) := by ring
        _ = sk i := by rw [hρ_mul, mul_one]
    linarith
  have hBk_left :
      Bk * ((1 : Matrix n n ℝ) - ρ • Matrix.vecMulVec sk yk) =
        Bk - ρ • Matrix.vecMulVec p yk := by
    -- Multiplying `Bk` through the first rank-one factor turns `s_k` into `p = Bk s_k`.
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec]
  have hBk_mid :
      Bk * (((1 : Matrix n n ℝ) - ρ • Matrix.vecMulVec sk yk) * Bk⁻¹) =
        1 - ρ • Matrix.vecMulVec p r := by
    -- The middle factor is the same cancellation pattern, now at the matrix level.
    rw [← Matrix.mul_assoc, hBk_left, Matrix.sub_mul, Matrix.mul_nonsing_inv Bk hBk_inv,
      smul_mul_assoc, Matrix.vecMulVec_mul]
  have hBk_mul_Hk1 :
      Bk * Hk1 =
        1 - ρ • Matrix.vecMulVec p r - ρ • Matrix.vecMulVec yk sk
          + (ρ ^ 2 * δ + ρ) • Matrix.vecMulVec p sk := by
    -- Expanding the right factor produces the standard BFGS cancellation pattern.
    rw [hHk1, Matrix.mul_add, ← Matrix.mul_assoc, hBk_mid, Matrix.mul_smul, Matrix.mul_vecMulVec]
    have hcross :
        (1 - ρ • Matrix.vecMulVec p r) *
            ((1 : Matrix n n ℝ) - ρ • Matrix.vecMulVec yk sk) =
          1 - ρ • Matrix.vecMulVec yk sk - ρ • Matrix.vecMulVec p r
            + (ρ ^ 2 * δ) • Matrix.vecMulVec p sk := by
      rw [sub_mul, one_mul, mul_sub, Matrix.mul_one, smul_mul_assoc, Matrix.mul_smul,
        Matrix.vecMulVec_mul_vecMulVec]
      ext i j
      simp [Matrix.vecMulVec_apply, hδ_row, mul_assoc]
      ring
    rw [hcross]
    ext i j
    simp [p, Matrix.vecMulVec_apply]
    ring
  have hBk1_rank_one :
      Bk1 = Bk - β⁻¹ • Matrix.vecMulVec p t + ρ • Matrix.vecMulVec yk yk := by
    -- The direct BFGS update is exactly the usual `p tᵀ` rank-one correction.
    rw [hBk1]
    simp [p, t, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  rw [hBk1_rank_one, add_mul, sub_mul, hBk_mul_Hk1, smul_mul_assoc, Matrix.vecMulVec_mul,
    smul_mul_assoc, Matrix.vecMulVec_mul, hyk_mul_Hk1, ht_mul_Hk1]
  -- The three expanded pieces cancel coefficient-by-coefficient after the row identities above.
  ext i j
  simp [Matrix.vecMulVec_apply]
  field_simp [β, ρ, hskBkSk, hykTsk]
  ring

end «problem-175»
