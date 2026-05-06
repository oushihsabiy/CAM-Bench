theorem cos_theta_ge_one_div_M_of_norm_mul_inv_le
    {ι n : Type*} [Preorder ι] [Fintype n] [DecidableEq n]
    (B : ι → Matrix n n ℝ)
    (hB : ∀ k, Invertible (B k))
    (M : ℝ)
    (hM : 0 < M)
    (hbound : ∀ k, ‖B k‖ * ‖⅟ (B k)‖ ≤ M)
    (θ : ι → ℝ)
    (hθ : ∀ k, Real.cos (θ k) = 1 / (‖B k‖ * ‖⅟ (B k)‖)) :
    ∀ k, Real.cos (θ k) ≥ 1 / M := by
  intro k
  rw [hθ k]
  have hnonneg : 0 ≤ ‖B k‖ * ‖⅟ (B k)‖ := by
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  by_cases hzero : ‖B k‖ * ‖⅟ (B k)‖ = 0
  · have hMzero : M = 0 := le_antisymm (le_of_lt hM) (by simpa [hzero] using hbound k)
    exfalso
    exact ne_of_gt hM hMzero
  · have hpos : 0 < ‖B k‖ * ‖⅟ (B k)‖ := lt_of_le_of_ne hnonneg hzero
    exact one_div_le_one_div_of_le hpos (hbound k)