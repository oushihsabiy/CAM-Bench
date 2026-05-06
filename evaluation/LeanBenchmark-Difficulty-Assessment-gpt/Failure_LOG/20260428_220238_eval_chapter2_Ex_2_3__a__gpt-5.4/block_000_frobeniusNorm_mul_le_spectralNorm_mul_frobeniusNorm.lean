theorem frobeniusNorm_mul_le_spectralNorm_mul_frobeniusNorm
    {𝕜 : Type*} {m : Type*} {n : Type*} {p : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n 𝕜) (B : Matrix n p 𝕜) :
    (∑ i, ∑ j, ‖(A * B) i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ‖A‖ * (∑ i, ∑ j, ‖B i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  sorry
