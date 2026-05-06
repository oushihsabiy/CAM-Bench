theorem abs_matrix_inner_le_spectral_mul_nuclear
    {K : Type*} {m : Type*} {n : Type*} [RCLike K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n K) :
    let spectralNorm : Matrix m n K → ℝ := fun M => sSup {r : ℝ | r = ‖M‖}
    let nuclearNorm : Matrix m n K → ℝ := fun M => sInf {r : ℝ | r = ‖M‖}
    ‖Matrix.trace (A.conjTranspose * B)‖ ≤ spectralNorm A * nuclearNorm B := by
  sorry
