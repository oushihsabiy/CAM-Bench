theorem KKTMatrix_inv_eq_fromBlocks
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (G : Matrix n n ℝ) (A : Matrix m n ℝ)
    [Invertible G] [Invertible (A * ⅟ G * Aᵀ)] :
    KKTMatrix G A *
        Matrix.fromBlocks
          (⅟ G - ⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ) * A * ⅟ G)
          (⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ))
          ((⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ))ᵀ)
          (-⅟ (A * ⅟ G * Aᵀ)) = 1 ∧
      Matrix.fromBlocks
          (⅟ G - ⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ) * A * ⅟ G)
          (⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ))
          ((⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ))ᵀ)
          (-⅟ (A * ⅟ G * Aᵀ)) *
        KKTMatrix G A = 1 := by
  sorry
