theorem recursive_sequence_RQuadraticallyConvergentToZero :
    RQuadraticallyConvergentToZero
      (fun k : ℕ =>
        if Even k then
          (1 / 4 : ℝ) ^ (2 ^ k)
        else
          (1 / (k : ℝ)) * (1 / 4 : ℝ) ^ (2 ^ (k - 1))) := by
  sorry
