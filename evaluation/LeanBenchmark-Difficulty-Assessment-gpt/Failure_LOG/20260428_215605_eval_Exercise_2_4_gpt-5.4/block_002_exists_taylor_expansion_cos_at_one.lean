theorem exists_taylor_expansion_cos_at_one
    (p : ℝ) :
    ∃ t : ℝ,
      t ∈ Set.Ioo (0 : ℝ) 1 ∧
        Real.cos (1 + p) =
          Real.cos 1 - Real.sin 1 * p - (1 / 2 : ℝ) * Real.cos 1 * p ^ 2 +
            (1 / 6 : ℝ) * Real.sin (1 + t * p) * p ^ 3 := by
  sorry
