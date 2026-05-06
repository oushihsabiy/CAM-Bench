theorem unit_norm_sq_points_are_limit_points_of_xSeq
    (x : Fin 2 → ℝ)
    (hx : ‖x‖ ^ 2 = 1) :
    IsLimitPointOfSequence x
      (fun k i =>
        (1 + (1 : ℝ) / (2 : ℝ) ^ k) *
          if i = 0 then Real.cos k else Real.sin k) := by
  sorry
