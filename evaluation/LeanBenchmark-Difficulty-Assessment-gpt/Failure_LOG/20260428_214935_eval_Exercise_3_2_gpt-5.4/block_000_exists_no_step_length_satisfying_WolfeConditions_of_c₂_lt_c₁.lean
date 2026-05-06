theorem exists_no_step_length_satisfying_WolfeConditions_of_c₂_lt_c₁
    {n : ℕ} (hn : 0 < n) (hpos : 0 < c₂) (hc : c₂ < c₁) (hc₁ : c₁ < 1) :
    ∃ (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (xk pk : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ 1 f ∧
      (fderiv ℝ f xk) pk < 0 ∧
      ¬ ∃ α : ℝ,
        WolfeConditions f (fun x => gradient f x) xk pk c₂ c₁ α := by
  sorry
