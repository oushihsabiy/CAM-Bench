theorem no_step_size_satisfies_armijo_and_curvature_when_c₂_lt_c₁ :
    ∃ (f : ℝ → ℝ) (x p c₁ c₂ : ℝ),
      0 < c₂ ∧ c₂ < c₁ ∧ c₁ < 1 ∧
      x = 0 ∧ p = -1 ∧ f = (fun t => t) ∧
      ∀ α : ℝ, 0 < α →
        ¬ (ArmijoCondition f x p c₁ α ∧ CurvatureCondition f x p c₂ α) := by
  sorry
