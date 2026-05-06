theorem every_feasible_point_is_optimal_of_no_negative_null_direction
    (p : LinearEqualityConstrainedProgram)
    (hx : ∃ x : Fin p.n → ℝ, p.is_feasible x)
    (hdir : ¬ ∃ d : Fin p.n → ℝ, p.A *ᵥ d = 0 ∧ dotProduct p.c d < 0) :
    ∀ x : Fin p.n → ℝ, p.is_feasible x →
      ∀ y : Fin p.n → ℝ, p.is_feasible y → p.objective x = p.objective y := by
  sorry
