theorem quartic_example_has_no_local_maxima
    (xStar : Fin 2 → ℝ) :
    ¬ (∃ r : ℝ, 0 < r ∧ ∀ x : Fin 2 → ℝ, ‖x - xStar‖ < r →
      2 * (x 0)^2 + (x 1)^2 - 2 * (x 0) * (x 1) + 2 * (x 0)^3 + (x 0)^4 ≤
      2 * (xStar 0)^2 + (xStar 1)^2 - 2 * (xStar 0) * (xStar 1) + 2 * (xStar 0)^3 + (xStar 0)^4) := by
  sorry
