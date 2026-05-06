theorem min_mul_on_unit_circle :
    (∀ x1 x2 : ℝ, x1 ^ 2 + x2 ^ 2 = 1 → -((1 : ℝ) / 2) ≤ x1 * x2) ∧
      ((∀ x1 x2 : ℝ,
          x1 ^ 2 + x2 ^ 2 = 1 →
            (x1 * x2 = -((1 : ℝ) / 2) ↔
              (x1 = 1 / Real.sqrt 2 ∧ x2 = -(1 / Real.sqrt 2)) ∨
                (x1 = -(1 / Real.sqrt 2) ∧ x2 = 1 / Real.sqrt 2)))) := by
  sorry
