theorem sup_mul_on_closed_unit_disk_eq_one_half :
    sSup {r : ℝ | ∃ x1 x2 : ℝ, 1 - x1 ^ 2 - x2 ^ 2 ≥ 0 ∧ r = x1 * x2} = (1 : ℝ) / 2 ∧
      (∀ x1 x2 : ℝ, 1 - x1 ^ 2 - x2 ^ 2 ≥ 0 → x1 * x2 ≤ (1 : ℝ) / 2) ∧
      (1 - (1 / Real.sqrt 2) ^ 2 - (1 / Real.sqrt 2) ^ 2 ≥ 0 ∧
        (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 : ℝ) / 2) ∧
      (1 - (-(1 / Real.sqrt 2)) ^ 2 - (-(1 / Real.sqrt 2)) ^ 2 ≥ 0 ∧
        (-(1 / Real.sqrt 2)) * (-(1 / Real.sqrt 2)) = (1 : ℝ) / 2) ∧
      (∀ x1 x2 : ℝ,
        1 - x1 ^ 2 - x2 ^ 2 ≥ 0 →
        x1 * x2 = (1 : ℝ) / 2 →
        (x1 = 1 / Real.sqrt 2 ∧ x2 = 1 / Real.sqrt 2) ∨
          (x1 = -(1 / Real.sqrt 2) ∧ x2 = -(1 / Real.sqrt 2))) := by
  sorry
