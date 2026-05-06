theorem quadratic_coefficients_of_interpolation_data
    {f g₁ g₂ G11sq G12 G22sq : ℝ}
    (hm1 : f = 1)
    (hm2 : f + g₁ + (1 / 2 : ℝ) * G11sq = 2.0084)
    (hm3 : f + 2 * g₁ + (1 / 2 : ℝ) * G11sq * 4 = 7.0091)
    (hm4 : f + g₁ + g₂ + (1 / 2 : ℝ) * G11sq + G12 + (1 / 2 : ℝ) * G22sq = 1.0168)
    (hm5 : f + 2 * g₂ + (1 / 2 : ℝ) * G22sq * 4 = -0.9909)
    (hm6 : f + g₂ + (1 / 2 : ℝ) * G22sq = -0.9916) :
    f = 1 ∧
    g₁ = -0.48795 ∧
    g₂ = -2.4954 ∧
    G11sq = 2.9927 ∧
    G12 = 0.00745 ∧
    G22sq = 1.9991 := by
  sorry
