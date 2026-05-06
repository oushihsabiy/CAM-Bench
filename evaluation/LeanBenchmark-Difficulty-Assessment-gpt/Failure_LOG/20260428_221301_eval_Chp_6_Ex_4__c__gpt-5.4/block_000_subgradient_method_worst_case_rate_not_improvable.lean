theorem subgradient_method_worst_case_rate_not_improvable
    (Problem : Type)
    (ProbSet : Set Problem)
    (e : ℕ → Problem → ℝ)
    (G R : ℝ)
    (hG : 0 < G)
    (hR : 0 < R)
    (hLower :
      ∀ K : ℕ, ∃ P ∈ ProbSet, e K P ≥ (G * R) / (1 + Real.sqrt K))
    : ∀ h : ℕ → ℝ, HasConvergenceRateOrder (worstCaseBound Problem ProbSet e) h →
        ∃ c > 0, ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → c * ((G * R) / (1 + Real.sqrt K)) ≤ h K := by
  sorry
