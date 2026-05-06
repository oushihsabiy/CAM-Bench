theorem mixedPenalty_log_barrier_scaled_tendsto_zero
    {n : ℕ}
    (baseProblem : ConstrainedOptimizationProblem n)
    (sigma : ℕ → ℝ)
    (sigma_pos : ∀ k, 0 < sigma k)
    (hsigma_tendsto_atTop : Tendsto sigma atTop atTop)
    (x : ℕ → (Fin n → ℝ))
    (hΩ_nonempty : Set.Nonempty baseProblem.feasibleSet)
    (hΩ_bounded : Bornology.IsBounded (baseProblem.feasibleSet))
    (hΩ_closed : IsClosed (baseProblem.feasibleSet))
    (xStar : Fin n → ℝ)
    (hxStar_feasible : baseProblem.isFeasible xStar)
    (hxStar_opt : IsMinOn baseProblem.objective (baseProblem.feasibleSet) xStar)
    (hopt_strict : ∀ k, IsMinOn
      (fun y => mixedPenaltyFunction
        baseProblem.f
        baseProblem.E
        baseProblem.I
        baseProblem.c
        y
        (sigma k)
        (sigma_pos k))
      {y | ∀ i ∈ baseProblem.I, baseProblem.c i y < 0}
      (x (k + 1))) :
    Tendsto
      (fun k => (1 / sigma k) * ∑ i ∈ baseProblem.I, Real.log (-baseProblem.c i (x (k + 1))))
      atTop
      (𝓝 0) := by
  sorry
