theorem exponentialConstrainedOptimizationProblem_optimal_solution_satisfies_kkt :
    let f : EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun x => Real.exp (x 0) + Real.exp (x 1)
    let g : Fin 1 → EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun _ x => (x 0) ^ 2 / x 1
    ∃ xStar : EuclideanSpace ℝ (Fin 2),
      xStar 1 ≠ 0 ∧
      g 0 xStar ≤ 0 ∧
      (∀ x : EuclideanSpace ℝ (Fin 2), x 1 ≠ 0 → g 0 x ≤ 0 → f xStar ≤ f x) ∧
      KarushKuhnTuckerConditions f g xStar := by
  sorry
