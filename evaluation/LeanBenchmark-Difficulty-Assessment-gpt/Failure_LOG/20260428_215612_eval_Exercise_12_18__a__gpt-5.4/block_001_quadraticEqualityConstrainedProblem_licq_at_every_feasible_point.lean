theorem quadraticEqualityConstrainedProblem_licq_at_every_feasible_point :
    let P := QuadraticEqualityConstrainedProblem.standard
    ∀ p : ℝ × ℝ, P.isFeasible p → ((2 * (p.1 - 1) : ℝ), (-5 : ℝ)) ≠ 0 := by
  sorry
