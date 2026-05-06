theorem unitCircleProblem_hasLocalSolution_and_penaltyUnboundedBelow :
    IsLocalSolution
      (UnitCircleEqualityConstrainedProblem.feasibleSet {})
      (UnitCircleEqualityConstrainedProblem.objective {})
      (fun i => if i = 0 then -1 else 0) ∧
      ∀ μ : ℝ, 0 < μ →
        IsUnboundedBelowOn
          (UnitCircleEqualityConstrainedProblem.penaltyFunction {} μ)
          Set.univ := by
  sorry
