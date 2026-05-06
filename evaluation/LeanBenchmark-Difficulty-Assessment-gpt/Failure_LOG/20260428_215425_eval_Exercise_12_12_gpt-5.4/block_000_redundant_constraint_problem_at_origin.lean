theorem redundant_constraint_problem_at_origin :
    let p := RedundantConstraintFeasibilityProblem.default
    let xstar : Fin 2 → ℝ := fun
      | ⟨0, _⟩ => 0
      | ⟨1, _⟩ => 0
    p.isFeasible xstar ∧
      active p.g 0 xstar ∧
      active p.g 1 xstar ∧
      linearFunction (p.g 0) ∧
      linearFunction (p.g 1) ∧
      ¬ LICQ p.g xstar := by
  sorry
