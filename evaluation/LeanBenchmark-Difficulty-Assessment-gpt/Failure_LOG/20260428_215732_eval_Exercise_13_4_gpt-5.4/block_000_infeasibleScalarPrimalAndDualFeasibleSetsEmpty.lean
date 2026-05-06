theorem infeasibleScalarPrimalAndDualFeasibleSetsEmpty :
    StandardFormLinearProgram.feasibleSet InfeasibleScalarPrimalLinearProgram.example.primal = (∅ : Set (Unit → ℝ)) ∧
    {lam : Unit → ℝ | InfeasibleScalarDualLinearProgram.isFeasible InfeasibleScalarDualLinearProgram.example lam} =
      (∅ : Set (Unit → ℝ)) := by
  sorry
