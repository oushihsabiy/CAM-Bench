theorem max_function_minimization_problem_reformulation
    (P : MaxFunctionMinimizationProblem) :
    {r : ℝ | ∃ x : Fin P.n → ℝ, MaxFunctionMinimizationProblem.objective P x = r} =
    {r : ℝ | ∃ xt : (Fin P.n → ℝ) × ℝ,
      MaxFunctionMinimizationProblemReformulation.isFeasible
        (P.toReformulation) xt ∧
      MaxFunctionMinimizationProblemReformulation.objective
        (P.toReformulation) xt = r} := by
  sorry
