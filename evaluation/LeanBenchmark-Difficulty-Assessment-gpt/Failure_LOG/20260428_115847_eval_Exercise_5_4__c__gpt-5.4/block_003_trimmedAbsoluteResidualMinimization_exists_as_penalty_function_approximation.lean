theorem trimmedAbsoluteResidualMinimization_exists_as_penalty_function_approximation
    (p : TrimmedAbsoluteResidualMinimization) (h₁ : 1 ≤ p.r) (x : Fin p.n → ℝ) :
    p.objectiveFromData x =
      sInf {v : ℝ | ∃ t : ℝ, 0 ≤ t ∧
        v = (p.r : ℝ) * t + ∑ i : Fin p.m, max (|p.residual x i| - t) 0} := by
  simpa [TrimmedAbsoluteResidualMinimization.objectiveFromData] using
    p.exists_as_penalty_function_approximation h₁ x