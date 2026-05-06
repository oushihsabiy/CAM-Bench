theorem l1NormMinimization_dual_problem
    {m n : ℕ} (P : L1NormMinimizationProblem m n) :
    {y : Fin m → ℝ | ∀ j : Fin n, |(P.A.transpose.mulVec y) j| ≤ 1} =
      {y : Fin m → ℝ |
        (∑ i, P.b i * y i) = (∑ i, P.b i * y i) ∧
        ∀ j : Fin n, |(P.A.transpose.mulVec y) j| ≤ 1} := by
  sorry
