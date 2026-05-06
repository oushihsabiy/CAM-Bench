theorem spectralNorm_eq_topSingularValue
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    ‖A‖ = sSup {r : ℝ | ∃ x : EuclideanSpace ℝ n, ‖x‖ = 1 ∧ r = ‖(Matrix.toEuclideanLin A) x‖} := by
  sorry
