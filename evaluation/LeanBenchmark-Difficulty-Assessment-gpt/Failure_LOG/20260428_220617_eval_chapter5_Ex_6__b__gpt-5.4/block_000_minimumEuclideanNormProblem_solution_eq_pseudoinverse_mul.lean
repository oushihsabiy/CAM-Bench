theorem minimumEuclideanNormProblem_solution_eq_pseudoinverse_mul
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (b : m → ℝ) (X : Matrix n m ℝ)
    (hMP : X = moorePenrosePseudoinverse A)
    (hfeas : ∃ x : n → ℝ, A.mulVec x = b) :
    X.mulVec b ∈ (MinimumEuclideanNormProblem.solutionSet
      { A := A, b := b } : Set (n → ℝ)) := by
  sorry
