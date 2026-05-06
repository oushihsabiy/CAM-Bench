theorem nuclearNormProximalProblem_has_soft_thresholding_solution
    {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq m] [DecidableEq n] [DecidableEq r]
    (P : NuclearNormProximalProblem m n)
    (U : Matrix m r ℝ) (Sigma : Matrix r r ℝ) (V : Matrix n r ℝ)
    (hsvd : IsSingularValueDecomposition P.Y U Sigma V) :
    P.isMinimizer
      (U *
        (Matrix.diagonal fun i => NuclearNormProximalProblem.positivePart (Sigma i i - 1)) *
        Vᵀ) := by
  sorry
