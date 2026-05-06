theorem gaussNewton_minimumL2NormSolution_of_fullRowRank
    (p : DifferentiableNonlinearLeastSquaresProblem) (x : EuclideanSpace ℝ (Fin p.n))
    (hmn : p.m ≤ p.n)
    (hInvertible : Invertible (p.jacobian x * (p.jacobian x)ᵀ)) :
    IsMinimumL2NormSolution
      {d : EuclideanSpace ℝ (Fin p.n) | p.gaussNewtonSystem x d}
      ((EuclideanSpace.equiv (Fin p.n) ℝ).symm
        (-((p.jacobian x)ᵀ).mulVec
          (((⅟ (p.jacobian x * (p.jacobian x)ᵀ)).mulVec (p.residual x))))) := by
  sorry
