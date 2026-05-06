theorem gradient_eq_zero_of_saddle
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    {xbar : EuclideanSpace ℝ (Fin n)}
    {zbar : EuclideanSpace ℝ (Fin m)}
    (hf : Differentiable ℝ f)
    (hsaddle :
      ∀ x z,
        f (xbar, z) ≤ f (xbar, zbar) ∧
        f (xbar, zbar) ≤ f (x, zbar)) :
    fderiv ℝ f (xbar, zbar) = 0 := by
  sorry
