theorem sgd_stochastic_gradient_norm_sq_le_lipschitz_dist_sq_plus_variance
    {d : Type*} [NormedAddCommGroup d] [InnerProductSpace ℝ d] [CompleteSpace d]
    {N : ℕ} (f : d → ℝ) (fi : Fin N → d → ℝ) (L : ℝ) (xk xstar : d)
    (havg : ∀ x, f x = (1 / (N : ℝ)) * ∑ i : Fin N, fi i x)
    (hL : HasLLipschitzGradient f L)
    (hmin : IsLocalMin f xstar) :
    (∑ i : Fin N, ‖FiniteSumStochasticGradient fi i xk‖ ^ 2) / N
      ≤ L ^ 2 * ‖xk - xstar‖ ^ 2
        + (∑ i : Fin N, ‖FiniteSumStochasticGradient fi i xk - ∇ f xk‖ ^ 2) / N := by
  sorry
