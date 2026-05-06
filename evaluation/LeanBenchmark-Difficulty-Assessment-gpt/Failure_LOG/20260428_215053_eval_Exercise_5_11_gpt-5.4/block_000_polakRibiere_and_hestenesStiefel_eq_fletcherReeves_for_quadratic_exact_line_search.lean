theorem polakRibiere_and_hestenesStiefel_eq_fletcherReeves_for_quadratic_exact_line_search
    {n : ℕ}
    [InnerProductSpace ℝ (Fin n → ℝ)]
    (f : (Fin n → ℝ) → ℝ)
    (x p : ℕ → (Fin n → ℝ))
    (α β : ℕ → ℝ)
    (k : ℕ)
    (hquad : IsQuadraticFunction f)
    (hcg : IsNonlinearConjugateGradientIteration f x p α β)
    (hexact : IsExactLineSearch f (x k) (p k) (α k))
    (hgrad_ne : gradient f (x k) ≠ 0) :
    PolakRibiereParameter f x k = FletcherReevesParameter f x k ∧
      HestenesStiefelParameter f x p k = FletcherReevesParameter f x k := by
  sorry
