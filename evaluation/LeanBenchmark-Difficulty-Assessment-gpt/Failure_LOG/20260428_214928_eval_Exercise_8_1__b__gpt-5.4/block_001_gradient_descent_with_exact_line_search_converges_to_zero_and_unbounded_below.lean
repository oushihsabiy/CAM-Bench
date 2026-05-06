theorem gradient_descent_with_exact_line_search_converges_to_zero_and_unbounded_below
    (A : GradientDescentWithExactLineSearch) (hγ : 1 ≤ A.γ)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2)
    (hcoords :
      ∀ k : ℕ,
        A.x k 0 = A.γ * ((A.γ - 1) / (A.γ + 1)) ^ k ∧
        A.x k 1 = (-((A.γ - 1) / (A.γ + 1))) ^ k) :
    Tendsto A.x atTop (𝓝 0) ∧
      ∀ M : ℝ, ∃ x : Fin 2 → ℝ, A.f x < M := by
  sorry
