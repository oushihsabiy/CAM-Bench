theorem projection_eq_along_ray_of_chebyshev
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsChebyshevSet C)
    {x₀ x : EuclideanSpace ℝ (Fin n)}
    (hx₀_not_mem : x₀ ∉ C) :
    ∀ θ : ℝ, 1 ≤ θ →
      x = θ • x₀ + (1 - θ) • Classical.choose (ExistsUnique.exists (hC x₀)) →
      Classical.choose (ExistsUnique.exists (hC x)) = Classical.choose (ExistsUnique.exists (hC x₀)) := by
  sorry
