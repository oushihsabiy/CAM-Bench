theorem chebyshev_set_convex_of_projection_ray_fixed {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsChebyshevSet C)
    (hproj :
      ∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
        0 ≤ t →
          let p := Classical.choose (hC x)
          Classical.choose (hC (p + t • (x - p))) = p) :
    Convex ℝ C := by
  sorry
