theorem depth_concave_on_convex_set
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC_nonempty : C.Nonempty)
    (hC_convex : Convex ℝ C) :
    ∀ x y : EuclideanSpace ℝ (Fin n), x ∈ C → y ∈ C →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        Metric.infDist (θ • x + (1 - θ) • y) (Cᶜ) ≥
          θ * Metric.infDist x (Cᶜ) + (1 - θ) * Metric.infDist y (Cᶜ) := by
  sorry
