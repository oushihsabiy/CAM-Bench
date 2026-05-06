theorem argminSet_convex
    {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hD : Convex ℝ D)
    (hf : ConvexOn ℝ D f) :
    Convex ℝ {x | x ∈ D ∧ ∀ y ∈ D, f x ≤ f y} := by
  sorry
