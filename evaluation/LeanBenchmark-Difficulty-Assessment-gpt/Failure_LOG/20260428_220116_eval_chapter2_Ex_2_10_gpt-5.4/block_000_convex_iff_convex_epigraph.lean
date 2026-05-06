theorem convex_iff_convex_epigraph {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    C.Nonempty →
    Convex ℝ C →
      (ConvexOn ℝ C f ↔
        Convex ℝ {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 ∈ C ∧ f p.1 ≤ p.2}) := by
  sorry
