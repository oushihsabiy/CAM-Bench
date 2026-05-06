theorem classicalNewtonMethod_diverges :
    ¬ ∃ (n : ℕ) (M : ClassicalNewtonMethod (n := n)),
      ∃ l : EuclideanSpace ℝ (Fin n), Tendsto M.x atTop (𝓝 l) := by
  sorry
