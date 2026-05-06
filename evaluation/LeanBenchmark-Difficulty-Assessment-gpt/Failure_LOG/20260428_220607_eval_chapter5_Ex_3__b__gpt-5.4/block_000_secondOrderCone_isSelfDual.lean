theorem secondOrderCone_isSelfDual (n : ℕ) :
    {q : EuclideanSpace ℝ (Fin n) × ℝ |
      ∀ p ∈ secondOrderCone n, 0 ≤ ⟪p.1, q.1⟫ + p.2 * q.2} = secondOrderCone n := by
  sorry
