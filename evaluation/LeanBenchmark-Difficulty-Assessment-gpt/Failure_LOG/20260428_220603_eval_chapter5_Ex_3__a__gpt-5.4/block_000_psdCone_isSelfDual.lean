theorem psdCone_isSelfDual {n : ℕ} :
    IsSelfDualCone
      {X : Matrix (Fin n) (Fin n) ℝ |
        X.IsSymm ∧ ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (X.mulVec v)} := by
  sorry
