theorem strictGeneralizedInequality_irrefl {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsProperCone K)
    (x : Fin n → ℝ) : ¬StrictGeneralizedInequality K x x := by
  rw [StrictGeneralizedInequality]
  simpa using hK.2.2.2.2.2

/-- The strict generalized inequality induced by a proper cone is transitive. -/