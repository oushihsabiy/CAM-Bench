theorem generalizedInequality_refl {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsProperCone K)
    (x : Fin n → ℝ) : x ≼[K] x := by
  change x - x ∈ K
  have h0 : (0 : Fin n → ℝ) ∈ K := by
    simpa using hK.1 (x := (0 : Fin n → ℝ)) (by simp) (a := (0 : ℝ)) (by linarith)
  simpa using h0

/-- The generalized inequality induced by a proper cone is transitive. -/