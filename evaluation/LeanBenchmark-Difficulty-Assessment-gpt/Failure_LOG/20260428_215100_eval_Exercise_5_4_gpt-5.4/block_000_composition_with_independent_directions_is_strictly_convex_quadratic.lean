theorem composition_with_independent_directions_is_strictly_convex_quadratic
    {n k : ℕ} (hk : 1 ≤ k)
    (x₀ c : Fin n → ℝ) (r : ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin k → (Fin n → ℝ))
    (hp_lin : LinearIndependent ℝ p)
    (hQsymm : Qᵀ = Q)
    (hQpos : ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < dotProduct x (fun i => ∑ j : Fin n, Q i j * x j)) :
    let h : (Fin k → ℝ) → ℝ :=
      fun σ =>
        let x : Fin n → ℝ := fun i => x₀ i + ∑ j : Fin k, σ j * p j i
        (1 / 2 : ℝ) * dotProduct x (fun i => ∑ j : Fin n, Q i j * x j) + dotProduct c x + r
    IsQuadraticFunction h ∧ StrictConvexOn ℝ Set.univ h := by
  sorry
