theorem trust_region_global_minimizer_exists_kkt_multiplier
    {n : ℕ} (p : QuadraticTrustRegionProblem n) (x : Fin n → ℝ)
    (h_symm : p.A.IsSymm)
    (h_min :
      x ∈ p.feasibleSet ∧
        ∀ y : Fin n → ℝ, y ∈ p.feasibleSet → p.objective x ≤ p.objective y) :
    ∃ lam : ℝ,
      x ∈ p.feasibleSet ∧
      0 ≤ lam ∧
      (p.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      ((p.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x = (fun i => -p.b i)) ∧
      lam * (1 - dotProduct x x) = 0 := by
  sorry
