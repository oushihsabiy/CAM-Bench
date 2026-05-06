theorem ad2aT_with_semidefinite_diagonal_counterexample :
    ¬ ∀ (m n : Type*) (_ : Fintype m) (_ : Fintype n) (_ : DecidableEq m) (_ : DecidableEq n)
      (A : Matrix m n ℝ) (D : Matrix n n ℝ),
      (∀ i j, i ≠ j → D i j = 0) →
      (∃ s : Finset n,
        s.card = Fintype.card m ∧
        (∀ i, i ∈ s → 0 < D i i) ∧
        (∀ i, i ∉ s → D i i = 0)) →
      (((A * (D * D) * Aᵀ).IsSymm ∧
          ∀ v : m → ℝ, v ≠ 0 → 0 < dotProduct v ((A * (D * D) * Aᵀ).mulVec v)) ↔
        Module.finrank ℝ (LinearMap.range Aᵀ.toLin') = Fintype.card m) := by
  sorry
