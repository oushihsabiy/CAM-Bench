theorem exists_common_cost_vector_iff_exists_dual_certificates
    {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin r → Fin m → ℝ) (x : Fin r → Fin n → ℝ) :
    (∃ c : Fin n → ℝ,
      ∀ j : Fin r,
        PrimalFeasible A (b j) (x j) ∧
        ∀ z : Fin n → ℝ, PrimalFeasible A (b j) z → dotProduct c (x j) ≤ dotProduct c z) ↔
    ∃ y : Fin r → Fin m → ℝ,
      (∀ j : Fin r, PrimalFeasible A (b j) (x j)) ∧
      (∀ j : Fin r, ComponentwiseGE (y j) 0) ∧
      (∀ j1 j2 : Fin r, A.transpose.mulVec (y j1) = A.transpose.mulVec (y j2)) ∧
      (∀ j : Fin r, ComplementarySlackness A (x j) (b j) (y j)) := by
  sorry
