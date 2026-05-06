theorem power_epigraph_has_second_order_cone_representation :
    ∀ (α : ℚ),
      1 ≤ α →
      ∃ m : ℕ,
        ∃ n : ℕ,
          ∃ k : Fin n → ℕ,
            ∃ A : ∀ i : Fin n, (ℝ × ℝ × (Fin m → ℝ)) →ᵃ[ℝ] (Fin (k i) → ℝ),
              ∃ b : Fin n → (ℝ × ℝ × (Fin m → ℝ)) →ᵃ[ℝ] ℝ,
                ∀ x t : ℝ,
                  ((if 0 ≤ x then x ^ (α : ℝ) else 0) ≤ t) ↔
                    ∃ y : Fin m → ℝ,
                      ∀ i : Fin n, ‖A i (x, t, y)‖ ≤ b i (x, t, y) := by
  intro α hα
  refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro x t
    constructor
    · intro hx
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      intro i
      exact Fin.elim0 i
    · intro h
      by_cases hxt : ((if 0 ≤ x then x ^ (α : ℝ) else 0) ≤ t)
      · exact hxt
      · exfalso
        exact hxt (by
          have hy : ∀ i : Fin 0, ‖(by exact Fin.elim0 i) (x, t, h.choose)‖ ≤ (by exact Fin.elim0 i) (x, t, h.choose) := h.choose_spec
          exact le_rfl)