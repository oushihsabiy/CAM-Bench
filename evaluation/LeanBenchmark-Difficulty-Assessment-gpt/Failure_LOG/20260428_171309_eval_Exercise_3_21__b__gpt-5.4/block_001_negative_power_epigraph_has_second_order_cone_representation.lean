theorem negative_power_epigraph_has_second_order_cone_representation :
    ∀ (α : ℚ),
      α < 0 →
      ∃ m : ℕ,
        ∃ n : ℕ,
          ∃ k : Fin n → ℕ,
            ∃ A : ∀ i : Fin n, (ℝ × ℝ × (Fin m → ℝ)) →ᵃ[ℝ] (Fin (k i) → ℝ),
              ∃ b : Fin n → (ℝ × ℝ × (Fin m → ℝ)) →ᵃ[ℝ] ℝ,
                ∀ x t : ℝ,
                  (0 < x ∧ x ^ (α : ℝ) ≤ t) ↔
                    ∃ y : Fin m → ℝ,
                      ∀ i : Fin n, ‖A i (x, t, y)‖ ≤ b i (x, t, y) := by
  intro α hα
  classical
  refine ⟨0, 1, (fun _ => 0), ?_, ?_, ?_⟩
  · intro i
    exact
      { toFun := fun _ => Fin.elim0
        map_add' := by
          intro a b
          funext j
          exact Fin.elim0 j
        map_smul' := by
          intro c a
          funext j
          exact Fin.elim0 j }
  · intro i
    exact
      { toFun := fun _ => 0
        map_add' := by
          intro a b
          simp
        map_smul' := by
          intro c a
          simp }
  · intro x t
    constructor
    · intro hx
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      intro i
      fin_cases i
      simp
    · intro hy
      rcases hy with ⟨y, hy⟩
      exfalso
      have h := hy ⟨0, by simp⟩
      simp at h