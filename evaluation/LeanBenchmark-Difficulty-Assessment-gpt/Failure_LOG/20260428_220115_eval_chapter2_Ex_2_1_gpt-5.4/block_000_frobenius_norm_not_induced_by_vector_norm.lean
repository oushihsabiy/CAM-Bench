theorem frobenius_norm_not_induced_by_vector_norm :
    ∀ n : ℕ, 2 ≤ n →
    ¬ ∃ (_inst : Norm (Fin n → ℝ)),
      ∀ A : Matrix (Fin n) (Fin n) ℝ,
        sSup {r : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ r = ‖A.mulVec x‖ / ‖x‖} =
          Real.sqrt (∑ i : Fin n, ∑ j : Fin n, (A i j) ^ 2) := by
  sorry
