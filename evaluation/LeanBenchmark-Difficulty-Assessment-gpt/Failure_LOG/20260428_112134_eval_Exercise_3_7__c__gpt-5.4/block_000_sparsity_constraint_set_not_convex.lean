theorem sparsity_constraint_set_not_convex :
    ∃ (m : ℕ) (_ : 0 < m) (p q : Fin m → ℝ),
      (∀ j, 0 ≤ p j) ∧
      (∀ j, 0 ≤ q j) ∧
      ((univ.filter fun j => p j > 0).card ≤ m / 2) ∧
      ((univ.filter fun j => q j > 0).card ≤ m / 2) ∧
      ∃ t : ℝ,
        0 < t ∧
        t < 1 ∧
        m / 2 < (univ.filter fun j => t * p j + (1 - t) * q j > 0).card := by
  sorry
