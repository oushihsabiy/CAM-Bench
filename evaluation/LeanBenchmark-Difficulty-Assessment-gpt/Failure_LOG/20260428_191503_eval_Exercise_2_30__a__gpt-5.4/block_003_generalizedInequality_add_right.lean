theorem generalizedInequality_add_right {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsProperCone K)
    {x y : Fin n → ℝ} (hxy : x ≼[K] y) (z : Fin n → ℝ) : x + z ≼[K] y + z := by
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxy

/-- Generalized inequality is preserved under nonnegative scalar multiplication. -/