theorem positiveSemidefinite_iff_quadraticForm_nonneg
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    A.PosSemidef ↔ ∀ x : n → ℝ, 0 ≤ dotProduct x (A.mulVec x) := by
  sorry
