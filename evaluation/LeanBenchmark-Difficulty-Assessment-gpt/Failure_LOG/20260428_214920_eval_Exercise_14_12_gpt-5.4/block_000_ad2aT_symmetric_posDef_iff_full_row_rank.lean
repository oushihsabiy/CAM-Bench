theorem ad2aT_symmetric_posDef_iff_full_row_rank
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (X S : Matrix n n ℝ)
    (hXdiag : ∀ i j, i ≠ j → X i j = 0) (hSdiag : ∀ i j, i ≠ j → S i j = 0)
    (hXpos : ∀ i, 0 < X i i) (hSpos : ∀ i, 0 < S i i) :
    ((A * (X * S⁻¹) * Aᵀ).IsSymm ∧
      ∀ v : m → ℝ, v ≠ 0 → 0 < dotProduct v ((A * (X * S⁻¹) * Aᵀ).mulVec v)) ↔
      Module.finrank ℝ (LinearMap.range Aᵀ.toLin') = Fintype.card m := by
  classical
  constructor
  · intro h
    sorry
  · intro h
    sorry

/-
Exercise 14.12 | 55 | thm

Let A ∈ ℝ^{m×n}, and let D ∈ ℝ^{n×n} be any diagonal matrix with exactly m positive diagonal entries
and all remaining diagonal entries equal to 0. Determine whether the conclusion that AD²Aᵀ ∈ ℝ^{m×m}
is symmetric and positive definite if and only if rank(A) = m remains valid.
-/