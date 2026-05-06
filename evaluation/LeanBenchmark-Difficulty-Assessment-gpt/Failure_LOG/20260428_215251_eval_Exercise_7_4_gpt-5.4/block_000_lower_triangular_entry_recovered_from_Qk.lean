theorem lower_triangular_entry_recovered_from_Qk
    (m k p n : ℕ)
    (hp : p = min k m)
    (B0 : Matrix (Fin n) (Fin n) ℝ)
    (pairs : ℕ → QuasiNewtonPair)
    (S Y Q : Matrix (Fin n) (Fin p) ℝ)
    (Lk : Matrix (Fin p) (Fin p) ℝ)
    (hS : ∀ i j, S i j = (pairs (k - p + j.1)).s i.1)
    (hY : ∀ i j, Y i j = (pairs (k - p + j.1)).y i.1)
    (hQ : Q = Y - B0 * S)
    (hL : ∀ i j, Lk i j = if i > j then ∑ t : Fin n, S t i * Y t j else 0)
    (htri : IsStrictlyLowerTriangular Lk) :
    ∀ i j, i > j →
      Lk i j =
        (∑ t : Fin n, S t i * Q t j) + (∑ a : Fin n, ∑ b : Fin n, S a i * B0 a b * S b j) := by
  sorry
