theorem not_extremePoint_of_rank_condition
    {n m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (Xhat : Matrix (Fin n) (Fin n) ℝ)
    (hA_symm : ∀ i : Fin m, (A i).IsSymm)
    (hXhat_symm : Xhat.IsSymm)
    (hXhat_psd : Xhat.PosSemidef)
    (hfeas : ∀ i : Fin m, Matrix.trace (A i * Xhat) = b i)
    (hineq : Matrix.rank Xhat * (Matrix.rank Xhat + 1) / 2 > m) :
    ¬ ∀ V : Matrix (Fin n) (Fin n) ℝ,
      V.IsSymm →
      (∀ i : Fin m, Matrix.trace (A i * V) = 0) →
      (Xhat + V).PosSemidef →
      (Xhat - V).PosSemidef →
      V = 0 := by
  sorry
