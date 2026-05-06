theorem lasso_coordinate_zero_of_column_norm_lt_gamma
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (γ : ℝ)
    (xStar : Fin n → ℝ)
    (hγ : 0 < γ)
    (hopt :
      ∀ x : Fin n → ℝ,
        ‖A.mulVec x - b‖ + γ * ‖x‖ ≥ ‖A.mulVec xStar - b‖ + γ * ‖xStar‖)
    (i : Fin n)
    (hi : ‖fun j : Fin m => A j i‖ < γ) :
    xStar i = 0 := by
  sorry
