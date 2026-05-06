theorem quadratic_model_global_minimizer_of_psd_and_eq_neg
    {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ) (g d : n → ℝ)
    (hsymm : B.IsSymm)
    (hpsd : ∀ x : n → ℝ, 0 ≤ dotProduct x (fun i => ∑ j, B i j * x j))
    (hBd : B.mulVec d = -g) :
    IsMinOn
      (fun d' : n → ℝ =>
        dotProduct g d' + (1 / 2 : ℝ) * dotProduct d' (fun i => ∑ j, B i j * d' j))
      Set.univ d := by
  sorry
