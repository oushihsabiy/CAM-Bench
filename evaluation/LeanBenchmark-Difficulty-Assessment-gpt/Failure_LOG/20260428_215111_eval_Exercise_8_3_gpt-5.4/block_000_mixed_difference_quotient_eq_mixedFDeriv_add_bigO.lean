theorem mixed_difference_quotient_eq_mixedFDeriv_add_bigO
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i j : Fin n)
    (hC3 : ContDiff ℝ 3 f) :
    Asymptotics.IsBigO (𝓝 (0 : ℝ))
      (fun ε : ℝ =>
        (f (x + fun k => (if k = i then ε else 0) + (if k = j then ε else 0))
          - f (x + fun k => if k = i then ε else 0)
          - f (x + fun k => if k = j then ε else 0)
          + f x) / ε ^ 2
            - fderiv ℝ
                (fun y : Fin n → ℝ =>
                  fderiv ℝ f y (fun k => if k = j then (1 : ℝ) else 0)) x
                (fun k => if k = i then (1 : ℝ) else 0))
      (fun ε : ℝ => ε) := by
  sorry
