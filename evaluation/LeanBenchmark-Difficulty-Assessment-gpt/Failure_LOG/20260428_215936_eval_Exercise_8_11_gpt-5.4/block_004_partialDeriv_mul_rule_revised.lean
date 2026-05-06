theorem partialDeriv_mul_rule_revised
    {n : ℕ}
    {x_i x_j x_k : (Fin n → ℝ) → ℝ}
    (h : x_i = fun x => x_j x * x_k x)
    {U : Set (Fin n → ℝ)}
    (hi : TwiceDifferentiableOn (fun x => ![x_i x]) U)
    (hj : TwiceDifferentiableOn (fun x => ![x_j x]) U)
    (hk : TwiceDifferentiableOn (fun x => ![x_k x]) U) :
    (∀ p : Fin n, ∀ x : Fin n → ℝ,
        fderiv ℝ x_i x (Pi.single p (1 : ℝ))
          = x_k x * fderiv ℝ x_j x (Pi.single p (1 : ℝ))
            + x_j x * fderiv ℝ x_k x (Pi.single p (1 : ℝ))) ∧
      ∀ p q : Fin n, ∀ x : Fin n → ℝ,
        fderiv ℝ
            (fun y => fderiv ℝ x_i y (Pi.single p (1 : ℝ))) x
            (Pi.single q (1 : ℝ))
          = x_k x * fderiv ℝ
              (fun y => fderiv ℝ x_j y (Pi.single p (1 : ℝ))) x
              (Pi.single q (1 : ℝ))
            + x_j x * fderiv ℝ
              (fun y => fderiv ℝ x_k y (Pi.single p (1 : ℝ))) x
              (Pi.single q (1 : ℝ))
            + fderiv ℝ x_j x (Pi.single p (1 : ℝ))
                * fderiv ℝ x_k x (Pi.single q (1 : ℝ))
            + fderiv ℝ x_j x (Pi.single q (1 : ℝ))
                * fderiv ℝ x_k x (Pi.single p (1 : ℝ)) := by
  sorry
