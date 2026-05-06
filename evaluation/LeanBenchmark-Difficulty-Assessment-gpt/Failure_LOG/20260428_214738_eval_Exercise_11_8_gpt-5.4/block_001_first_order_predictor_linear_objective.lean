theorem first_order_predictor_linear_objective
    (n : ℕ)
    (f0 phi : (Fin n → ℝ) → ℝ)
    (xStar : ℝ → (Fin n → ℝ))
    (gradf0 gradphi : (Fin n → ℝ) → (Fin n → ℝ))
    (hessphi : (Fin n → ℝ) → ((Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (newtonStep : Fin n → ℝ)
    (t μ : ℝ)
    (hf0_linear : ∃ c : Fin n → ℝ, ∀ x y, fderiv ℝ f0 x y = dotProduct c y)
    (hgradphi : ∀ x y, fderiv ℝ phi x y = dotProduct (gradphi x) y)
    (hhessphi : ∀ x, fderiv ℝ gradphi x = hessphi x)
    (hcent :
      (t : ℝ) • gradf0 (xStar t) + gradphi (xStar t) = 0)
    (ht : 0 < t)
    (hμ : 0 < μ)
    (hderiv :
      hessphi (xStar t) (deriv xStar t) + gradf0 (xStar t) = 0)
    (hns :
      Function.Bijective (hessphi (xStar t)))
    (hnewton :
      hessphi (xStar t) newtonStep =
        -(((μ * t : ℝ) • gradf0 (xStar t)) + gradphi (xStar t))) :
    xStar t + (μ * t - t) • deriv xStar t = xStar t + newtonStep := by
  have hcent' : gradphi (xStar t) = -(t • gradf0 (xStar t)) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hcent
  have hderiv' : hessphi (xStar t) (deriv xStar t) = -(gradf0 (xStar t)) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hderiv
  have hnewton' : hessphi (xStar t) newtonStep = (t - μ * t) • gradf0 (xStar t) := by
    rw [hcent'] at hnewton
    calc
      hessphi (xStar t) newtonStep
          = -(((μ * t : ℝ) • gradf0 (xStar t)) + -(t • gradf0 (xStar t))) := hnewton
      _ = -(((μ * t : ℝ) • gradf0 (xStar t)) - t • gradf0 (xStar t)) := by
            rw [sub_eq_add_neg]
      _ = -(((μ * t) - t) • gradf0 (xStar t)) := by
            rw [sub_smul]
      _ = (t - μ * t) • gradf0 (xStar t) := by
            rw [neg_smul]
            congr 1
            ring
  have hscaled :
      hessphi (xStar t) ((μ * t - t) • deriv xStar t) = hessphi (xStar t) newtonStep := by
    calc
      hessphi (xStar t) ((μ * t - t) • deriv xStar t)
          = (μ * t - t) • hessphi (xStar t) (deriv xStar t) := by
              simp
      _ = (μ * t - t) • (-(gradf0 (xStar t))) := by rw [hderiv']
      _ = -((μ * t - t) • gradf0 (xStar t)) := by rw [smul_neg]
      _ = (t - μ * t) • gradf0 (xStar t) := by
            rw [neg_smul]
            congr 1
            ring
      _ = hessphi (xStar t) newtonStep := hnewton'.symm
  have hinj : Function.Injective (hessphi (xStar t)) := Function.Bijective.injective hns
  have hstep : (μ * t - t) • deriv xStar t = newtonStep := hinj hscaled
  rw [hstep]