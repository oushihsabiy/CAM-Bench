theorem first_order_predictor_eq_newton_update
    (n : ℕ)
    (f0 phi : (Fin n → ℝ) → ℝ)
    (xStar : ℝ → (Fin n → ℝ))
    (gradf0 gradphi : (Fin n → ℝ) → (Fin n → ℝ))
    (hessf0 hessphi : (Fin n → ℝ) → ((Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (newtonStep : Fin n → ℝ)
    (t μ : ℝ)
    (hgradf0 : ∀ x y, fderiv ℝ f0 x y = dotProduct (gradf0 x) y)
    (hgradphi : ∀ x y, fderiv ℝ phi x y = dotProduct (gradphi x) y)
    (hhessf0 : ∀ x, fderiv ℝ gradf0 x = hessf0 x)
    (hhessphi : ∀ x, fderiv ℝ gradphi x = hessphi x)
    (hcent :
      (t : ℝ) • gradf0 (xStar t) + gradphi (xStar t) = 0)
    (ht : 0 < t)
    (hμ : 0 < μ)
    (hderiv :
      (((t : ℝ) • hessf0 (xStar t)) + hessphi (xStar t)) (deriv xStar t) +
        gradf0 (xStar t) = 0)
    (hns :
      Function.Bijective (((t : ℝ) • hessf0 (xStar t)) + hessphi (xStar t)))
    (hnewton :
      (((μ * t : ℝ) • hessf0 (xStar t)) + hessphi (xStar t)) newtonStep =
        -(((μ * t : ℝ) • gradf0 (xStar t)) + gradphi (xStar t))) :
    xStar t + (μ * t - t) • deriv xStar t = xStar t + newtonStep := by
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := ((t : ℝ) • hessf0 (xStar t)) + hessphi (xStar t)
  have hAderiv : A (deriv xStar t) = -gradf0 (xStar t) := by
    have h := hderiv
    simpa [A] using eq_neg_of_add_eq_zero_left h
  have hcent' : gradphi (xStar t) = -(t : ℝ) • gradf0 (xStar t) := by
    have h := eq_neg_of_add_eq_zero_left hcent
    simpa using h.symm
  have hAnewton : A newtonStep = (μ * t - t) • (-(gradf0 (xStar t))) := by
    apply (Function.Bijective.injective hns)
    calc
      A (A newtonStep)
          = A (((μ * t - t) : ℝ) • (-(gradf0 (xStar t)))) := by
            congr 1
            calc
              A newtonStep
                  = (((μ * t : ℝ) • hessf0 (xStar t)) + hessphi (xStar t)) newtonStep := by
                    simp [A]
              _ = -(((μ * t : ℝ) • gradf0 (xStar t)) + gradphi (xStar t)) := hnewton
              _ = -(((μ * t : ℝ) • gradf0 (xStar t)) + (-(t : ℝ) • gradf0 (xStar t))) := by
                    rw [hcent']
              _ = (μ * t - t) • (-(gradf0 (xStar t))) := by
                    ext i
                    simp
                    ring
      _ = A newtonStep := by rfl
  have hEq : (μ * t - t) • deriv xStar t = newtonStep := by
    apply (Function.Bijective.injective hns)
    calc
      A ((μ * t - t) • deriv xStar t)
          = (μ * t - t) • A (deriv xStar t) := by simp [A]
      _ = (μ * t - t) • (-(gradf0 (xStar t))) := by rw [hAderiv]
      _ = A newtonStep := by rw [hAnewton]
  rw [hEq]

/- [BLOCK Exercise 11.8 | 35 | thm]
Consider an inequality-constrained problem with no equality constraints. Let f₀:ℝ^n→ℝ and φ:ℝ^n→ℝ be
twice differentiable, and for t>0 define F_t(x)=t f₀(x)+φ(x). For each t, let x*(t) be a minimizer
of F_t, so that t∇ f₀(x*(t)) + ∇ φ(x*(t)) = 0. Assume that all derivatives used below exist and that
t∇^2 f₀(x*(t)) + ∇^2 φ(x*(t)) is nonsingular. The first-order predictor based on the tangent to the
central path is x=x*(t)+(d x*(t))/(dt)(μ t-t), where μ>0. Determine what happens when f₀ is linear.
-/