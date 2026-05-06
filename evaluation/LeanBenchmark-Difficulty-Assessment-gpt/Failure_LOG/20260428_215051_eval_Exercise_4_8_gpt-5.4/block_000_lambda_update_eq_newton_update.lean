theorem lambda_update_eq_newton_update
    {n : ℕ} {Δ : ℝ} (g : EuclideanSpace ℝ (Fin n)) (q : Fin n → EuclideanSpace ℝ (Fin n))
    (μ : Fin n → ℝ) (lam : ℕ → ℝ) (p : ℝ → EuclideanSpace ℝ (Fin n)) (qnorm : ℕ → ℝ)
    (hΔ : 0 < Δ)
    (hp_sq : ∀ lam0 : ℝ,
      ‖p lam0‖ ^ 2 = ∑ j : Fin n, (⟪q j, g⟫)^2 / (μ j + lam0)^2)
    (hden : ∀ lam0 : ℝ, ∀ j : Fin n, μ j + lam0 ≠ 0)
    (hp : ∀ lam0 : ℝ, 0 < ‖p lam0‖)
    (hq_sq : ∀ ell : ℕ,
      qnorm ell ^ 2 = ∑ j : Fin n, (⟪q j, g⟫)^2 / (μ j + lam ell)^3)
    (hq : ∀ ell : ℕ, 0 < qnorm ell)
    (hphi2' : ∀ ell : ℕ,
      HasDerivAt (fun lam0 : ℝ => (‖p lam0‖)⁻¹ - Δ⁻¹)
        (-((qnorm ell)^2) / (‖p (lam ell)‖)^3) (lam ell)) :
    ∀ ell : ℕ,
      lam (ell + 1) = lam ell - (((‖p (lam ell)‖)⁻¹ - Δ⁻¹) / (-((qnorm ell)^2) / (‖p (lam ell)‖)^3)) ↔
        lam (ell + 1) = lam ell + ((‖p (lam ell)‖ / qnorm ell)^2) * ((‖p (lam ell)‖ - Δ) / Δ) := by
  sorry
