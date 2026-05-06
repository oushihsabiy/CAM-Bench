theorem hessian_psi_comp_piecewise
    {n : ℕ} (c : (Fin n → ℝ) → ℝ) (lam μ : ℝ) (x : Fin n → ℝ)
    (hc : TwiceContinuouslyDifferentiable c) (hμ : μ ≠ 0) :
    HessianMatrix
      (fun y =>
        if c y - lam / μ ≤ 0 then -lam * c y + (μ / 2) * (c y)^2 else -(lam^2) / (2 * μ))
      x
      =
    if c x < lam / μ then
      fun i j =>
        (μ * c x - lam) * HessianMatrix c x i j +
          μ * (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single i 1)) *
            (iteratedFDeriv ℝ 1 c x (fun _ => Pi.single j 1))
    else 0 := by
  sorry
