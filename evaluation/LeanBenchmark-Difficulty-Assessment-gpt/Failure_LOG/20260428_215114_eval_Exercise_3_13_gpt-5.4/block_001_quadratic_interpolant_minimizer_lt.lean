theorem quadratic_interpolant_minimizer_lt
    {f : ℝ → ℝ} {xk pk α₀ c₁ α₁ : ℝ}
    (hα₀ : 0 < α₀)
    (hc₁ : 0 < c₁ ∧ c₁ < 1)
    (φ q : ℝ → ℝ)
    (φderiv : ℝ → ℝ)
    (hφ : φ = fun α => f (xk + α * pk))
    (hq_quad : ∃ a b c : ℝ, q = fun α => a + b * α + c * α ^ 2)
    (hq0 : q 0 = φ 0)
    (hq0' : HasDerivAt q (φderiv 0) 0)
    (hφα₀ : q α₀ = φ α₀)
    (hφ0' : HasDerivAt φ (φderiv 0) 0)
    (hφ0neg : φderiv 0 < 0)
    (hineq : φ α₀ > φ 0 + c₁ * α₀ * (φderiv 0))
    (hα₁ : IsLocalMin q α₁) :
    0 < (φ α₀ - φ 0 - α₀ * (φderiv 0)) / α₀ ^ 2 ∧
      α₁ < α₀ / (2 * (1 - c₁)) := by
  sorry
