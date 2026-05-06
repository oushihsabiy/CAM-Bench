theorem quadratic_interpolant_eq
    {f : ℝ → ℝ} {xk pk α₀ : ℝ}
    (hα₀ : 0 < α₀)
    (φ q : ℝ → ℝ)
    (φderiv : ℝ → ℝ)
    (hφ : φ = fun α => f (xk + α * pk))
    (hq_quad : ∃ a b c : ℝ, q = fun α => a + b * α + c * α ^ 2)
    (hq0 : q 0 = φ 0)
    (hq0' : HasDerivAt q (φderiv 0) 0)
    (hφα₀ : q α₀ = φ α₀)
    (hφ0' : HasDerivAt φ (φderiv 0) 0) :
    q = fun α =>
      φ 0 + (φderiv 0) * α +
        ((φ α₀ - φ 0 - α₀ * (φderiv 0)) / α₀ ^ 2) * α ^ 2 := by
  sorry

/- [BLOCK Exercise 3.13 | 26 | thm]
Let φ : ℝ → ℝ be defined by φ(α)=f(xₖ+α pₖ), where f is differentiable, so that φ(0)=f(xₖ) and
φ'(0)=∇ f(xₖ)ᵀ pₖ. Let α_0>0 and 0<c₁<1. Let q(α) be the quadratic polynomial satisfying q(0)=φ(0),
q'(0)=φ'(0), q(α_0)=φ(α_0). Assume that φ(α_0) > φ(0)+c_1α_0φ'(0). Show that the quadratic
coefficient
(φ(α_0)-φ(0)-α_0φ'(0))/(α_0^2)
is positive, and that the minimizer α_1 of q satisfies α_1<(α_0)/(2(1-c₁)).
-/
