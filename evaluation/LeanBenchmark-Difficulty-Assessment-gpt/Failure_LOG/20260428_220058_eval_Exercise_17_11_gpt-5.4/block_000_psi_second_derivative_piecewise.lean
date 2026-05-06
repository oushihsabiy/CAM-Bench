theorem psi_second_derivative_piecewise
    {σ μ : ℝ} (hμ : μ ≠ 0) :
    (∀ t : ℝ,
      t < σ / μ →
        deriv
          (fun x : ℝ =>
            deriv
              (fun u : ℝ =>
                if u - σ / μ ≤ 0 then -σ * u + (μ / 2) * u^2 else -(σ^2) / (2 * μ))
              x)
          t = μ)
    ∧
    (∀ t : ℝ,
      t > σ / μ →
        deriv
          (fun x : ℝ =>
            deriv
              (fun u : ℝ =>
                if u - σ / μ ≤ 0 then -σ * u + (μ / 2) * u^2 else -(σ^2) / (2 * μ))
              x)
          t = 0)
    ∧
    ¬ ContinuousAt
      (fun t : ℝ =>
        deriv
          (fun x : ℝ =>
            deriv
              (fun u : ℝ =>
                if u - σ / μ ≤ 0 then -σ * u + (μ / 2) * u^2 else -(σ^2) / (2 * μ))
              x)
          t)
      (σ / μ) := by
  sorry

/- [BLOCK Exercise 17.11 | 22 | thm]
Let
psi(t,σ;μ)=
cases
-σ t+μ{2}t^2, & t-σ/μ≤ 0,\4pt]
-1{2μ}σ^2, & t-σ/μ>0.
cases
Assume μne 0. Also, let cᵢ:ℝ^n→ℝ be twice continuously differentiable, and let λ_i∈ℝ. Prove that the
Hessian matrix with respect to x of the function xmapsto psi(cᵢ(x),λ_i;μ) is
∇_x^2(psi(cᵢ(x),λ_i;μ))=
cases
(μ cᵢ(x)-λ_i)∇_x^2 cᵢ(x)+μ∇ cᵢ(x)∇ cᵢ(x)ᵀ, & cᵢ(x)<λ_i/μ,\6pt]
0, & cᵢ(x)≥ λ_i/μ.
cases
-/
