theorem gradient_characterization {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x h : EuclideanSpace ℝ (Fin n)) (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x h = ⟪gradient f x, h⟫ := by
  sorry

/- [BLOCK Exercise 2.3 | 7 | defn]
Let f : ℝ^n → ℝ be twice differentiable at x. The Hessian of f at x is the matrix ∇^2 f(x)
∈ ℝ^n×n with entries (∇^2 f(x))_ij = (∂^2 f)/(∂ xᵢ ∂ xⱼ)(x).
-/
