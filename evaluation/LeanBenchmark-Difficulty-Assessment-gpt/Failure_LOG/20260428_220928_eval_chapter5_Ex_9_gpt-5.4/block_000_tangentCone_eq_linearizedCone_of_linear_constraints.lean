theorem tangentCone_eq_linearizedCone_of_linear_constraints
    {n I E : Type*} [Fintype n] [Fintype I] [Fintype E]
    (cI : I → EuclideanSpace ℝ n → ℝ) (cE : E → EuclideanSpace ℝ n → ℝ)
    (x : EuclideanSpace ℝ n)
    (hfeasI : ∀ i, cI i x ≤ 0)
    (hfeasE : ∀ i, cE i x = 0)
    (hdiffI : ∀ i, DifferentiableAt ℝ (cI i) x)
    (hdiffE : ∀ i, DifferentiableAt ℝ (cE i) x)
    (hlinI : ∀ i, ∃ L : EuclideanSpace ℝ n →ₗ[ℝ] ℝ, ∀ y, cI i y = cI i x + L (y - x))
    (hlinE : ∀ i, ∃ L : EuclideanSpace ℝ n →ₗ[ℝ] ℝ, ∀ y, cE i y = cE i x + L (y - x))
    :
    let X : Set (EuclideanSpace ℝ n) := {y | (∀ i, cI i y ≤ 0) ∧ (∀ i, cE i y = 0)}
    {d : EuclideanSpace ℝ n |
      ∃ xk : ℕ → EuclideanSpace ℝ n, (∀ k, xk k ∈ X) ∧
        ∃ tk : ℕ → ℝ, (∀ k, 0 < tk k) ∧ Tendsto tk atTop (𝓝 0) ∧
          Tendsto (fun k => (1 / tk k) • (xk k - x)) atTop (𝓝 d)} =
    {d : EuclideanSpace ℝ n |
      (∀ i, cI i x = 0 → fderiv ℝ (cI i) x d ≤ 0) ∧
      (∀ i, fderiv ℝ (cE i) x d = 0)} := by
  sorry
