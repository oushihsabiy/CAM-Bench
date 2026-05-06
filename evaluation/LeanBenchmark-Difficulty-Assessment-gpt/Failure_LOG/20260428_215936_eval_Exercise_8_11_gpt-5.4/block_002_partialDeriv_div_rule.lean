theorem partialDeriv_div_rule
    {n : ℕ}
    {x_i x_j x_k : (Fin n → ℝ) → ℝ}
    (h : x_i = fun x => x_j x / x_k x)
    {U : Set (Fin n → ℝ)}
    (hi : TwiceDifferentiableOn (fun x => ![x_i x]) U)
    (hj : TwiceDifferentiableOn (fun x => ![x_j x]) U)
    (hk : TwiceDifferentiableOn (fun x => ![x_k x]) U)
    (hk_ne : ∀ x, x ∈ U → x_k x ≠ 0) :
    (∀ p : Fin n, ∀ x, x ∈ U →
        (fderiv ℝ x_i x) (Pi.single p (1 : ℝ))
          = (x_k x * (fderiv ℝ x_j x) (Pi.single p (1 : ℝ))
              - x_j x * (fderiv ℝ x_k x) (Pi.single p (1 : ℝ))) / (x_k x)^2) ∧
      ∀ p q : Fin n, ∀ x, x ∈ U →
        (fderiv ℝ (fun y => (fderiv ℝ x_i y) (Pi.single p (1 : ℝ))) x) (Pi.single q (1 : ℝ))
          = (fderiv ℝ (fun y => (fderiv ℝ x_j y) (Pi.single p (1 : ℝ))) x) (Pi.single q (1 : ℝ)) / x_k x
            - ((fderiv ℝ x_j x) (Pi.single p (1 : ℝ)) * (fderiv ℝ x_k x) (Pi.single q (1 : ℝ))
                + (fderiv ℝ x_j x) (Pi.single q (1 : ℝ)) * (fderiv ℝ x_k x) (Pi.single p (1 : ℝ))) / (x_k x)^2
            - x_j x * (fderiv ℝ (fun y => (fderiv ℝ x_k y) (Pi.single p (1 : ℝ))) x) (Pi.single q (1 : ℝ)) / (x_k x)^2
            + (2 * x_j x * (fderiv ℝ x_k x) (Pi.single p (1 : ℝ)) * (fderiv ℝ x_k x) (Pi.single q (1 : ℝ))) / (x_k x)^3 := by
  sorry

/- [BLOCK Exercise 8.11 | 24 | thm]
Let D_p xᵢ denote the first partial derivative of an intermediate quantity xᵢ with respect to the
independent variable indexed by p, and let D_{pq} xᵢ denote the corresponding second partial
derivative with respect to the variables indexed by p and q. Assume all quantities are twice
differentiable with respect to the underlying independent variables. If xᵢ = xⱼ - xₖ, then
D_p xᵢ = D_p xⱼ - D_p xₖ,
D_{pq} xᵢ = D_{pq} xⱼ - D_{pq} xₖ.
-/
