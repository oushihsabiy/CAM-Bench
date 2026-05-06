theorem partialDeriv_mul_rule
    {n : ℕ}
    {x_i x_j x_k : (Fin n → ℝ) → ℝ}
    (h : x_i = fun x => x_j x * x_k x)
    {U : Set (Fin n → ℝ)}
    (hi : TwiceDifferentiableOn (fun x => ![x_i x]) U)
    (hj : TwiceDifferentiableOn (fun x => ![x_j x]) U)
    (hk : TwiceDifferentiableOn (fun x => ![x_k x]) U) :
    (∀ p : Fin n, ∀ x, x ∈ U →
        (fderiv ℝ x_i x) (Pi.single p (1 : ℝ))
          = x_k x * (fderiv ℝ x_j x) (Pi.single p (1 : ℝ)) + x_j x * (fderiv ℝ x_k x) (Pi.single p (1 : ℝ))) ∧
      ∀ p q : Fin n, ∀ x, x ∈ U →
        (fderiv ℝ (fun y => (fderiv ℝ x_i y) (Pi.single p (1 : ℝ))) x) (Pi.single q (1 : ℝ))
          = x_k x * (fderiv ℝ (fun y => (fderiv ℝ x_j y) (Pi.single p (1 : ℝ))) x) (Pi.single q (1 : ℝ))
            + x_j x * (fderiv ℝ (fun y => (fderiv ℝ x_k y) (Pi.single p (1 : ℝ))) x) (Pi.single q (1 : ℝ))
            + (fderiv ℝ x_j x) (Pi.single p (1 : ℝ)) * (fderiv ℝ x_k x) (Pi.single q (1 : ℝ))
            + (fderiv ℝ x_j x) (Pi.single q (1 : ℝ)) * (fderiv ℝ x_k x) (Pi.single p (1 : ℝ)) := by
  sorry

/- [BLOCK Exercise 8.11 | 32 | thm]
Let D_p xᵢ denote the first partial derivative of an intermediate quantity xᵢ with respect to the
independent variable indexed by p, and let D_{pq} xᵢ denote the corresponding second partial
derivative with respect to the variables indexed by p and q. Assume all quantities are twice
differentiable with respect to the underlying independent variables, and assume xₖ ≠ 0. If xᵢ =
xⱼ{xₖ}, then
D_p xᵢ = (xₖ D_p xⱼ - xⱼ D_p xₖ)/(xₖ^2),
and
D_{pq} xᵢ
= frac{D_{pq} xⱼ}{xₖ}
- (D_p xⱼ D_q xₖ + D_q xⱼ D_p xₖ)/(xₖ^2)
- frac{xⱼ D_{pq} xₖ}{xₖ^2}
+ (2 xⱼ D_p xₖ D_q xₖ)/(xₖ^3).
-/
