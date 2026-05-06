theorem partialDeriv_sub_rule
    {n : ℕ}
    {x_i x_j x_k : (Fin n → ℝ) → ℝ}
    (h : x_i = fun x => x_j x - x_k x)
    {U : Set (Fin n → ℝ)}
    (hi : TwiceDifferentiableOn (fun x => ![x_i x]) U)
    (hj : TwiceDifferentiableOn (fun x => ![x_j x]) U)
    (hk : TwiceDifferentiableOn (fun x => ![x_k x]) U) :
    (∀ p : Fin n, ∀ x, x ∈ U →
      (fderiv ℝ x_i x) (Pi.single p (1 : ℝ)) =
        (fderiv ℝ x_j x) (Pi.single p (1 : ℝ)) -
          (fderiv ℝ x_k x) (Pi.single p (1 : ℝ))) ∧
      ∀ p q : Fin n, ∀ x, x ∈ U →
        (fderiv ℝ
          (fun y => (fderiv ℝ x_i y) (Pi.single p (1 : ℝ))) x)
          (Pi.single q (1 : ℝ))
          =
            (fderiv ℝ
              (fun y => (fderiv ℝ x_j y) (Pi.single p (1 : ℝ))) x)
              (Pi.single q (1 : ℝ))
            -
            (fderiv ℝ
              (fun y => (fderiv ℝ x_k y) (Pi.single p (1 : ℝ))) x)
              (Pi.single q (1 : ℝ)) := by
  sorry

/- [BLOCK Exercise 8.11 | 31 | thm]
Let D_p xᵢ denote the first partial derivative of an intermediate quantity xᵢ with respect to the
independent variable indexed by p, and let D_{pq} xᵢ denote the corresponding second partial
derivative with respect to the variables indexed by p and q. Assume all quantities are twice
differentiable with respect to the underlying independent variables. If xᵢ = xⱼ xₖ, then
D_p xᵢ = xₖ D_p xⱼ + xⱼ D_p xₖ,
D_{pq} xᵢ = xₖ D_{pq} xⱼ + xⱼ D_{pq} xₖ + D_p xⱼ D_q xₖ + D_q xⱼ D_p xₖ.
-/
