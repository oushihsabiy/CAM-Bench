theorem partialDeriv_sub_rule_revised
    {n : ℕ}
    {x_i x_j x_k : (Fin n → ℝ) → ℝ}
    (h : x_i = fun x => x_j x - x_k x)
    {U : Set (Fin n → ℝ)}
    (hi : TwiceDifferentiableOn (fun x => ![x_i x]) U)
    (hj : TwiceDifferentiableOn (fun x => ![x_j x]) U)
    (hk : TwiceDifferentiableOn (fun x => ![x_k x]) U) :
    (∀ p x, fderiv ℝ x_i x p = fderiv ℝ x_j x p - fderiv ℝ x_k x p) ∧
      ∀ p q x,
        fderiv ℝ (fun y => fderiv ℝ x_i y p) x q
          = fderiv ℝ (fun y => fderiv ℝ x_j y p) x q
            - fderiv ℝ (fun y => fderiv ℝ x_k y p) x q := by
  sorry

/-
Exercise 8.11 | 25 | thm

Let Dₚxᵢ denote the first partial derivative of an intermediate quantity xᵢ with respect to the
independent variable indexed by p, and let Dₚq xᵢ denote the corresponding second partial derivative
with respect to the variables indexed by p and q. Assume all quantities are twice differentiable
with respect to the underlying independent variables. If xᵢ = xⱼxₖ, then

Dₚxᵢ = xₖ Dₚxⱼ + xⱼ Dₚxₖ,

Dₚq xᵢ = xₖ Dₚq xⱼ + xⱼ Dₚq xₖ + Dₚxⱼ Dqxₖ + Dqxⱼ Dₚxₖ.
-/
