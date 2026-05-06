theorem exp_integral_on_nonnegative_orthant_finite_iff
    (n : ℕ) (θ : Fin n → ℝ) :
    -- Finiteness iff all components are negative
    ((MeasureTheory.IntegrableOn
        (fun x : Fin n → ℝ => Real.exp (∑ i, θ i * x i))
        {x | ∀ i, 0 ≤ x i}) ↔ (∀ i, θ i < 0)) ∧
    -- When all negative, the integral equals ∏ (-θ i)⁻¹ (so a(θ) = ∏ (-θ i))
    ((∀ i, θ i < 0) →
      ∫ x : Fin n → ℝ in {x | ∀ i, 0 ≤ x i},
        Real.exp (∑ i, θ i * x i) = ∏ i : Fin n, (-θ i)⁻¹) := by
  sorry
