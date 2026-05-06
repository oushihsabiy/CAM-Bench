theorem linearizedConstraint_at_zero_one_eq_two_p2_zero
    (p : Fin 2 → ℝ) :
    linearizedEqualityConstraint
      (fun x : Fin 2 → ℝ => fun _ : Fin 1 => x 0 ^ 2 + x 1 ^ 2 - (1 : ℝ))
      (fun x => circleConstraintLinearMap x)
      (fun i => if i = 0 then 0 else 1)
      p
    ↔ 2 * p 1 = 0 := by
  sorry

/-
Exercise 18.5 | 26 | thm

Let c : ℝ² → ℝ be defined by c(x) = x₁² + x₂² - 1 for x = (x₁, x₂)ᵀ ∈ ℝ². For a given point xₖ ∈ ℝ²,
define cₖ = c(xₖ) and Aₖ = ∇c(xₖ)ᵀ. The linearized equality constraint is Aₖp + cₖ = 0 for p = (p₁,
p₂)ᵀ ∈ ℝ². Prove that at xₖ = (0.1, 0.02)ᵀ, the linearized constraint is 0.2p₁ + 0.04p₂ - 0.9896 =
0.
-/
