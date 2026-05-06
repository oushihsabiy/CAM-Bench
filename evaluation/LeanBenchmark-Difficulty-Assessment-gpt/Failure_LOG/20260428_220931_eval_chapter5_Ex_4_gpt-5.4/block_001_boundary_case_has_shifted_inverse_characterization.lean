theorem boundary_case_has_shifted_inverse_characterization
    {n : ℕ} (p : QuadraticBallConstrainedProblem n) (x₀ : Fin n → ℝ)
    (hx₀ : x₀ = -(p.A⁻¹.mulVec p.b))
    (houtside : p.Δ < ‖x₀‖) :
    ∃! lam : ℝ,
      0 < lam ∧
      ‖((p.A + lam • 1)⁻¹).mulVec p.b‖ = p.Δ ∧
      IsMinOn p.objective {x | p.feasible x} (-(((p.A + lam • 1)⁻¹).mulVec p.b)) ∧
      p.objective (-(((p.A + lam • 1)⁻¹).mulVec p.b)) =
        -dotProduct p.b (((p.A + lam • 1)⁻¹).mulVec p.b) -
          lam * p.Δ ^ 2 := by
  sorry

/- [BLOCK chapter5 Ex.4 | 21 | thm]
Let quadratic ball-constrained problem. Let x_0 = -A^-1b. Explain why the two cases ‖x_0‖_2 ≤ Δ and ‖x_0‖_2 > Δ exhaust all possibilities.
-/
