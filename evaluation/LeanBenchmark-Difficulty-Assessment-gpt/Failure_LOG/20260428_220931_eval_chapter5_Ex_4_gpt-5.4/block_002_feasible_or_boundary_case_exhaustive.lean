theorem feasible_or_boundary_case_exhaustive
    {n : ℕ} (p : QuadraticBallConstrainedProblem n) (x₀ : Fin n → ℝ)
    (hx₀ : x₀ = -(p.A⁻¹.mulVec p.b)) :
    ‖x₀‖ ≤ p.Δ ∨ p.Δ < ‖x₀‖ := by
 sorry
