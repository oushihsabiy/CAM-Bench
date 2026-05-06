theorem unconstrained_minimizer_is_optimal_when_feasible
    {n : ℕ} (p : QuadraticBallConstrainedProblem n) (x₀ : Fin n → ℝ)
    (hx₀ : x₀ = -(p.A⁻¹.mulVec p.b))
    (hfeas : p.feasible x₀) :
    IsMinOn p.objective {x | p.feasible x} x₀ ∧
      p.objective x₀ = -dotProduct p.b (p.A⁻¹.mulVec p.b) := by
  sorry

/- [BLOCK chapter5 Ex.4 | 20 | thm]
Let quadratic ball-constrained problem. Let x_0 = -A^-1b. Prove that if ‖x_0‖_2 > Δ, then there exists a unique λ^* > 0 such that ‖(A+λ^* I)^-1 b‖_2 = Δ, and the optimal solution is x^* = -(A+λ^* I)^-1 b, and write down the corresponding expression for the optimal value of the optimization problem.
-/
