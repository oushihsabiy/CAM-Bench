theorem nonlinearProgramP_dual_optimal_value_eq_zero_and_duality_gap_eq_one :
    let pStar : ℝ := optimalValue nonlinearProgramP.feasibleSet nonlinearProgramP.objective
    let dStar : ℝ :=
      lagrangianDualProblem
        (fun p : {p : ℝ × ℝ // p.2 ≠ 0} =>
          fun lam : NNReal =>
            lagrangianWithIneqMultiplier
              (fun q : ℝ × ℝ => Real.exp q.1 + Real.exp q.2)
              (fun q : ℝ × ℝ => q.1 ^ 2 / q.2)
              p.1 lam)
    dStar = 0 ∧ dualityGap pStar dStar = 1 := by
  sorry
