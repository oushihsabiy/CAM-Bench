theorem infeasible_of_eventually_stationary_penalty
    {n : ℕ}
    (P : DifferentiableNonlinearProgram n)
    [Fintype P.equalityIndex] [Fintype P.inequalityIndex]
    (h : (Fin n → ℝ) → ℝ)
    (h_def : h =
      fun x : Fin n → ℝ =>
        (∑ i : P.equalityIndex, |P.equalityConstraint i x|) +
        ∑ i : P.inequalityIndex, max 0 (-P.inequalityConstraint i x))
    (xhat : Fin n → ℝ) (muhat : ℝ)
    (h_muhat_pos : 0 < muhat)
    (h_infeasible : P.toNonlinearProgram.IsInfeasible xhat)
    (h_stationary :
      ∀ μ : ℝ, muhat < μ →
        IsStationaryPoint (fun x : Fin n → ℝ => P.f x + μ * h x) xhat) :
    P.toNonlinearProgram.IsInfeasible xhat ∧ IsStationaryPoint h xhat := by
  sorry
