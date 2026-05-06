theorem l1_residual_minimization_dual_is_linf_constrained
    (m n : ℕ)
    (p : L1ResidualMinimization m n) :
    let d : L1ResidualDualProblem m n := {
      A := p.A
      b := p.b
    }
    d.A = p.A ∧
    d.b = p.b ∧
    (∀ y : Fin m → ℝ, d.objective y = -∑ i, p.b i * y i) ∧
    (∀ y : Fin m → ℝ,
      d.is_feasible y ↔ (∀ j, ∑ i, p.A i j * y i = 0) ∧ ‖y‖ ≤ (1 : ℝ)) := by
  sorry
