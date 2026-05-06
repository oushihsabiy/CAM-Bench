theorem unit_eigenvector_for_nonextremal_eigenvalue_is_not_minimizer_or_maximizer
    (n : ℕ) (P : RayleighQuotientMinimization n) (lam : ℝ)
    (hlam : Module.End.HasEigenvalue P.A.toLin' lam)
    (hnotmin : ¬ ∀ μ : ℝ, Module.End.HasEigenvalue P.A.toLin' μ → lam ≤ μ)
    (hnotmax : ¬ ∀ μ : ℝ, Module.End.HasEigenvalue P.A.toLin' μ → μ ≤ lam) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      Module.End.HasEigenvector P.A.toLin' lam x ∧ ‖x‖ = 1 →
        (∀ r : ℝ, r > 0 →
          ∃ y z : EuclideanSpace ℝ (Fin n),
            ‖y‖ = 1 ∧ ‖z‖ = 1 ∧
            0 < ‖y - x‖ ∧ ‖y - x‖ < r ∧
            0 < ‖z - x‖ ∧ ‖z - x‖ < r ∧
            P.objective y < P.objective x ∧ P.objective x < P.objective z) := by
  sorry
