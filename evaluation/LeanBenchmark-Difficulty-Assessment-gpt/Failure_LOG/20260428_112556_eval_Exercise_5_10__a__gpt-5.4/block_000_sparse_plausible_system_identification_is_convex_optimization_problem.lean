theorem sparse_plausible_system_identification_is_convex_optimization_problem
    {n m T : ℕ} (hT : 2 ≤ T)
    (P : SparsePlausibleSystemIdentification n m T) :
    SparsePlausibleSystemIdentification.is_feasible P ∧
    ∀ A' : Matrix (Fin n) (Fin n) ℝ, ∀ B' : Matrix (Fin n) (Fin m) ℝ,
      sparsePlausibleSystemFeasible P.x P.u P.WsqrtInv A' B' →
        SparsePlausibleSystemIdentification.objective P ≤
          matrixEntrywiseL1Norm A' + matrixEntrywiseL1Norm B' := by
  sorry
