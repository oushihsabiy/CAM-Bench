theorem logarithmicPenaltyMethod_terminates_or_converges
    {ι X : Type*} [DecidableEq ι]
    (M : LogarithmicPenaltyFunctionMethod ι X)
    (hInterior : ∀ k : ℕ, M.problem.isInteriorPoint (M.x (k + 1)))
    (h_bdd_below :
      BddBelow (M.problem.objective '' M.problem.feasibleSet))
    :
    (∃ N : ℕ, ∀ k : ℕ, N ≤ k → M.x (k + 1) = M.x k) ∨
      (Tendsto
          (fun k : ℕ =>
            M.σ k *
              Finset.sum M.problem.activeSet
                (fun i => Real.log (-M.problem.constraint i (M.x (k + 1)))))
          atTop (𝓝 0) ∧
        Tendsto
          (fun k : ℕ => M.problem.objective (M.x k))
          atTop
          (𝓝 (sInf (M.problem.objective '' M.problem.interior)))) := by
  sorry
