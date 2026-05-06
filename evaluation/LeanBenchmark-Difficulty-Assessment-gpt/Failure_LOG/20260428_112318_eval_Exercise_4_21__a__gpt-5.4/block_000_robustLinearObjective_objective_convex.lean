theorem robustLinearObjective_objective_convex
    (p : RobustLinearObjectiveProblem)
    (q : ℕ)
    (F : Fin q → Fin p.n → ℝ)
    (g : Fin q → ℝ)
    (hpC :
      p.C =
        {c : Fin p.n → ℝ |
          ∀ i : Fin q, (∑ j : Fin p.n, F i j * c j) ≤ g i})
    (hCnonempty : p.C.Nonempty)
    (hfeas : ∃ x : Fin p.n → ℝ, p.isFeasible x) :
    ExtendedValueConvex p.n p.objective := by
  sorry
