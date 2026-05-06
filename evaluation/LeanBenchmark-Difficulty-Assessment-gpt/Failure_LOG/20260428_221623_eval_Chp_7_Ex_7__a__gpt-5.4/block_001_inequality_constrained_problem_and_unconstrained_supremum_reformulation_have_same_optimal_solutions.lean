theorem inequality_constrained_problem_and_unconstrained_supremum_reformulation_have_same_optimal_solutions
    {n ι : Type} [Fintype ι]
    (P : InequalityConstrainedOptimizationProblem n ι)
    (h_feasible : ∃ x : n → ℝ, P.IsFeasible x)
    (h_finite_sup :
      ∀ x : n → ℝ,
        ∃ r : ℝ,
          sSup {s : ℝ | ∃ lam : ι → ℝ, (∀ i : ι, 0 ≤ lam i) ∧
            s = P.objective x + ∑ i : ι, lam i * P.constraint i x} = r) :
    let Q : UnconstrainedOptimizationProblem n :=
      { objective := fun x =>
          Classical.choose (h_finite_sup x) }
    {x : n → ℝ |
        P.IsFeasible x ∧
        ∀ y : n → ℝ, P.IsFeasible y → P.ObjectiveValue x ≤ P.ObjectiveValue y} =
      {x : n → ℝ |
        ∀ y : n → ℝ, Q.ObjectiveValue x ≤ Q.ObjectiveValue y} := by
  sorry
