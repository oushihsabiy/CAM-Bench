theorem inequality_constrained_problem_eq_unconstrained_supremum_reformulation
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
    sInf {r : ℝ | ∃ x : n → ℝ, P.IsFeasible x ∧ P.ObjectiveValue x = r} =
      sInf {r : ℝ | ∃ x : n → ℝ, Q.ObjectiveValue x = r} := by
  sorry

/- [BLOCK Chp.7 Ex.7-(a) | 4 | thm]
Let f:ℝ^n → ℝ and cᵢ:ℝ^n → ℝ (i ∈ mathcal I) be given functions, and let mathcal I be the constraint
index set. Consider the inequality constrained optimization problem
min_{x ∈ ℝ^n} f(x)
quad s.t. quad cᵢ(x) ≤ 0,\ i ∈ mathcal I.
Define
F(x)=sup_{λ_i ≥ 0,\ i ∈ mathcal I}≤ft{ f(x)+sum_{i∈mathcal I}λ_i cᵢ(x)},
where the supremum is taken over all multiplier vectors satisfying λ_i ≥ 0 (i ∈ mathcal I). Prove
that the original problem is equivalent to unconstrained supremum reformulation. Here, “equivalent”
means: The set of optimal solutions of the original problem coincides with the set of optimal
solutions of the unconstrained problem min_{x ∈ ℝ^n} F(x).
-/
