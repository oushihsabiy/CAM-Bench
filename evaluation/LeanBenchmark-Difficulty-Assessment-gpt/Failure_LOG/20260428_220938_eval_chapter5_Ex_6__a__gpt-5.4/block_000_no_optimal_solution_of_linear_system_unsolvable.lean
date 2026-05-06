theorem no_optimal_solution_of_linear_system_unsolvable
    (p : LinearEqualityConstrainedProgram)
    (h : ¬ ∃ x : Fin p.n → ℝ, p.A *ᵥ x = p.b) :
    p.is_infeasible ∧
      ¬ ∃ x : Fin p.n → ℝ,
        p.is_feasible x ∧
        ∀ y : Fin p.n → ℝ, p.is_feasible y → p.objective x ≤ p.objective y := by
  sorry

/- [BLOCK chapter5 Ex.6-(a) | 33 | thm]
Let A ∈ ℝ^(m × n), b ∈ ℝ^m, and c ∈ ℝ^n. Consider the linear equality-constrained program. If the feasible set S={x ∈ ℝ^n : Ax=b} is nonempty, define N=Null(A)={d ∈ ℝ^n : Ad=0}. Give an explicit characterization of the optimal solutions of this problem, and prove the following conclusion: If there exists d ∈ N such that cᵀd<0, then the optimal value of the problem is -∞.
-/
