theorem optimal_value_eq_neg_infty_of_exists_null_direction
    (p : LinearEqualityConstrainedProgram)
    (hx : ∃ x : Fin p.n → ℝ, p.is_feasible x)
    (hd : ∃ d : Fin p.n → ℝ, p.A *ᵥ d = 0 ∧ dotProduct p.c d < 0) :
    ∀ M : ℝ, ∃ x : Fin p.n → ℝ, p.is_feasible x ∧ p.objective x < M := by
  sorry

/- [BLOCK chapter5 Ex.6-(a) | 34 | thm]
Let A ∈ ℝ^(m × n), b ∈ ℝ^m, and c ∈ ℝ^n. Consider the linear equality-constrained program. If the feasible set S={x ∈ ℝ^n : Ax=b} is nonempty, define N=Null(A)={d ∈ ℝ^n : Ad=0}. Give an explicit characterization of the optimal solutions of this problem, and prove the following conclusion: If there does not exist d ∈ N such that cᵀd<0, then c ⊥ N, equivalently, c ∈ Range(Aᵀ), and the objective function cᵀx is constant on the feasible set S; therefore every feasible point is an optimal solution.
-/
