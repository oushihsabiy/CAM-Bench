theorem linfty_minimization_problem_reformulation
    (P : LinftyMinimizationProblem) :
    {r : ℝ | ∃ x : Fin P.n → ℝ, LinftyMinimizationProblem.objective P x = r} =
    {r : ℝ | ∃ xt : (Fin P.n → ℝ) × ℝ,
      LinftyMinimizationProblemReformulation.isFeasible
        (P.toReformulation) xt ∧
      LinftyMinimizationProblemReformulation.objective
        (P.toReformulation) xt = r} := by
  sorry

/- [BLOCK Exercise 12.5 | 13 | thm]
Let n,m ∈ ℕ with m ≥ 1, and let v:ℝ^n → ℝ^m be smooth, with components v(x)=(v₁(x),ldots,vₘ(x)) and
vᵢ:ℝ^n → ℝ smooth for i=1,ldots,m. For y=(y₁,ldots,yₘ)∈ℝ^m, define ‖y‖_{∞}=max_{1≤ i≤ m}|yᵢ|. Prove
that the problem max-function minimization reformulation.
-/
