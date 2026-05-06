theorem constantVectorApproximation_l2_unique_minimizer_mean
    (p : ConstantVectorApproximationProblem n) :
    ∀ x : ℝ,
      p.objectiveL2 x = sInf (Set.range p.objectiveL2) ↔
        x = (∑ i : Fin n, p.b i) / n := by
  intro x
  simpa using p.is_argmin_objectiveL2_iff x

/- [BLOCK Exercise 6.2-(a) | 8 | thm]
Consider the constant vector approximation problem. Let n ∈ ℕ with n ≥ 1, let b=(b₁,dots,bₙ) ∈ ℝ^n,
and let 1 ∈ ℝ^n denote the vector whose entries are all 1. For a scalar variable x ∈ ℝ, consider the
optimization problem min_{x ∈ ℝ} ‖x1-b‖. Prove that, for the ell_1-norm, the set of minimizers is
exactly the set of medians of b₁,dots,bₙ, i.e., the set of all x ∈ ℝ such that at least half of the
numbers bᵢ are ≤ x and at least half are ≥ x.
-/