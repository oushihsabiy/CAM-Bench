theorem stationary_point_not_for_smallest_eigenvalue_is_not_local_minimizer
    (n : ℕ) (P : RayleighQuotientMinimization n) :
    ∀ (x : EuclideanSpace ℝ (Fin n)) (lam : ℝ),
      ‖x‖ = 1 →
      Module.End.HasEigenvalue P.A.toLin' lam →
      Module.End.HasEigenvector P.A.toLin' lam x →
      (¬ ∀ μ : ℝ, Module.End.HasEigenvalue P.A.toLin' μ → lam ≤ μ) →
      ¬ ∃ r > 0, ∀ y : EuclideanSpace ℝ (Fin n),
        ‖y‖ = 1 → ‖y - x‖ < r → P.objective x ≤ P.objective y := by
  sorry

/- [BLOCK chapter5 Ex.11 | 17 | thm]
Let A ∈ S^n, that is, A is an n × n real symmetric matrix. Consider the constrained optimization
problem on the unit sphere S^{n-1} = {x ∈ ℝ^n : ‖x‖_2 = 1} given by min_{x ∈ ℝ^n} x^→p A x, s.t.
‖x‖_2 = 1. Here, x^→p A x is the value of the Rayleigh quotient of the matrix A on the unit sphere.
Denote the smallest and largest eigenvalues of A by λ_{min} and λ_{max}, respectively. Prove that
all unit eigenvectors corresponding to non-extremal eigenvalues are saddle points. More
specifically, if x ∈ S^{n-1} satisfies Ax = λ x, where λ is neither λ_{min} nor λ_{max}, then x is a
saddle point of the objective function x^→p A x on the constraint set S^{n-1}.
-/
