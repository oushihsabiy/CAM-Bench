theorem isolated_smallest_eigenvalue_unit_eigenvector_is_strict_local_and_global_minimizer
    (n : ℕ) (P : RayleighQuotientMinimization n) (lam : ℝ)
    (hlam : Module.End.HasEigenvalue P.A.toLin' lam)
    (hiso : ∀ μ : ℝ, Module.End.HasEigenvalue P.A.toLin' μ → μ ≠ lam → lam < μ) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      Module.End.HasEigenvector P.A.toLin' lam x ∧ ‖x‖ = 1 →
        (∃ r > 0, ∀ y : EuclideanSpace ℝ (Fin n),
          ‖y‖ = 1 → 0 < ‖y - x‖ → ‖y - x‖ < r → P.objective x < P.objective y) ∧
        P.isMinimizer x := by
  sorry

/- [BLOCK chapter5 Ex.11 | 16 | thm]
Let A ∈ S^n, that is, A is an n × n real symmetric matrix. Consider the constrained optimization
problem on the unit sphere S^{n-1} = {x ∈ ℝ^n : ‖x‖_2 = 1} given by min_{x ∈ ℝ^n} x^→p A x, s.t.
‖x‖_2 = 1. Here, x^→p A x is the value of the Rayleigh quotient of the matrix A on the unit sphere.
Denote the smallest and largest eigenvalues of A by λ_{min} and λ_{max}, respectively. Further prove
that, in this problem, there do not exist points that are “locally optimal but not globally optimal”
in the strict sense; that is, any stationary point that does not correspond to the globally smallest
eigenvalue is not a local minimizer.
-/
