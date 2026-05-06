theorem rayleigh_quotient_minimizers_and_maximizers_are_unit_extreme_eigenvectors
    (n : ℕ) (P : RayleighQuotientMinimization n) :
    ∃ lmin lmax : ℝ,
      (Module.End.HasEigenvalue P.A.toLin' lmin ∧
        ∀ ν : ℝ, Module.End.HasEigenvalue P.A.toLin' ν → lmin ≤ ν) ∧
      (Module.End.HasEigenvalue P.A.toLin' lmax ∧
        ∀ ν : ℝ, Module.End.HasEigenvalue P.A.toLin' ν → ν ≤ lmax) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        P.isMinimizer x ↔ ‖x‖ = 1 ∧ Module.End.HasEigenvector P.A.toLin' lmin x) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        P.isMaximizer x ↔ ‖x‖ = 1 ∧ Module.End.HasEigenvector P.A.toLin' lmax x) := by
  sorry

/- [BLOCK chapter5 Ex.11 | 15 | thm]
Let A ∈ S^n, that is, A is an n × n real symmetric matrix. Consider the constrained optimization
problem on the unit sphere S^{n-1} = {x ∈ ℝ^n : ‖x‖_2 = 1} given by min_{x ∈ ℝ^n} x^→p A x, s.t.
‖x‖_2 = 1. Here, x^→p A x is the value of the Rayleigh quotient of the matrix A on the unit sphere.
Denote the smallest and largest eigenvalues of A by λ_{min} and λ_{max}, respectively. Let λ be an
eigenvalue of A. If λ is strictly minimal in the eigenvalue sequence, that is, it is an isolated
smallest eigenvalue (equivalently, there are no other eigenvalues smaller than it in some
neighborhood), prove that any unit eigenvector corresponding to λ is a strict local minimizer of
this constrained optimization problem; and explain that such points are in fact also global
minimizers.
-/
