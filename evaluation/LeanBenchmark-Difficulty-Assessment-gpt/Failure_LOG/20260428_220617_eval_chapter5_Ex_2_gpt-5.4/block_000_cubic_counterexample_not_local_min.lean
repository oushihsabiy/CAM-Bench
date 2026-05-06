theorem cubic_counterexample_not_local_min :
    ∃ (f : ℝ → ℝ) (xstar : ℝ),
      (∃ U : Set ℝ, U ∈ 𝓝 xstar ∧ ContDiffOn ℝ 2 f U) ∧
      HasFDerivAt f (0 : ℝ →L[ℝ] ℝ) xstar ∧
      (∀ v : ℝ, 0 ≤ (fderiv ℝ (fderiv ℝ f) xstar) v v) ∧
      ¬ IsLocalMin f xstar := by
  sorry

/- [BLOCK chapter5 Ex.2 | 9 | thm]
Consider the unconstrained minimization problem min_(x ∈ ℝ^n) f(x), where the function f:ℝ^n → ℝ is twice continuously differentiable in some open neighborhood of the point x^*. The following conclusions are known: if x^* is a local minimizer, then necessarily ∇ f(x^*) = 0, ∇^2 f(x^*) ⪰ 0. If ∇ f(x^*) = 0, ∇^2 f(x^*) ≻ 0, then x^* is a strict local minimizer. Here, ∇ f(x^*) denotes the gradient of f at x^*, and ∇^2 f(x^*) denotes the Hessian matrix of f at x^*; ∇^2 f(x^*) ⪰ 0 means that this matrix is positive semidefinite, and ∇^2 f(x^*) ≻ 0 means that this matrix is positive definite. If there exists a neighborhood U of x^* such that f(x) ≥ f(x^*) for every x ∈ U, then x^* is called a local minimizer; if f(x) > f(x^*) for every x ∈ U∖{x^*}, then x^* is called a strict local minimizer. Construct a function f and a point x^* such that x^* is a strict local minimizer, but the positive definiteness requirement in the second-order sufficient condition is not satisfied; that is, it is not necessarily true that ∇ f(x^*) = 0, ∇^2 f(x^*) ≻ 0. In other words, give an example to show that a strict local minimizer does not necessarily have to satisfy that the Hessian is positive definite at that point.
-/
