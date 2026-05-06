theorem maximizing_logLikelihood_equiv_logLikelihoodConvexProgram
    (P : LogLikelihoodConvexProgram)
    (f : ℝ → ℝ)
    (hf_density : ProbabilityDensity f)
    (hf_logConcave : LogConcave f)
    -- g(t) = -log f(t) on the support where f(t) > 0
    (hg : ∀ t, 0 < f t → P.g t = -Real.log (f t)) :
    -- (1) The log-likelihood equals -P.objective at any feasible (x,μ,σ) where f > 0 at all residuals,
    --     so maximizing the log-likelihood is equivalent to minimizing P.objective.
    (∀ (x : Fin P.n → ℝ) (μ σ : ℝ),
      P.isFeasible x μ σ →
      (∀ i : Fin P.m, 0 < f (P.residual x μ σ i)) →
      -(↑P.m * Real.log σ) + ∑ i : Fin P.m, Real.log (f (P.residual x μ σ i))
        = -(P.objective x μ σ)) ∧
    -- (2) P.objective is convex on the feasible domain {(x, μ, σ) | σ > 0}
    ConvexOn ℝ
      {p : (Fin P.n → ℝ) × ℝ × ℝ | 0 < p.2.2}
      (fun p => P.objective p.1 p.2.1 p.2.2) := by
  sorry
