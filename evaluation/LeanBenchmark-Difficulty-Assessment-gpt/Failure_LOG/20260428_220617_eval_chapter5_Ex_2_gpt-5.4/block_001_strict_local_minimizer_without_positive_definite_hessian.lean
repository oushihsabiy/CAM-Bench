theorem strict_local_minimizer_without_positive_definite_hessian :
    ∃ (f : ℝ → ℝ) (xstar : ℝ),
      (∃ U : Set ℝ, U ∈ 𝓝 xstar ∧ ContDiffOn ℝ 2 f U) ∧
      IsStrictLocalMin f xstar ∧
      HasFDerivAt f (0 : ℝ →L[ℝ] ℝ) xstar ∧
      (∃ v : ℝ, v ≠ 0 ∧ (fderiv ℝ (fderiv ℝ f) xstar) v v = 0) := by
  sorry
