theorem log_sum_exp_convex
    (n : ℕ) :
    ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => Real.log (∑ k : Fin n, Real.exp (x k))) := by
  sorry
