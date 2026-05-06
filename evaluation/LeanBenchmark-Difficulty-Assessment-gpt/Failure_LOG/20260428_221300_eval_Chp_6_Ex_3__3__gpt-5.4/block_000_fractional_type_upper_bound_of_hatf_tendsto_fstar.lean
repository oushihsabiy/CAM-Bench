theorem fractional_type_upper_bound_of_hatf_tendsto_fstar
    {α : ℕ → ℝ} {hatf : ℕ → ℝ} {fstar c : ℝ}
    (hα : Tendsto (fun n => Finset.sum (Finset.range n) α) atTop atTop)
    (hinequality : ∀ k, hatf k - fstar ≤ c / (k + 1 : ℝ)) :
    ∀ k, hatf k ≤ fstar + c / (k + 1 : ℝ) := by
  sorry
