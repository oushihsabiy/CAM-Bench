theorem geometricMean_concaveOn_positiveOrthant (n : ℕ) (hn : 0 < n) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ k, 0 < x k}
      (fun x : Fin n → ℝ => Real.rpow (∏ k, x k) (1 / (n : ℝ))) := by
  sorry
