theorem lp_quasinorm_concave_on_positive_orthant
    {n : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ i, 0 < x i}
      (fun x => (∑ i, (x i) ^ p) ^ (1 / p)) := by
  sorry
