theorem centroid_pairwise_sqdist_identity
    {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d)))
    (hS : S.Nonempty) :
    let n : ℝ := (S.card : ℝ)
    let c : EuclideanSpace ℝ (Fin d) := (n⁻¹ : ℝ) • ∑ a ∈ S, a
    2 * n * (∑ a ∈ S, ‖a - c‖ ^ 2) = ∑ a ∈ S, ∑ a' ∈ S, ‖a - a'‖ ^ 2 := by
  sorry
