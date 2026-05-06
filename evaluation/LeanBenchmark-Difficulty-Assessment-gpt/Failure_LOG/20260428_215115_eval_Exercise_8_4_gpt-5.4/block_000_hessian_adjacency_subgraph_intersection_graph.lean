theorem hessian_adjacency_subgraph_intersection_graph
    {n : ℕ} {H : Fin n → Fin n → ℝ}
    (hdiag : ∀ i : Fin n, H i i ≠ 0) :
    ∀ ⦃i j : Fin n⦄, i ≠ j → H i j ≠ 0 → ∃ k : Fin n, H k i ≠ 0 ∧ H k j ≠ 0 := by
  sorry
