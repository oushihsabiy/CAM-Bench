theorem linear_min_on_closure_nonnegative_compl_reduces_to_axis_problems
    (n : ℕ)
    (C : Set (Fin n → ℝ))
    (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C)
    (hC_bdd : Bornology.IsBounded C)
    (hC_convex : Convex ℝ C)
    (h0C : (0 : Fin n → ℝ) ∈ C)
    (hC_nonneg : ∀ x ∈ C, ∀ i, 0 ≤ x i)
    (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hn : 0 < n) :
    ∃ k : Fin n, ∃ α : ℝ,
      0 ≤ α ∧
        (α • (fun i => if i = k then (1 : ℝ) else 0)) ∈
          closure ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} \ C) ∧
        (∀ y ∈ closure ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} \ C),
          ∑ i, c i * ((α • (fun j => if j = k then (1 : ℝ) else 0)) i) ≤
            ∑ i, c i * y i) := by
  sorry
