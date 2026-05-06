theorem nearestPointProperty_nonempty_and_isClosed
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC :
      ∀ x0 : EuclideanSpace ℝ (Fin n),
        ∃! c : EuclideanSpace ℝ (Fin n),
          c ∈ C ∧ ∀ y : EuclideanSpace ℝ (Fin n), y ∈ C → ‖x0 - c‖ ≤ ‖x0 - y‖) :
    C.Nonempty ∧ IsClosed C := by
  sorry
