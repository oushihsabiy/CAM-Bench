theorem exp_max_log_deviation_convexOn
    {m n : ℕ} [NeZero n]
    (a : Fin n → EuclideanSpace ℝ (Fin m)) {I_des : ℝ} (hI_des : 0 < I_des) :
    ConvexOn ℝ
      {p : EuclideanSpace ℝ (Fin m) |
        (∀ j : Fin m, 0 ≤ p j) ∧ ∀ i : Fin n, 0 < ⟪a i, p⟫}
      (fun p =>
        Real.exp
          (Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin n => |Real.log ⟪a i, p⟫ - Real.log I_des|))) := by
  sorry
