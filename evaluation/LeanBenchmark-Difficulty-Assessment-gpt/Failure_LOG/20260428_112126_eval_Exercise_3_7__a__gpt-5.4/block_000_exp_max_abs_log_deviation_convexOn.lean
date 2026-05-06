theorem exp_max_abs_log_deviation_convexOn
    {m n : ℕ}
    (a : Fin n → (Fin m → ℝ))
    (I_des : ℝ)
    (hIdes : 0 < I_des)
    (D : Set (Fin m → ℝ))
    (hD :
      D = {p | (∀ j : Fin m, 0 ≤ p j) ∧ ∀ i : Fin n, 0 < ∑ j : Fin m, a i j * p j})
    (hne : D.Nonempty)
    (hn : NeZero n) :
    ConvexOn ℝ D (fun p =>
      Real.exp <|
        Finset.univ.sup' Finset.univ_nonempty (fun i : Fin n =>
          |Real.log (∑ j : Fin m, a i j * p j) - Real.log I_des|)) := by
  sorry
