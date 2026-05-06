theorem center_of_gravity_minimizes_squared_distance_integral
    {n : ℕ} (C : Set (Fin n → ℝ))
    (hC_meas : MeasurableSet C)
    (hC_interior_nonempty : (interior C).Nonempty)
    (h_int_one_finite : MeasureTheory.Integrable (Set.indicator C (fun _ : Fin n → ℝ => (1 : ℝ))))
    (h_int_id_finite : MeasureTheory.Integrable (Set.indicator C (fun u : Fin n → ℝ => u)))
    (h_pos : 0 < ∫ u, Set.indicator C (fun _ : Fin n → ℝ => (1 : ℝ)) u ∂MeasureTheory.volume) :
    IsMinOn
      (fun x : Fin n → ℝ =>
        ∫ u, Set.indicator C (fun u : Fin n → ℝ => ‖u - x‖ ^ 2) u ∂MeasureTheory.volume)
      Set.univ
      (fun i : Fin n =>
        (∫ u, Set.indicator C (fun u : Fin n → ℝ => u i) u ∂MeasureTheory.volume) /
          (∫ u, Set.indicator C (fun _ : Fin n → ℝ => (1 : ℝ)) u ∂MeasureTheory.volume)) := by
  sorry
