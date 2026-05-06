theorem phiRho_tendsto_atTop_of_component_product_tendsto_zero
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (x s : ℕ → Fin n → ℝ)
    (hpos : ∀ k j, 0 < x k j * s k j)
    (i : Fin n)
    (ε : ℝ) (hε : 0 < ε)
    (hxi : Tendsto (fun k => x k i * s k i) atTop (𝓝 0))
    (hμ :
      ∀ᶠ k in atTop,
        ε ≤ (∑ j : Fin n, x k j * s k j) / (n : ℝ)) :
    Tendsto
      (fun k =>
        ρ * Real.log (∑ j : Fin n, x k j * s k j) -
          ∑ j : Fin n, Real.log (x k j * s k j))
      atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hlog_tendsto : Tendsto (fun k => Real.log (x k i * s k i)) atTop atBot := by
    simpa using (Real.tendsto_log_nhds_zero.comp hxi)
  have hneglog_tendsto : Tendsto (fun k => -Real.log (x k i * s k i)) atTop atTop := by
    simpa using hlog_tendsto.neg_atTop
  have h_event :
      ∀ᶠ k in atTop,
        b ≤ -Real.log (x k i * s k i) := by
    exact (tendsto_atTop.1 hneglog_tendsto) b
  filter_upwards [h_event] with k hk
  have hsum_pos : 0 < ∑ j : Fin n, x k j * s k j := by
    classical
    refine Finset.sum_pos ?_
    intro j hj
    exact hpos k j
  have hlogi_le :
      Real.log (x k i * s k i) ≤ ∑ j : Fin n, Real.log (x k j * s k j) := by
    classical
    have hle :
        ({i} : Finset (Fin n)).sum (fun j => Real.log (x k j * s k j)) ≤
          ∑ j : Fin n, Real.log (x k j * s k j) := by
      refine Finset.single_le_sum ?_ ?_
      · intro j hj
        have : 0 < x k j * s k j := hpos k j
        exact le_of_lt (show 0 < Real.log (x k j * s k j) ∨ Real.log (x k j * s k j) ≤ Real.log (x k j * s k j) from by
          exact Or.inr le_rfl).elim
      · simp
    simpa using hle
  have hmain :
      ρ * Real.log (∑ j : Fin n, x k j * s k j) -
        ∑ j : Fin n, Real.log (x k j * s k j) ≤
      -Real.log (x k i * s k i) := by
    have hA : -(∑ j : Fin n, Real.log (x k j * s k j)) ≤ -Real.log (x k i * s k i) := by
      linarith
    have hB : ρ * Real.log (∑ j : Fin n, x k j * s k j) ≥ 0 ∨ ρ * Real.log (∑ j : Fin n, x k j * s k j) < 0 := by
      exact le_or_lt 0 (ρ * Real.log (∑ j : Fin n, x k j * s k j))
    rcases hB with hB | hB
    · linarith
    · linarith
  exact le_trans hk hmain