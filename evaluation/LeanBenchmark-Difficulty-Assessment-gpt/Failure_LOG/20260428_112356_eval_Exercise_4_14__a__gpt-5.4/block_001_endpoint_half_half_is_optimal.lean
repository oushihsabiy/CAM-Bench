theorem endpoint_half_half_is_optimal
    {n : ℕ}
    (hn : 2 ≤ n)
    (a : Fin n → ℝ)
    (ha_mono : ∀ i j : Fin n, i ≤ j → a i ≥ a j)
    (ha_pos : ∀ i : Fin n, 0 < a i) :
    let P : LogarithmicSimplexProgram n :=
      { a := a
        b := fun k => (a k)⁻¹ }
    let x : Fin n → ℝ :=
      fun i => if i = ⟨0, Nat.lt_of_lt_of_le (by decide) hn⟩ ∨ i.1 + 1 = n then (1 : ℝ) / 2 else 0
    P.isFeasible x ∧
      ∀ y : Fin n → ℝ, P.isFeasible y → P.objective x ≤ P.objective y := by
  sorry
