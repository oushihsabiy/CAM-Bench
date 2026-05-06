theorem linearProgram_optimal_iff_standardForm_optimal
    (lp : LinearProgram)
    (sf : StandardFormLinearProgram)
    (hsf : sf.base = lp)
    {x : Fin lp.n → ℝ}
    (hx : x ∈ lp.feasibleSet) :
    (∀ y ∈ lp.feasibleSet, lp.objective x ≤ lp.objective y) ↔
      ∃ xPlus xMinus : Fin sf.base.n → ℝ,
        (xPlus = fun i => max (x (hsf ▸ i)) 0) ∧
        (xMinus = fun i => max (-x (hsf ▸ i)) 0) ∧
        let s : Fin sf.base.m → ℝ := fun i =>
          sf.base.h i - ∑ j : Fin sf.base.n, sf.base.G i j * x (hsf ▸ j)
        (xPlus, xMinus, s) ∈ sf.feasibleSet ∧
          (x = fun i => xPlus (hsf ▸ i) - xMinus (hsf ▸ i)) ∧
          ∀ yPlus yMinus : Fin sf.base.n → ℝ, ∀ t : Fin sf.base.m → ℝ,
            (yPlus, yMinus, t) ∈ sf.feasibleSet →
              sf.objective xPlus xMinus ≤ sf.objective yPlus yMinus := by
  subst hsf
  constructor
  · intro hopt
    refine ⟨fun i => max (x i) 0, fun i => max (-x i) 0, rfl, rfl, ?_⟩
    dsimp
    refine ⟨?_, ?_, ?_⟩
    · sorry
    · funext i
      by_cases h : 0 ≤ x i
      · have hneg : max (-x i) 0 = 0 := by
          apply max_eq_right
          linarith
        rw [max_eq_left h, hneg]
      · have hxle : x i ≤ 0 := le_of_not_ge h
        have hpos : max (x i) 0 = 0 := by
          apply max_eq_right
          exact hxle
        have hneg : max (-x i) 0 = -x i := by
          apply max_eq_left
          linarith
        rw [hpos, hneg]
        linarith
    · intro yPlus yMinus t hy
      sorry
  · rintro ⟨xPlus, xMinus, hxPlus, hxMinus, hfeas, hxrepr, hopt⟩
    intro y hy
    sorry