theorem standardForm_optimal_iff_linearProgram_optimal
    (sf : StandardFormLinearProgram)
    {xPlus xMinus : Fin sf.base.n → ℝ}
    {s : Fin sf.base.m → ℝ}
    (hfeas : (xPlus, xMinus, s) ∈ sf.feasibleSet) :
    (∀ yPlus yMinus : Fin sf.base.n → ℝ, ∀ t : Fin sf.base.m → ℝ,
        (yPlus, yMinus, t) ∈ sf.feasibleSet →
          sf.objective xPlus xMinus ≤ sf.objective yPlus yMinus) ↔
      (let x : Fin sf.base.n → ℝ := fun i => xPlus i - xMinus i
       x ∈ sf.base.feasibleSet ∧
         ∀ y ∈ sf.base.feasibleSet, sf.base.objective x ≤ sf.base.objective y) := by
  constructor
  · intro h
    dsimp
    constructor
    · rcases hfeas with ⟨hxnonneg, hmnonneg, hsnonneg, hEq⟩
      exact hEq
    · intro y hy
      let yPlus : Fin sf.base.n → ℝ := fun i => max (y i) 0
      let yMinus : Fin sf.base.n → ℝ := fun i => max (-y i) 0
      have hydecomp : y = fun i => yPlus i - yMinus i := by
        funext i
        dsimp [yPlus, yMinus]
        by_cases hyi : 0 ≤ y i
        · rw [max_eq_left hyi, max_eq_right]
          · ring
          · linarith
        · have hyi' : y i ≤ 0 := le_of_not_ge hyi
          rw [max_eq_right, max_eq_left]
          · ring
          · linarith
          · linarith
          · linarith
      have hy' : (yPlus, yMinus, fun _ => 0) ∈ sf.feasibleSet := by
        rcases hfeas with ⟨hxnonneg, hmnonneg, hsnonneg, hEq⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i
          dsimp [yPlus]
          exact le_max_right _ _
        · intro i
          dsimp [yMinus]
          exact le_max_right _ _
        · intro i
          exact le_rfl
        · simpa [hydecomp]
      have hopt := h yPlus yMinus (fun _ => 0) hy'
      simpa [StandardFormLinearProgram.objective] using hopt
  · dsimp
    rintro ⟨hxfeas, hopt⟩ yPlus yMinus t hy
    rcases hy with ⟨hyP, hyM, ht, hEq⟩
    have hybase : (fun i => yPlus i - yMinus i) ∈ sf.base.feasibleSet := hEq
    have hopt' := hopt (fun i => yPlus i - yMinus i) hybase
    simpa [StandardFormLinearProgram.objective] using hopt'