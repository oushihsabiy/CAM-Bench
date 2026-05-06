theorem line_search_minimizers_for_quadratic :
    let f : (Fin 2 → ℝ) → ℝ := fun x => (x 0 + (x 1) ^ 2) ^ 2
    let x : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
    let p : Fin 2 → ℝ := fun i => if i = 0 then -1 else 1
    let P : LineSearchMinimizationProblem 2 := {
      f := f
      x := x
      p := p
    }
    ∀ α : ℝ,
      0 < α → (P.is_minimizer α ↔ α = 1) := by
  sorry
