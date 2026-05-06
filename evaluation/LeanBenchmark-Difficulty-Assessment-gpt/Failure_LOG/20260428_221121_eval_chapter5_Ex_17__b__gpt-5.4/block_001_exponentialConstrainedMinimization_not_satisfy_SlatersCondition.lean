theorem exponentialConstrainedMinimization_not_satisfy_SlatersCondition :
    ¬ SlatersCondition
      (domain := {p : ℝ × ℝ | p.2 ≠ 0})
      (A := fun _ : ℝ × ℝ => (0 : ℝ))
      (b := (0 : ℝ))
      (g := fun (_ : Unit) p => p.1 ^ 2 / p.2) := by
  sorry
