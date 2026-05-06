theorem linearizedConstraint_at_neg_point_0_1_0_02
    (p : Fin 2 → ℝ) :
    linearizedEqualityConstraint
      (fun x : Fin 2 → ℝ => fun _ : Fin 1 => x 0 ^ 2 + x 1 ^ 2 - (1 : ℝ))
      (fun x => circleConstraintLinearMap x)
      (fun i => if i = 0 then (-0.1 : ℝ) else (-0.02 : ℝ))
      p
    ↔ (-0.2 : ℝ) * p 0 + (-0.04 : ℝ) * p 1 - 0.9896 = 0 := by
  sorry
