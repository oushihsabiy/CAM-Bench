theorem reverseSweep_cos_operation_rule
    (adjoint : Fin 1 → ℝ) (xkAdjoint xi : ℝ) :
    reverseSweep adjoint xkAdjoint
      (fun _ => -Real.sin xi) 0
      = adjoint 0 + xkAdjoint * (-(Real.sin xi)) := by
  sorry
