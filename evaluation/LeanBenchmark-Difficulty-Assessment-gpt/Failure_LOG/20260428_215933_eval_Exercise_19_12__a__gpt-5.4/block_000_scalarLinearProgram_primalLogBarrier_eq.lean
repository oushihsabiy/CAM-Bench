theorem scalarLinearProgram_primalLogBarrier_eq
    (μ x : ℝ) (hμ : 0 < μ) (hx0 : 0 < x) (hx1 : x < 1) :
    primalLogBarrier (α := ℝ) (ι := Fin 2)
      (fun y => y)
      (fun i y => if i = 0 then y else 1 - y)
      μ x
      hμ
      (by
        intro i
        fin_cases i
        · simpa using hx0
        · simpa using sub_pos.mpr hx1)
      =
      x - μ * Real.log x - μ * Real.log (1 - x) := by
  sorry
