theorem origin_is_strictLocalMinimum_for_quartic_example :
    IsStrictLocalMinimum
      (fun x : Fin 2 → ℝ =>
        2 * (x 0)^2 + (x 1)^2 - 2 * (x 0) * (x 1) + 2 * (x 0)^3 + (x 0)^4)
      0 := by
  sorry

/- [BLOCK chapter5 Ex.5-(2) | 26 | thm]
Let the function f:ℝ^2 → ℝ be f(x_1,x_2)=2x_1^2+x_2^2-2x_1x_2+2x_1^3+x_1^4. Determine the nature of the point (-1,-1), and prove that (-1,-1) is a strict local minimum of f.
-/
