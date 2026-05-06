theorem neg_one_neg_one_is_strictLocalMinimum_for_quartic_example :
    IsStrictLocalMinimum
      (fun x : Fin 2 → ℝ =>
        2 * (x 0)^2 + (x 1)^2 - 2 * (x 0) * (x 1) + 2 * (x 0)^3 + (x 0)^4)
      (fun _ => (-1 : ℝ)) := by
  sorry

/- [BLOCK chapter5 Ex.5-(2) | 27 | thm]
Let the function f:ℝ^2 → ℝ be f(x_1,x_2)=2x_1^2+x_2^2-2x_1x_2+2x_1^3+x_1^4. Prove that (0,0) and (-1,-1) are also global minima of f on ℝ^2.
-/
