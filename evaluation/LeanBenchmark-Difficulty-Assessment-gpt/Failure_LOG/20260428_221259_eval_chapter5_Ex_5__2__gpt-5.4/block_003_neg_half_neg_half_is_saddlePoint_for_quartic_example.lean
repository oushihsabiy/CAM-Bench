theorem neg_half_neg_half_is_saddlePoint_for_quartic_example :
    IsSaddlePoint
      (fun x : Fin 2 → ℝ =>
        2 * (x 0)^2 + (x 1)^2 - 2 * (x 0) * (x 1) + 2 * (x 0)^3 + (x 0)^4)
      (fun _ => (-(1 : ℝ) / 2)) := by
  sorry

/- [BLOCK chapter5 Ex.5-(2) | 29 | thm]
Let the function f:ℝ^2 → ℝ be f(x_1,x_2)=2x_1^2+x_2^2-2x_1x_2+2x_1^3+x_1^4. Prove that f has no local maxima on ℝ^2.
-/
