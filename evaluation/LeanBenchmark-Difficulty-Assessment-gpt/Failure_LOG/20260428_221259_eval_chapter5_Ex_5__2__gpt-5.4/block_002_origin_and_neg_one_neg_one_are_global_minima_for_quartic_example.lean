theorem origin_and_neg_one_neg_one_are_global_minima_for_quartic_example
    (x : Fin 2 → ℝ) :
    let f : (Fin 2 → ℝ) → ℝ :=
      fun y : Fin 2 → ℝ =>
        2 * (y 0)^2 + (y 1)^2 - 2 * (y 0) * (y 1) + 2 * (y 0)^3 + (y 0)^4
    f 0 ≤ f x ∧ f (fun _ => (-1 : ℝ)) ≤ f x := by
  sorry

/- [BLOCK chapter5 Ex.5-(2) | 28 | thm]
Let the function f:ℝ^2 → ℝ be f(x_1,x_2)=2x_1^2+x_2^2-2x_1x_2+2x_1^3+x_1^4. Determine the nature of the point ≤ft(-\frac12,-\frac12
ight), and prove that ≤ft(-rac12,-rac12
ight) is a saddle point of f.
-/
