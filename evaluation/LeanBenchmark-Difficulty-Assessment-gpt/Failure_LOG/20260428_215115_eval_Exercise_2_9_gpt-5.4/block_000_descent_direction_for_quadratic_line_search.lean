theorem descent_direction_for_quadratic_line_search :
    Exercise_2_9.IsDescentDirectionAt
      (fun x : Fin 2 → ℝ => (x 0 + (x 1) ^ 2) ^ 2)
      (fun i : Fin 2 => if i = 0 then 1 else 0)
      (fun i : Fin 2 => if i = 0 then -1 else 1) := by
  sorry

/-
Exercise 2.9 | 7 | thm

Let f: ℝ² → ℝ be defined by f(x₁, x₂) = (x₁ + x₂²)². Let x = (1, 0), p = (-1, 1). Consider the line
search minimization. Find all α > 0 that minimize f(x + αp).
-/
