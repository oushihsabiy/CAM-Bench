theorem critical_points_eq_for_quartic_bivariate
    (x : EuclideanSpace ℝ (Fin 2)) :
    (∇ (fun y : EuclideanSpace ℝ (Fin 2) =>
        2 * (y 0)^2 + (y 1)^2 - 2 * y 0 * y 1 + 2 * (y 0)^3 + (y 0)^4) x = 0) ↔
      x = (EuclideanSpace.single (0 : Fin 2) (0 : ℝ) +
            EuclideanSpace.single (1 : Fin 2) (0 : ℝ)) ∨
      x = (EuclideanSpace.single (0 : Fin 2) (-(1 : ℝ) / 2) +
            EuclideanSpace.single (1 : Fin 2) (-(1 : ℝ) / 2)) ∨
      x = (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ) +
            EuclideanSpace.single (1 : Fin 2) (-1 : ℝ)) := by
  sorry
