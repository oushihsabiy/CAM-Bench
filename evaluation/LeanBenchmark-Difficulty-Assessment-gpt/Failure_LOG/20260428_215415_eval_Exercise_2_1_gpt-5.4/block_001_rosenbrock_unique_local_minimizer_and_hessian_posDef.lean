theorem rosenbrock_unique_local_minimizer_and_hessian_posDef :
    let f : EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun y => 100 * (y 1 - (y 0)^2)^2 + (1 - y 0)^2
    let xstar : EuclideanSpace ℝ (Fin 2) :=
      EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ)
    IsLocalMinimizer f xstar ∧
      (∀ x : EuclideanSpace ℝ (Fin 2), IsLocalMinimizer f x → x = xstar) ∧
      hessian f xstar = !![802, -400; -400, 200] ∧
      Matrix.PosDef (hessian f xstar) := by
  sorry
