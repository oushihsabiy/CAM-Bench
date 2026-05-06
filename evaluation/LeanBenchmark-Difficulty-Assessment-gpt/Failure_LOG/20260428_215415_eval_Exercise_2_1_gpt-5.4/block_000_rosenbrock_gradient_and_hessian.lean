theorem rosenbrock_gradient_and_hessian
    (x : EuclideanSpace ℝ (Fin 2)) :
    gradient (fun y : EuclideanSpace ℝ (Fin 2) => 100 * (y 1 - (y 0)^2)^2 + (1 - y 0)^2) x =
      (EuclideanSpace.single 0 (-400 * x 0 * (x 1 - (x 0)^2) + 2 * x 0 - 2) +
        EuclideanSpace.single 1 (200 * (x 1 - (x 0)^2))) ∧
    hessian (fun y : EuclideanSpace ℝ (Fin 2) => 100 * (y 1 - (y 0)^2)^2 + (1 - y 0)^2) x =
      !![1200 * (x 0)^2 - 400 * x 1 + 2, -400 * x 0;
        -400 * x 0, 200] := by
  sorry

/-
Exercise 2.1 | 5 | thm

Let f : ℝ² → ℝ be defined by
f(x₁, x₂) = 100(x₂ - x₁²)² + (1 - x₁)².

Prove that x* = (1, 1)ᵀ is the unique local minimizer of f, and that
∇²f(1, 1) = (802  -400; -400  200)
is positive definite.
-/
