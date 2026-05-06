theorem quadraticEqualityConstrainedProblem_kkt_points_exactly :
    let P := QuadraticEqualityConstrainedProblem.standard
    let f := P.objective
    let g : Unit → (ℝ × ℝ) → ℝ := fun _ => P.constraint
    let gradL : (ℝ × ℝ) → (Unit → ℝ) → (ℝ × ℝ) → ℝ := fun p lam z =>
      (2 * (p.1 - 1) + 2 * lam () * (p.1 - 1)) * z.1 +
        (2 * (p.2 - 2) - 5 * lam ()) * z.2
    ({p : ℝ × ℝ | IsKKTPoint f g gradL p} =
      ({(1, 0), (1 + Real.sqrt 15, 3), (1 - Real.sqrt 15, 3)} : Set (ℝ × ℝ))) ∧
    ({q : (ℝ × ℝ) × (Unit → ℝ) |
        (∀ i, g i q.1 = 0) ∧ gradL q.1 q.2 = 0} =
      ({((1, 0), fun _ => -(4 : ℝ) / 5),
        ((1 + Real.sqrt 15, 3), fun _ => -(1 : ℝ) / 2),
        ((1 - Real.sqrt 15, 3), fun _ => -(1 : ℝ) / 2)} :
        Set ((ℝ × ℝ) × (Unit → ℝ)))) := by
  sorry

/- [BLOCK Exercise 12.18-(a) | 38 | thm]
Consider the quadratic equality-constrained problem. Define f(x,y)=(x-1)^2+(y-2)^2,
g(x,y)=(x-1)^2-5y, and the Lagrangian L(x,y,λ)=f(x,y)+λ g(x,y). Also prove that the linear
independence constraint qualification is satisfied at every feasible point, i.e., ∇ g(x,y)neq 0 for
all (x,y)∈ℝ^2 such that g(x,y)=0.
-/
