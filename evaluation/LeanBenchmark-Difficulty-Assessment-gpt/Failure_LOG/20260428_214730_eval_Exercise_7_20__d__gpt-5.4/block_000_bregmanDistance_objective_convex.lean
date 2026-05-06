theorem bregmanDistance_objective_convex
    (P : BregmanDistanceMinimization)
    (h_diff : DifferentiableAt ℝ P.f P.y)
    (h_strict : StrictConvexOn ℝ (Set.univ : Set (Fin P.n → ℝ)) P.f) :
    ConvexOn ℝ (Set.univ : Set (Fin P.n → ℝ)) P.objective := by
  simpa [BregmanDistanceMinimization.objective] using h_strict.convexOn

/- [BLOCK Exercise 7.20-(d) | 17 | thm]
Let n ∈ ℕ, let f:ℝ^n → ℝ be strictly convex and differentiable, let y ∈ ℝ^n be fixed, and define
D_f(x,y)=f(x)-f(y)-∇ f(y)ᵀ(x-y).
Let C ⊆ ℝ^n be convex. Hence determine that Bregman distance minimization is a convex optimization
problem.
-/