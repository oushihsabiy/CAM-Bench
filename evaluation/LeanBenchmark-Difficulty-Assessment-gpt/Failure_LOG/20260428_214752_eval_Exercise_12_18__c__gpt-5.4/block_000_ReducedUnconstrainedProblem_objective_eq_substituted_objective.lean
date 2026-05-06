theorem ReducedUnconstrainedProblem_objective_eq_substituted_objective
    (q : ReducedUnconstrainedProblem) :
    q.objective = 5 * q.y + (q.y - 2) ^ 2 := by
  exact q.objective_eq

/- [BLOCK Exercise 12.18-(c) | 51 | thm]
Consider the quadratic equality-constrained problem
min_{x,y∈ℝ} (x-1)^2+(y-2)^2
subject to (x-1)^2=5y.
Using the constraint (x-1)^2=5y, directly substitute into the objective to obtain the reduced
unconstrained problem
min_{y∈ℝ} 5y+(y-2)^2.
Show that a solution of this reduced unconstrained problem does not itself give a solution of the
original constrained problem.
-/