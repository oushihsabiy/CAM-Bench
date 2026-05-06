theorem reduced_solution_does_not_determine_original_solution
    (q : ReducedUnconstrainedProblem)
    (hq : ∀ r : ReducedUnconstrainedProblem,
      q.objective ≤ r.objective) :
    ¬ ∃ p : QuadraticEqualityConstrainedProblem, p.y = q.y := by
  intro h
  rcases h with ⟨p, hp⟩
  have hconstraint : (p.x - 1) ^ 2 = 5 * q.y := by
    simpa [hp] using p.constraint
  have hy_nonneg : 0 ≤ q.y := by
    nlinarith
  let r : ReducedUnconstrainedProblem :=
    { y := -1
      objective := 4
      objective_eq := by ring }
  have hle : q.objective ≤ r.objective := hq r
  have hqobj : q.objective = 5 * q.y + (q.y - 2) ^ 2 := q.objective_eq
  have hge : 4 ≤ q.objective := by
    rw [hqobj]
    nlinarith [hy_nonneg]
  have hre : r.objective = 4 := rfl
  rw [hre] at hle
  have hqeq : q.objective = 4 := by linarith
  rw [hqobj] at hqeq
  have hy_zero : q.y = 0 := by
    nlinarith [hy_nonneg, hqeq]
  have hqobj0 : q.objective = 4 := by
    rw [hqobj, hy_zero]
    ring
  have r0 : ReducedUnconstrainedProblem :=
    { y := 0
      objective := 4
      objective_eq := by ring }
  have hle0 : q.objective ≤ r0.objective := hq r0
  rw [hqobj0] at hle0
  have hp0 : p.y = 0 := by simpa [hy_zero] using hp
  have hconstraint0 : (p.x - 1) ^ 2 = 0 := by
    simpa [hp0] using p.constraint
  have hx1 : p.x = 1 := by
    nlinarith
  have r1 : ReducedUnconstrainedProblem :=
    { y := 1
      objective := 2
      objective_eq := by ring }
  have hle1 : q.objective ≤ r1.objective := hq r1
  rw [hqobj0] at hle1
  linarith