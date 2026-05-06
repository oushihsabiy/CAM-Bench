theorem unconstrainedQuadraticProgram_has_optimal_solution_iff
    {n : Type*} [Fintype n] [DecidableEq n] (p : UnconstrainedQuadraticProgram n) :
    (((∃ x : n → ℝ, p.isMinimizer x) ↔
      ((∀ x : n → ℝ, 0 ≤ dotProduct x (p.A.mulVec x)) ∧
        (∀ z : n → ℝ, p.A.mulVec z = 0 → dotProduct p.b z = 0))) ∧
    (((∀ x : n → ℝ, 0 ≤ dotProduct x (p.A.mulVec x)) ∧
        (∀ z : n → ℝ, p.A.mulVec z = 0 → dotProduct p.b z = 0)) →
      ∀ Adag : Matrix n n ℝ, IsMoorePenrosePseudoinverse p.A Adag →
        ({x : n → ℝ | p.isMinimizer x} =
          {x : n → ℝ | p.A.mulVec x = fun i => -p.b i}) ∧
        ({x : n → ℝ | p.isMinimizer x} =
          {x : n → ℝ | ∃ z : n → ℝ,
              x = fun i => -(Adag.mulVec p.b) i + (z i - (Adag.mulVec (p.A.mulVec z)) i)}) ∧
        (∀ x : n → ℝ, p.isMinimizer x →
          p.objective x = -dotProduct p.b (Adag.mulVec p.b)))) := by
  sorry
