theorem equivalentBarrierOptimizationProblem_has_same_feasible_points_and_optimal_solutions
    (m n : ℕ) (hm : 0 < m)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    (let phi : (Fin m → ℝ) → ℝ :=
      fun y => -((1 : ℝ) / (2 * (m : ℝ))) *
        ∑ i : Fin m, Real.log ((1 - y i) * (1 + y i))
     let p : EquivalentBarrierOptimizationProblem := {
       m := m
       n := n
       hm := hm
       A := A
       b := b
       phi := phi
     }
     p.equivalentProblems) := by
  sorry
