theorem MorrisonMethod_nextM_le_optimal_of_current_le_optimal
    (mm : MorrisonMethod)
    (k : ℕ)
    (xStar : Fin mm.problem.n → ℝ)
    (hxStar_feasible : mm.problem.isFeasible xStar)
    (hxStar_optimal : ∀ x : Fin mm.problem.n → ℝ,
      mm.problem.isFeasible x → mm.problem.f xStar ≤ mm.problem.f x)
    (hv : ∀ M : ℝ, ∀ x : Fin mm.problem.n → ℝ,
      mm.v M x =
        (mm.problem.f x - M) ^ 2 +
          ∑' i, by
            classical
            exact if i ∈ mm.problem.eq_constraints then (mm.problem.c i x) ^ 2 else 0)
    (hMlb : IsLowerBoundEstimate (mm.problem.f xStar) (mm.M k)) :
    mm.nextM k ≤ mm.problem.f xStar := by
  sorry
