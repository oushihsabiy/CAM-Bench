theorem sum_posPart_le_cardinality_implies_feasible
    (P : CardinalityConstrainedConvexProgram) (x : Fin P.n → ℝ) (lam : ℝ)
    (h :
      ∑ i : Fin P.m, max (1 + lam * P.fi i x) 0 ≤ P.m - P.k)
    (hlam : 1 ≤ lam) :
    P.isFeasible x := by
  sorry
