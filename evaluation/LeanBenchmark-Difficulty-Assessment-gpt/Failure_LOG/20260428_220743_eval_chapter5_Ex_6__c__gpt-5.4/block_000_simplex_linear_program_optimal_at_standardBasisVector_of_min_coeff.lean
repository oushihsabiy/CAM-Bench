theorem simplex_linear_program_optimal_at_standardBasisVector_of_min_coeff
    {n : ℕ} [NeZero n] (P : SimplexLinearProgram n) :
    ∃ i : Fin n,
      IsMinOn P.objective (P.feasibleSet) (SimplexLinearProgram.standardBasisVector i) ∧
      P.objective (SimplexLinearProgram.standardBasisVector i) = iInf fun j : Fin n => P.c j := by
  sorry
