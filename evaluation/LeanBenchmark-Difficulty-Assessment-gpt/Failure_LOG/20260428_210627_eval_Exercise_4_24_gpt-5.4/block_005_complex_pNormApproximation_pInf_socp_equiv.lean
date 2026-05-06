theorem complex_pNormApproximation_pInf_socp_equiv
    (P : ComplexPNormApproximation)
    (hP : P.p ≥ 1) :
    ∃ Q : ComplexPNormApproximationPInfSOCP,
      Q.objectiveSource = P ∧
      (∀ i : Fin Q.m,
          Q.r i =
            Complex.re
              (Q.objectiveSource.residual
                (fun j : Fin Q.objectiveSource.n =>
                  (Q.u (Fin.cast Q.h_n j) : ℂ) +
                    Complex.I * (Q.v (Fin.cast Q.h_n j) : ℂ))
                (Fin.cast Q.h_m i))) ∧
      (∀ i : Fin Q.m,
          Q.s i =
            Complex.im
              (Q.objectiveSource.residual
                (fun j : Fin Q.objectiveSource.n =>
                  (Q.u (Fin.cast Q.h_n j) : ℂ) +
                    Complex.I * (Q.v (Fin.cast Q.h_n j) : ℂ))
                (Fin.cast Q.h_m i))) ∧
      (∀ i : Fin Q.m,
          Real.sqrt ((Q.r i) ^ 2 + (Q.s i) ^ 2) ≤ Q.t) ∧
      (Q.objectiveSource.objective
          (fun j : Fin Q.objectiveSource.n =>
            (Q.u (Fin.cast Q.h_n j) : ℂ) + Complex.I * (Q.v (Fin.cast Q.h_n j) : ℂ)) =
        Q.objective) ∧
      (∀ x : Fin Q.objectiveSource.n → ℂ,
        ∃ u : Fin Q.n → ℝ,
          ∃ v : Fin Q.n → ℝ,
            x = fun j : Fin Q.objectiveSource.n =>
              (u (Fin.cast Q.h_n j) : ℂ) + Complex.I * (v (Fin.cast Q.h_n j) : ℂ)) ∧
      (∀ u : Fin Q.n → ℝ,
        ∀ v : Fin Q.n → ℝ,
          ∃ x : Fin Q.objectiveSource.n → ℂ,
            x = fun j : Fin Q.objectiveSource.n =>
              (u (Fin.cast Q.h_n j) : ℂ) + Complex.I * (v (Fin.cast Q.h_n j) : ℂ)) := by
  simpa using P.toPInfSOCP_equiv hP