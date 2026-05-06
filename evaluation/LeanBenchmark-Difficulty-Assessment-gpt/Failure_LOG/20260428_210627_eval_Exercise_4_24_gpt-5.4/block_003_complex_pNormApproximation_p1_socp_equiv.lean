theorem complex_pNormApproximation_p1_socp_equiv
    (P : ComplexPNormApproximation)
    (hP : P.p = 1) :
    ∃ Q : ComplexPNormApproximationP1SOCP,
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
          Real.sqrt ((Q.r i) ^ 2 + (Q.s i) ^ 2) ≤ Q.t i) ∧
      (Q.objectiveSource.objective
          (fun j : Fin Q.objectiveSource.n =>
            (Q.u (Fin.cast Q.h_n j) : ℂ) + Complex.I * (Q.v (Fin.cast Q.h_n j) : ℂ)) =
        ∑ i : Fin Q.m, Real.sqrt ((Q.r i) ^ 2 + (Q.s i) ^ 2)) ∧
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
  classical
  refine ⟨P.toP1SOCP, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa using P.toP1SOCP_residual_real i
  · intro i
    simpa using P.toP1SOCP_residual_imag i
  · intro i
    simpa using P.toP1SOCP_coneConstraint i
  · simpa [hP] using P.toP1SOCP_objective
  · intro x
    refine ⟨fun j => Complex.re (x j), fun j => Complex.im (x j), ?_⟩
    funext j
    simpa using (Complex.re_add_im (x j)).symm
  · intro u v
    refine ⟨fun j : Fin P.n => (u j : ℂ) + Complex.I * (v j : ℂ), ?_⟩
    rfl

/-
Exercise 4.24 | 18 | thm

Let A = Aᵣ + iAᵢ ∈ ℂ^{m×n}, b = bᵣ + ibᵢ ∈ ℂ^m, and write the complex decision variable as x = u +
iv with u, v ∈ ℝ^n. Define

r = Aᵣu - Aᵢv - bᵣ ∈ ℝ^m,

s = Aᵣv + Aᵢu - bᵢ ∈ ℝ^m.

Then Ax - b = r + is, so for each i = 1, …, m,

|(Ax - b)ᵢ| = rᵢ² + sᵢ².

Prove that the complex optimization problem complex p-norm approximation is equivalent to the
following optimization problem with only real variables and real data: for p = 2, it is equivalent
to the real SOCP and QCQP for p = 2. Here the correspondence between feasible points is given by x =
u + iv, and the objective value of the real problem is equal to ‖Ax - b‖ₚ.
-/