theorem complex_pNormApproximation_p2_socp_qcqp_equiv
    (P : ComplexPNormApproximation)
    (hP : P.p = 2) :
    ∃ Q : ComplexPNormApproximationP2Model,
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
      (Q.socConstraint ↔
        Real.sqrt (Finset.univ.sum (fun i : Fin Q.m => (Q.r i) ^ 2 + (Q.s i) ^ 2)) ≤ Q.t) ∧
      (Q.qcqpConstraint ↔
        (Finset.univ.sum (fun i : Fin Q.m => (Q.r i) ^ 2 + (Q.s i) ^ 2)) ≤ Q.t ^ 2 ∧ 0 ≤ Q.t) ∧
      (∀ x : Fin Q.objectiveSource.n → ℂ,
        ∃ u : Fin Q.n → ℝ,
          ∃ v : Fin Q.n → ℝ,
            x = fun j : Fin Q.objectiveSource.n =>
              (u (Fin.cast Q.h_n j) : ℂ) + Complex.I * (v (Fin.cast Q.h_n j) : ℂ)) ∧
      (∀ u : Fin Q.n → ℝ,
        ∀ v : Fin Q.n → ℝ,
          ∃ x : Fin Q.objectiveSource.n → ℂ,
            x = fun j : Fin Q.objectiveSource.n =>
              (u (Fin.cast Q.h_n j) : ℂ) + Complex.I * (v (Fin.cast Q.h_n j) : ℂ)) ∧
      (Q.objectiveSource.objective
          (fun j : Fin Q.objectiveSource.n =>
            (Q.u (Fin.cast Q.h_n j) : ℂ) + Complex.I * (Q.v (Fin.cast Q.h_n j) : ℂ)) =
        Real.sqrt (Finset.univ.sum (fun i : Fin Q.m => (Q.r i) ^ 2 + (Q.s i) ^ 2))) := by
  refine ⟨{
    objectiveSource := P
    h_p := hP
  }, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    rfl
  · rfl
  · rfl
  · intro x
    refine ⟨fun j => Complex.re (x (cast (by rfl) j)), fun j => Complex.im (x (cast (by rfl) j)), ?_⟩
    funext j
    simp
  · intro u v
    refine ⟨fun j => (u (cast (by rfl) j) : ℂ) + Complex.I * (v (cast (by rfl) j) : ℂ), ?_⟩
    funext j
    simp
  · rfl

/-
Exercise 4.24 | 19 | thm

Let A = Aᵣ + iAᵢ ∈ ℂ^{m×n}, b = bᵣ + ibᵢ ∈ ℂ^m, and write the complex decision variable as x = u +
iv with u, v ∈ ℝ^n. Define

r = Aᵣu - Aᵢv - bᵣ ∈ ℝ^m,
s = Aᵣv + Aᵢu - bᵢ ∈ ℝ^m.

Then Ax - b = r + is, so for each i = 1, …, m,

|(Ax - b)ᵢ| = rᵢ² + sᵢ².

Prove that the complex optimization problem complex p-norm approximation is equivalent to the
following optimization problem with only real variables and real data: for p = ∞, it is equivalent
to the real SOCP real SOCP for p equals infinity. Here the correspondence between feasible points is
given by x = u + iv, and the objective value of the real problem is equal to ‖Ax - b‖ₚ.
-/