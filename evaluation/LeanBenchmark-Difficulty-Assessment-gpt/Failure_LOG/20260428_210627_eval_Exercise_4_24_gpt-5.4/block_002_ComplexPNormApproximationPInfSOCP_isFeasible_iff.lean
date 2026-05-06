theorem ComplexPNormApproximationPInfSOCP_isFeasible_iff
    (P : ComplexPNormApproximationPInfSOCP) :
    P.isFeasible ↔
      (∀ i : Fin P.m,
        P.r i =
          Complex.re
            (P.objectiveSource.residual
              (fun j => P.complexVector (Fin.cast P.h_n j))
              (Fin.cast P.h_m i))) ∧
      (∀ i : Fin P.m,
        P.s i =
          Complex.im
            (P.objectiveSource.residual
              (fun j => P.complexVector (Fin.cast P.h_n j))
              (Fin.cast P.h_m i))) ∧
      (∀ i : Fin P.m,
        Real.sqrt ((P.r i) ^ 2 + (P.s i) ^ 2) ≤ P.t) := by
  rfl

/-
Exercise 4.24 | 17 | thm

Let A = Aᵣ + iAᵢ ∈ ℂ^{m×n}, b = bᵣ + ibᵢ ∈ ℂ^m, and write the complex decision variable as x = u +
iv with u, v ∈ ℝ^n. Define

r = Aᵣu - Aᵢv - bᵣ ∈ ℝ^m,
s = Aᵣv + Aᵢu - bᵢ ∈ ℝ^m.

Then Ax - b = r + is, so for each i = 1, …, m,

|(Ax - b)ᵢ| = rᵢ^2 + sᵢ^2.

Prove that the complex optimization problem complex p-norm approximation is equivalent to the
following optimization problem with only real variables and real data: for p = 1, it is equivalent
to the real SOCP real SOCP for p equals one. Here the correspondence between feasible points is
given by x = u + iv, and the objective value of the real problem is equal to ‖Ax - b‖ₚ.
-/