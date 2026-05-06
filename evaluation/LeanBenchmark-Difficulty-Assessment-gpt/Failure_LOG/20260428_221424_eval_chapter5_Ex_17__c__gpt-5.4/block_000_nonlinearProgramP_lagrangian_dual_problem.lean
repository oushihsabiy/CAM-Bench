theorem nonlinearProgramP_lagrangian_dual_problem :
    lagrangianDualProblem
        (fun p : {p : ℝ × ℝ // p.2 ≠ 0} =>
          fun lam : NNReal =>
            lagrangianWithIneqMultiplier
              (fun q : ℝ × ℝ => Real.exp q.1 + Real.exp q.2)
              (fun q : ℝ × ℝ => q.1 ^ 2 / q.2)
              p.1 lam)
      =
    sSup
      (Set.range (fun lam : NNReal =>
        sInf
          (Set.range (fun p : {p : ℝ × ℝ // p.2 ≠ 0} =>
            Real.exp p.1.1 + Real.exp p.1.2 + (lam : ℝ) * (p.1.1 ^ 2 / p.1.2))))) := by
  sorry

/- [BLOCK chapter5 Ex.17-(c) | 39 | thm]
Consider the nonlinear program (P). Denote the optimal value of the primal problem by p*. Introduce
a Lagrange multiplier λ ≥ 0 for the constraint
rac{x^2}{y} ≤ 0, and define the Lagrangian function L(x,y,λ)=e^x+e^y+λ
rac{x^2}{y}, λ ≥ 0, where it is still required that y
e 0. Define the Lagrangian dual function g(λ)=∈f_{x ∈ ℝ, y ∈ ℝ, y
e 0} L(x,y,λ), λ ≥ 0, and denote the dual optimal value by d*=sup_{λ ≥ 0} g(λ). Prove that for every
λ ≥ 0, g(λ)=0.
-/
