theorem nonlinearProgramP_dual_function_eq_zero_of_nonneg (lam : ℝ) (h_lam : 0 ≤ lam) :
    let L : (ℝ × ℝ) → ℝ :=
      fun p => Real.exp p.1 + Real.exp p.2 + lam * (p.1 ^ 2 / p.2)
    let g : ℝ :=
      sInf (Set.range (fun p : {p : ℝ × ℝ // p.2 ≠ 0} => L p.1))
    g = 0 := by
  sorry

/- [BLOCK chapter5 Ex.17-(c) | 40 | thm]
Consider the nonlinear program (P). Denote the optimal value of the primal problem by p*. Introduce
a Lagrange multiplier λ ≥ 0 for the constraint
rac{x^2}{y} ≤ 0, and define the Lagrangian function L(x,y,λ)=e^x+e^y+λ
rac{x^2}{y}, λ ≥ 0, where it is still required that y
e 0. Define the Lagrangian dual function g(λ)=∈f_{x ∈ ℝ, y ∈ ℝ, y
e 0} L(x,y,λ), λ ≥ 0, and denote the dual optimal value by d*=sup_{λ ≥ 0} g(λ). Hence determine the
dual optimal value d* and the duality gap p*-d*, and prove that d*=0, p*-d*=1.
-/
