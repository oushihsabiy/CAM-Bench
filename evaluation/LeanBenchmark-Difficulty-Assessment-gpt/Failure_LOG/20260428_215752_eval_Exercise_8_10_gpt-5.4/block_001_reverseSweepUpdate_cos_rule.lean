theorem reverseSweepUpdate_cos_rule
    (adjoint : Fin 1 → ℝ) (xkAdjoint xi : ℝ) :
    reverseSweepUpdate adjoint xkAdjoint
      (fun _ => -Real.sin xi) 0
      = adjoint 0 + xkAdjoint * (-(Real.sin xi))
    ∧ ((1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ)) = (1, 1, 1, 1) := by
  sorry

/- [BLOCK Exercise 8.10 | 19 | defn]
For a scalar-valued function f computed from intermediate variables x₁,dots,x_N, the reverse-mode
adjoint of an intermediate variable x_ell is x_ell := (∂ f)/(∂ x_ell).
-/
