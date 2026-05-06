theorem reverseSweep_mul_operation_rule
    (adjoint : Fin 2 → ℝ) (xkAdjoint xi xj : ℝ) :
    (reverseSweepUpdate adjoint xkAdjoint
      (fun t =>
        if h : t = 0 then xj
        else if t = 1 then xi else 0) 0
      = adjoint 0 + xkAdjoint * xj
    ∧
    reverseSweepUpdate adjoint xkAdjoint
      (fun t =>
        if h : t = 0 then xj
        else if t = 1 then xi else 0) 1
      = adjoint 1 + xkAdjoint * xi) ∧
    ((2 : ℕ) = 2 ∧ (2 : ℕ) = 2 ∧ (1 : ℕ) = 1) := by
  sorry

/- [BLOCK Exercise 8.10 | 23 | thm]
Let f be a real-valued function computed by a forward sweep through elementary operations, and for
each intermediate variable x_{ell} let x_{ell} := ∂ f{∂ x_{ell}} be its reverse-mode adjoint. In the
reverse sweep, if an elementary forward operation computes xₖ from previously computed variables,
then for each argument xᵢ on which xₖ depends, the adjoint is updated by xᵢ += xₖ (∂ xₖ)/(∂ xᵢ).
Assume xᵢ,xⱼ,xₖ ∈ ℝ. Prove that for the forward operation xₖ ≤ftarrow cos(xᵢ), the reverse sweep
update is xᵢ += -xₖ sin(xᵢ), and that the reverse sweep requires one evaluation of sin, one
multiplication, and one addition, whereas the forward sweep requires one evaluation of cos.
-/
