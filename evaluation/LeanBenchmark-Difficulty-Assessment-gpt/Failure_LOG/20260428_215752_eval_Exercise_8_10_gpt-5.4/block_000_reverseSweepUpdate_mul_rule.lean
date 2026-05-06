theorem reverseSweepUpdate_mul_rule
    (xbar_i xbar_j xbar_k xi xj : ℝ) :
    reverseSweepUpdate (fun b : Bool => if b then xbar_i else xbar_j) xbar_k
        (fun b : Bool => if b then xj else xi) true
        = xbar_i + xbar_k * xj
    ∧ reverseSweepUpdate (fun b : Bool => if b then xbar_i else xbar_j) xbar_k
        (fun b : Bool => if b then xj else xi) false
        = xbar_j + xbar_k * xi
    ∧ ((2 : ℕ), (2 : ℕ), (1 : ℕ)) = (2, 2, 1) := by
  sorry

/- [BLOCK Exercise 8.10 | 28 | thm]
Let f be a real-valued function computed by a forward sweep through elementary operations, and for
each intermediate variable x_{ell} let x_{ell} := ∂ f{∂ x_{ell}} be its reverse-mode adjoint. In the
reverse sweep, if an elementary forward operation computes xₖ from previously computed variables,
then for each argument xᵢ on which xₖ depends, the adjoint is updated by xᵢ += xₖ (∂ xₖ)/(∂ xᵢ).
Assume xᵢ,xⱼ,xₖ ∈ ℝ. Prove that for the forward operation xₖ ≤ftarrow cos(xᵢ), the reverse sweep
update is xᵢ += -xₖ sin(xᵢ), and that the reverse sweep requires one evaluation of sin, one
multiplication, and one addition, whereas the forward sweep requires one evaluation of cos.
-/
