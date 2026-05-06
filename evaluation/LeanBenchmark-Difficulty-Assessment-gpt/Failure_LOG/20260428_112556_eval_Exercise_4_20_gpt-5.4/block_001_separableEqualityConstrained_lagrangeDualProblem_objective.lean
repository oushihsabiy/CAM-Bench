theorem separableEqualityConstrained_lagrangeDualProblem_objective
    (n p : ℕ)
    (A : Fin p → Fin n → ℝ)
    (b : Fin p → ℝ)
    (c : ℝ)
    (hc : 0 < c) :
    -- The Lagrange dual problem: maximize g(ν) over all ν ∈ ℝᵖ (unconstrained)
    -- where g(ν) = dual function of the primal = stated formula
    let phi : ℝ → ℝ := fun u => if |u| < c then |u| / (c - |u|) else 0
    let psi : ℝ → ℝ := fun t =>
      if |t| ≤ 1 / c then 0 else (Real.sqrt (c * |t|) - 1) ^ 2
    -- Build the dual problem using default objective = dualFunction
    let dualProb : LagrangeDualProblem := {
      n := n
      m := 0
      p := p
      f0 := fun x : Fin n → ℝ => ∑ i : Fin n, phi (x i)
      f := Fin.elim0
      h := fun j : Fin p => fun x : Fin n → ℝ => (∑ i : Fin n, A j i * x i) - b j
    }
    -- The dual objective equals the closed-form formula for all ν
    ∀ nu : Fin p → ℝ,
      dualProb.objective Fin.elim0 nu =
        -∑ j : Fin p, b j * nu j
          - ∑ i : Fin n, psi (∑ j : Fin p, A j i * nu j) := by
  sorry
