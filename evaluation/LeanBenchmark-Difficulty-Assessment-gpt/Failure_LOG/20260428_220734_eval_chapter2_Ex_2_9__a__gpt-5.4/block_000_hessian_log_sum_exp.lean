theorem hessian_log_sum_exp
    (n : ℕ)
    (x : Fin n → ℝ) :
    ∀ i j : Fin n,
      (fderiv ℝ
        (fun y : Fin n → ℝ =>
          (fderiv ℝ
            (fun z : Fin n → ℝ => Real.log (∑ k : Fin n, Real.exp (z k))) y)
            (Pi.single j (1 : ℝ))) x)
        (Pi.single i (1 : ℝ))
      =
      (Real.exp (x i) / (∑ k : Fin n, Real.exp (x k))) *
        ((if i = j then (1 : ℝ) else 0) -
          Real.exp (x j) / (∑ k : Fin n, Real.exp (x k))) := by
  sorry

/- [BLOCK chapter2 Ex.2.9-(a) | 13 | thm]
Let the function f:ℝ^n → ℝ be defined by f(x)=ln≤ft(sum_{k=1}^n e^{xₖ}), x=(x₁,dots,xₙ)^→p ∈ ℝ^n.
Prove that for any x∈ ℝ^n, the matrix abla^2 f(x) is positive semidefinite.
-/
