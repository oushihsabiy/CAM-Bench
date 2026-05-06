theorem hessian_log_sum_exp_posSemidef
    (n : ℕ)
    (x v : Fin n → ℝ) :
    0 ≤
      ∑ i : Fin n, ∑ j : Fin n,
        v i *
          ((fderiv ℝ
            (fun y : Fin n → ℝ =>
              (fderiv ℝ
                (fun z : Fin n → ℝ => Real.log (∑ k : Fin n, Real.exp (z k))) y)
                (Pi.single j (1 : ℝ))) x)
            (Pi.single i (1 : ℝ))) * v j := by
  sorry

/- [BLOCK chapter2 Ex.2.9-(a) | 14 | thm]
Let the function f:ℝ^n → ℝ be defined by f(x)=ln≤ft(sum_{k=1}^n e^{xₖ}), x=(x₁,dots,xₙ)^→p ∈ ℝ^n.
Deduce that f is convex on ℝ^n.
-/
