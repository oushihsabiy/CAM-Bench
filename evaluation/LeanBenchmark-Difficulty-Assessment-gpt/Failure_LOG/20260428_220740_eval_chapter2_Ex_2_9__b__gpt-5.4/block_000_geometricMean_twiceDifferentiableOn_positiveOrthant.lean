theorem geometricMean_twiceDifferentiableOn_positiveOrthant (n : ℕ) (hn : 0 < n) :
    ContDiffOn ℝ 2
      (fun x : Fin n → ℝ => Real.rpow (∏ k, x k) (1 / (n : ℝ)))
      {x : Fin n → ℝ | ∀ k, 0 < x k} := by
  sorry

/- [BLOCK chapter2 Ex.2.9-(b) | 16 | thm]
Let n ∈ ℕ, and define ℝ_{++}^n={x=(x₁,dots,xₙ)∈ ℝ^n:\ xₖ>0,\ k=1,dots,n}. Given the function
f:ℝ_{++}^n o ℝ, f(x)=≤ft(prod_{k=1}^n xₖ
ight)^{1/n}. Prove that for any x ∈ ℝ_{++}^n, the Hessian matrix abla^2 f(x) is negative
semidefinite.
-/
