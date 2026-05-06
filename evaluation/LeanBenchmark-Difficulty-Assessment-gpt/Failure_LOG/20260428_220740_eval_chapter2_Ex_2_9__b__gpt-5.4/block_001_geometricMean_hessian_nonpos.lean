theorem geometricMean_hessian_nonpos (n : ℕ) (hn : 0 < n) :
    ∀ x : Fin n → ℝ,
      (∀ k, 0 < x k) →
      Matrix.PosSemidef
        (-fun i j =>
          (fderiv ℝ
            (fun y : Fin n → ℝ =>
              (fderiv ℝ
                (fun z : Fin n → ℝ => Real.rpow (∏ k, z k) (1 / (n : ℝ))) y)
                (Pi.single j (1 : ℝ))) x)
            (Pi.single i (1 : ℝ))) := by
  sorry

/- [BLOCK chapter2 Ex.2.9-(b) | 17 | thm]
Let n ∈ ℕ, and define ℝ_{++}^n={x=(x₁,dots,xₙ)∈ ℝ^n:\ xₖ>0,\ k=1,dots,n}. Given the function
f:ℝ_{++}^n o ℝ, f(x)=≤ft(prod_{k=1}^n xₖ
ight)^{1/n}. Prove that f is a concave function on ℝ_{++}^n.
-/
