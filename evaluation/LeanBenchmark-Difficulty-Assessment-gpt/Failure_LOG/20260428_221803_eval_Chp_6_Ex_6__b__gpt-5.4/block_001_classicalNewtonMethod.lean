def classicalNewtonMethod {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (_k : ℕ)
    (xk : EuclideanSpace ℝ (Fin n))
    (_hf : ContDiff ℝ 2 f := by sorry)
    (hInv : Function.Bijective ((fderiv ℝ (gradient f) xk).toLinearMap) := by sorry) :
    EuclideanSpace ℝ (Fin n) := by
  sorry

instance {α : Type*} [TopologicalSpace α] [Inhabited α] : TopologicalSpace (Option α) :=
  TopologicalSpace.induced (fun o : Option α => o.getD default) inferInstance

/- [BLOCK Chp.6 Ex.6-(b) | 14 | algo]
The classical Newton method is defined as follows: at each step k, if ∇^2 f(xₖ) is invertible, then
x_{k+1} = xₖ - ≤ft(∇^2 f(xₖ))^{-1}∇ f(xₖ).
-/
structure ClassicalNewtonMethod {n : ℕ} where
  f : EuclideanSpace ℝ (Fin n) → ℝ
  hf : ContDiff ℝ 2 f
  x : ℕ → EuclideanSpace ℝ (Fin n)
  step :
    ∀ k : ℕ,
      ∀ hbij : Function.Bijective ((fderiv ℝ (gradient f) (x k)).toLinearMap),
      x (k + 1) =
        x k -
          (LinearEquiv.ofBijective
            ((fderiv ℝ (gradient f) (x k)).toLinearMap) hbij) (gradient f (x k))

