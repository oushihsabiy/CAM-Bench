import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators


namespace «problem-61»
/-
[BLOCK Exercise 9.9 | 24 | defn] Let f: ℝⁿ → ℝ be twice differentiable at x, and suppose the Hessian
∇²f(x) is invertible. The Newton decrement at x is defined by λ(x) = (∇f(x)ᵀ(∇²f(x))⁻¹∇f(x))^{1/2}.
-/
open scoped Matrix
local notation "newtonDecrementHessian" =>
  fun {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) =>
    Matrix.of fun i j : Fin n =>
      (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x) (Pi.single i (1 : ℝ))

def newtonDecrement {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (_h_twice : ContDiffAt ℝ 2 f x)
    [Invertible (newtonDecrementHessian f x)] : ℝ :=
  let grad : Fin n → ℝ := fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))
  let hess : Matrix (Fin n) (Fin n) ℝ := newtonDecrementHessian f x
  Real.sqrt (dotProduct grad (⅟ hess *ᵥ grad))

/-
Let f: ℝ^n → ℝ be twice differentiable at x ∈ ℝ^n, and assume that ∇^2 f(x) is positive definite.
Define the Newton decrement at x by λ(x) = (∇ f(x)ᵀ(∇^2 f(x)^{- 1}∇ f(x))^{1/2}. Show that λ(x) =
sup_{vᵀ∇^2 f(x)v = 1}(- vᵀ∇ f(x)) = sup_{vne 0} - vᵀ∇ f(x){(vᵀ∇^2 f(x)v)^{1/2}}. 9. 20
-/
theorem newtonDecrement_eq_sup_normalized_and_rayleigh_quotient
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hn : 0 < n)
    (h_twice : ContDiffAt ℝ 2 f x)
    [Invertible (newtonDecrementHessian f x)]
    (hpd : Matrix.PosDef (newtonDecrementHessian f x)) :
    let grad : Fin n → ℝ := fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))
    let hess : Matrix (Fin n) (Fin n) ℝ := newtonDecrementHessian f x
    newtonDecrement f x h_twice =
      sSup {r : ℝ | ∃ v : Fin n → ℝ, dotProduct v (hess *ᵥ v) = 1 ∧ r = -dotProduct v grad} ∧
    sSup {r : ℝ | ∃ v : Fin n → ℝ, dotProduct v (hess *ᵥ v) = 1 ∧ r = -dotProduct v grad} =
      sSup
        {r : ℝ |
          ∃ v : Fin n → ℝ,
            v ≠ 0 ∧
            r = (-dotProduct v grad) / Real.sqrt (dotProduct v (hess *ᵥ v))} := by
  sorry

end «problem-61»
