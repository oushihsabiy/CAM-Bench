import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-41»
/-
For a function f: ℝ^n → ℝ cup {+ ∞}, its convex conjugate f*: ℝ^n → ℝ cup {+ ∞} is defined by f*(y)
=
sup_{z ∈ ℝ^n} (yᵀ z - f(z)).
-/
open scoped BigOperators

def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup (Set.range fun z : Fin n → ℝ => (∑ i, y i * z i : ℝ) - f z)

/-
Let f: ℝ^n → ℝ be a convex C^2 function, and let f*: ℝ^n → ℝ + ∞ be its convex conjugate defined by
f*(y) = sup_{z∈ℝ^n}(yᵀz - f(z)). Assume that x, y∈ℝ^n satisfy y = ∇ f(x) and that ∇^2 f(x)succ 0.
Show
that f* is twice differentiable at y and that ∇^2 f*(y) = (∇^2 f(x))^{- 1}.
-/
theorem hessian_convexConjugate_eq_inverse_hessian_at_gradient
    {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (fStar : (Fin n → ℝ) → ℝ)
    (x y : Fin n → ℝ)
    (hy :
      y = fun i =>
        (fderiv ℝ f x) (Pi.single i (1 : ℝ)))
    (hconv : ConvexOn ℝ Set.univ f)
    (hC2 : ContDiffAt ℝ 2 f x)
    (hstar : ∀ z, convexConjugate (fun w => (f w : EReal)) z = (fStar z : EReal))
    (hpos :
      let hessf : Matrix (Fin n) (Fin n) ℝ :=
        fun i j =>
          (fderiv ℝ
            (fun x' => (fderiv ℝ f x') (Pi.single j (1 : ℝ))) x)
            (Pi.single i (1 : ℝ))
      hessf.PosDef) :
    let hessf : Matrix (Fin n) (Fin n) ℝ :=
      fun i j =>
        (fderiv ℝ
          (fun x' => (fderiv ℝ f x') (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ))
    let hessfstar : Matrix (Fin n) (Fin n) ℝ :=
      fun i j =>
        (fderiv ℝ
          (fun y' =>
            (fderiv ℝ fStar y')
              (Pi.single j (1 : ℝ))) y)
          (Pi.single i (1 : ℝ))
    ContDiffAt ℝ 2 fStar y ∧ hessfstar = hessf⁻¹ := by
  sorry

end «problem-41»