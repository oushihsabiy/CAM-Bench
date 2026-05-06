import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-129»
/-
Let D ⊆ ℝ^n be a convex set, and let g: D → ℝ be twice continuously differentiable. Define f: D → ℝ
by f(x) = - exp(- g(x)) (x ∈ D). Assume that for every x ∈ D, [ ∇^2 g(x) & ∇ g(x); ∇ g(x)ᵀ & 1 ]
succeq 0. Prove that f is convex on D.
-/
open scoped RealInnerProductSpace

theorem neg_exp_neg_convexOn_of_posSemidef_hessian_block
    {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hD : Convex ℝ D)
    (hD_open : IsOpen D)
    (hg : ContDiffOn ℝ 2 g D)
    (hblock :
      ∀ x ∈ D, ∀ v : (EuclideanSpace ℝ (Fin n)) × ℝ,
        0 ≤
          let xv : EuclideanSpace ℝ (Fin n) := v.1
          let t : ℝ := v.2
          ⟪fderiv ℝ (fun y => gradient g y) x xv, xv⟫ +
            2 * t * ⟪gradient g x, xv⟫ + t ^ 2)
    :
    ConvexOn ℝ D
      (fun x => -Real.exp (-(g x))) := by
  sorry

end «problem-129»
