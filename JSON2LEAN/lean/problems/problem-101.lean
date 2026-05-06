import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-101»
/-
Let D subseteq ℝ^n be a convex set, and let g: D → ℝ be twice continuously differentiable. Define f:
D → ℝ by f(x) = - exp(- g(x)). Assume that for every x in D, the block matrix [[nabla^2 g(x), nabla
g(x)], [nabla g(x)ᵀ, 1]] is positive semidefinite. Prove that f is convex on D.
-/
open scoped RealInnerProductSpace

theorem convexOn_neg_exp_neg_of_hessian_gradient_block_pos
    {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hess : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hD : Convex ℝ D)
    (hg : ContDiffOn ℝ 2 g D)
    (hgrad : ∀ x ∈ D, HasGradientAt g (G x) x)
    (hhess : ∀ x ∈ D, HasFDerivAt G (hess x) x)
    (hblock :
      ∀ x ∈ D, ∀ (u : EuclideanSpace ℝ (Fin n)) (s : ℝ),
        0 ≤ ⟪hess x u, u⟫ + 2 * s * ⟪G x, u⟫ + s ^ 2) :
    ConvexOn ℝ D (fun x => -Real.exp (-g x)) := by
  sorry

end «problem-101»