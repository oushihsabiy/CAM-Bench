import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-44»
/-
Let f: ℝ^n → ℝ be a twice continuously differentiable convex function. Assume that ∇^2 f(x) succ 0
for every x ∈ ℝ^n. For x ∈ ℝ^n, define λ(x)^2 = ∇ f(x)ᵀbig(∇^2 f(x)big)^{- 1}∇ f(x). Suppose there
exists a constant c > 0 such that λ(x)^2 ≤ c for all x ∈ ℝ^n. Show that the function g(x) =
exp(- (f(x))/(c)) is concave on ℝ^n.
-/
open scoped BigOperators Matrix
theorem exp_neg_div_convex_is_concave
    {n : ℕ} (hn : 0 < n) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf₂ : ContDiff ℝ 2 f)
    (hconv : ConvexOn ℝ Set.univ f)
    (hpd :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ∃ hess_inv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
          (∀ v w : EuclideanSpace ℝ (Fin n),
            ((fderiv ℝ (fun y => fderiv ℝ f y) x) v) (hess_inv w) = inner ℝ v w) ∧
          (∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
            0 < ((fderiv ℝ (fun y => fderiv ℝ f y) x) v) v))
    (c : ℝ) (hc : 0 < c)
    (hlambda :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ∃ hess_inv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
          (∀ v w : EuclideanSpace ℝ (Fin n),
            ((fderiv ℝ (fun y => fderiv ℝ f y) x) v) (hess_inv w) = inner ℝ v w) ∧
          let gradx :=
            (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x)
          inner ℝ gradx (hess_inv gradx) ≤ c)
    : ConcaveOn ℝ Set.univ (fun x => Real.exp (-f x / c)) := by
  sorry

end «problem-44»