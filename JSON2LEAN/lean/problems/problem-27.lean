import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-27»
/-
Let f: ℝ^n \times ℝ^m o ℝ and f ∈ C^2. Define: if for every fixed z ∈ ℝ^m, the function x mapsto
f(x,
z) is convex on ℝ^n; and for every fixed x ∈ ℝ^n, the function z mapsto f(x, z) is concave on ℝ^m,
then f is called a convex - - concave function with respect to (x, z). Prove the following
equivalence:
f is a convex - - concave function with respect to (x, z) if and only if for every (x, z) ∈ ℝ^n
\times
ℝ^m, one has abla_{xx}^2 f(x, z) succeq 0, abla_{zz}^2 f(x, z) preceq 0. Here, abla_{xx}^2 f(x, z)
succeq 0 means that the Hessian matrix with respect to x is positive semidefinite, and abla_{zz}^2
f(x, z) preceq 0 means that the Hessian matrix with respect to z is negative semidefinite.
-/
theorem convexConcave_iff_hessian_blocks_semidefinite
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hf : ContDiff ℝ 2 f) :
    ((
      ∀ z : EuclideanSpace ℝ (Fin m),
        ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => f (x, z))) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        ConcaveOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    ) ↔
    (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m),
      (∀ v : EuclideanSpace ℝ (Fin n),
        0 ≤
          (fderiv ℝ
            (fun x : EuclideanSpace ℝ (Fin n) =>
              (fderiv ℝ (fun x' : EuclideanSpace ℝ (Fin n) => f (x', p.2)) x) v)
            p.1) v) ∧
      (∀ w : EuclideanSpace ℝ (Fin m),
        (fderiv ℝ
          (fun z : EuclideanSpace ℝ (Fin m) =>
            (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin m) => f (p.1, z')) z) w)
          p.2) w ≤ 0)) := by
  sorry

end «problem-27»