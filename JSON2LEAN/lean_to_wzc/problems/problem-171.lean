import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-171»
/-
A set C is a Chebyshev set if for every x ∈ ℝ^n there exists a unique point P_C(x) in C such that ‖x
- P_C(x)‖ < = ‖x - y‖ for all y in C.
-/
def IsChebyshevSet {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    ∃! p, p ∈ C ∧ ∀ y, y ∈ C → ‖x - p‖ ≤ ‖x - y‖

/-
Let C be a Chebyshev set ∈ ℝ^n. Assume that for every x ∈ ℝ^n and every t > = 0, P_C(P_C(x) + t (x -
P_C(x))) = P_C(x). Prove that C is convex.
-/
theorem chebyshev_set_convex_of_projection_ray_fixed {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsChebyshevSet C)
    (hproj :
      ∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
        0 ≤ t →
          let p := Classical.choose (hC x)
          Classical.choose (hC (p + t • (x - p))) = p) :
    Convex ℝ C := by
  sorry
end «problem-171»