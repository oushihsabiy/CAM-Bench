import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-26»
/-
A function f: A × B → ℝ is convex - concave if, for each fixed z ∈ B, the map x mapsto f(x, z) is
convex on A, and for each fixed x ∈ A, the map z mapsto f(x, z) is concave on B.
-/
theorem isConvexConcave_iff_hessian_blocks_semidefinite
    {n m : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin n)))
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (hA_open : IsOpen A)
    (hB_open : IsOpen B)
    (hA : Convex ℝ A)
    (hB : Convex ℝ B)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
    (h2 : ContDiffOn ℝ 2 (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) => f p.1 p.2)
      (A ×ˢ B)) :
    ((∀ z ∈ B, ConvexOn ℝ A (fun x => f x z)) ∧
      (∀ x ∈ A, ConcaveOn ℝ B (fun z => f x z))) ↔
      (∀ x ∈ A, ∀ z ∈ B,
        (∀ u : EuclideanSpace ℝ (Fin n),
          0 ≤
            iteratedFDeriv ℝ 2 (fun x' => f x' z) x ![u, u]) ∧
        (∀ v : EuclideanSpace ℝ (Fin m),
          iteratedFDeriv ℝ 2 (fun z' => f x z') z ![v, v] ≤ 0)) := by
  sorry

end «problem-26»
