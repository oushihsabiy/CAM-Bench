import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-172»
/-
Let C be a nonempty convex subset of ℝ^n, let C^c = ℝ^n C, and fix a norm. Define dist(x, S) =
\inf{‖x - z‖: z in S}. For x in C, define depth(x, C) = dist(x, C^c). Prove that depth(., C) is
concave
on C: for all x, y in C and θ in [0, 1], depth(θ x + (1 - θ) y, C) > = θ depth(x, C) + (1 - θ)
depth(y,
C).
-/
theorem depth_concave_on_convex_set
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC_nonempty : C.Nonempty)
    (hC_compl_nonempty : (Cᶜ).Nonempty)
    (hC_convex : Convex ℝ C) :
    ∀ x y : EuclideanSpace ℝ (Fin n), x ∈ C → y ∈ C →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        Metric.infDist (θ • x + (1 - θ) • y) (Cᶜ) ≥
          θ * Metric.infDist x (Cᶜ) + (1 - θ) * Metric.infDist y (Cᶜ) := by
  sorry

end «problem-172»
