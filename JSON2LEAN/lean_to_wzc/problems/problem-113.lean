import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-113»
/-
Let p > 1 and q satisfy 1/p + 1/q = 1. Define ‖x‖_p = (∑_{i = 1}^n |xᵢ|^p)^(1/p), and define f(x, t)
=
−(t^p−‖x‖_p^p)^(1/p) on dom(f) = {(x, t)∈ℝ^n×ℝ: t ≥ ‖x‖_p}. Prove that f is convex on dom(f).
-/
open scoped BigOperators
theorem minkowski_gauge_neg_root_convexOn
    {n : ℕ} {p q : ℝ}
    (hp : 1 < p) (hq : 1 / p + 1 / q = 1) :
    let pNormPow : (Fin n → ℝ) → ℝ :=
      fun x => ∑ i : Fin n, Real.rpow (|x i|) p
    let pNorm : (Fin n → ℝ) → ℝ :=
      fun x => Real.rpow (pNormPow x) (1 / p)
    let dom : Set ((Fin n → ℝ) × ℝ) :=
      {xt | xt.2 ≥ pNorm xt.1}
    let f : ((Fin n → ℝ) × ℝ) → ℝ :=
      fun xt => -Real.rpow (Real.rpow xt.2 p - pNormPow xt.1) (1 / p)
    ConvexOn ℝ dom f := by
  sorry

end «problem-113»