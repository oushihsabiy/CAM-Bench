import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-114»
/-
Let p > 1 and define ‖x‖_p as usual. Define f(x, t) = −log(t^p−‖x‖_p^p) on dom(f) = {(x, t)∈ℝ^n×ℝ: t
> ‖x‖_p}. Prove that f is convex on dom(f).
-/
open scoped BigOperators

theorem lp_log_barrier_convexOn
    {n : ℕ} {p : ℝ} (hp : 1 < p) :
    let pNormPow : (Fin n → ℝ) → ℝ := fun x => ∑ i : Fin n, Real.rpow (|x i|) p
    let pNorm : (Fin n → ℝ) → ℝ := fun x => Real.rpow (pNormPow x) (1 / p)
    ConvexOn ℝ
      {xt : (Fin n → ℝ) × ℝ | pNorm xt.1 < xt.2}
      (fun xt : (Fin n → ℝ) × ℝ =>
        -Real.log (Real.rpow xt.2 p - pNormPow xt.1)) := by
  sorry

end «problem-114»
