import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-115»
/-
Let p > 1 and D = {(x, t)∈ℝ^n×ℝ: t > ‖x‖_p}. Define f(x, t) = ‖x‖_p^p / t^(p−1). Prove that f is
convex on D.
-/
theorem lp_power_over_t_convexOn
    {n : ℕ} {p : ℝ}
    (hp : 1 < p) :
    let pNormPow : (Fin n → ℝ) → ℝ := fun x => ∑ i : Fin n, Real.rpow (|x i|) p
    let pNorm : (Fin n → ℝ) → ℝ := fun x => Real.rpow (pNormPow x) (1 / p)
    ConvexOn ℝ
      {xt : (Fin n → ℝ) × ℝ | xt.2 > pNorm xt.1}
      (fun xt : (Fin n → ℝ) × ℝ => pNormPow xt.1 / Real.rpow xt.2 (p - 1)) := by
  sorry

end «problem-115»