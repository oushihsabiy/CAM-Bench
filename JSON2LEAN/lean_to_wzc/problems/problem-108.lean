import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-108»
/-
For x ∈ ℝ^n and ω ∈ [0, 2π], define T(x, ω) = x₁ + x₂ cos ω + ··· + xₙ cos((n−1)ω). Let D = {x∈ℝ^n:
T(x,
ω) > 0 for all ω∈[0, 2π]}. Define f(x) = −∫_0^{2π} log T(x, ω) dω on D. Prove that f is convex on D.
-/
theorem f_convex_on_D_trigonometric_log_integral
    (n : ℕ) (hn : 0 < n) :
    ConvexOn ℝ
      {x : Fin n → ℝ | ∀ ω : ℝ, 0 ≤ ω → ω ≤ 2 * Real.pi →
        0 < ∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω)}
      (fun x =>
        -∫ ω in (0 : ℝ)..(2 * Real.pi),
          Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω))) := by
  sorry

end «problem-108»
