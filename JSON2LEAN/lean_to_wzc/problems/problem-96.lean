import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-96»

/- [BLOCK Exercise 6.14-(d) | 19 | thm]
Let z₁, ..., zₙ ∈ ℂ be distinct and satisfy |zₖ| > 1 for k = 1, ..., n.
Define
F = {f : ℂ → ℂ | f is analytic on {z ∈ ℂ : |z| > 1}
and Re f(z) ≥ 0 for all |z| > 1}.
Define
K_PR = {y ∈ ℂ^n | ∃ f ∈ F such that f(zₖ) = yₖ, k = 1, ..., n}.
For y = (y₁, ..., yₙ) ∈ ℂ^n, define the Pick matrix P(y) by
P(y)_{kl} = (yₖ + conjugate(y_l)) / (zₖ * conjugate(z_l) - 1).
Prove that K_PR is exactly the set of y such that P(y) is positive semidefinite.
-/
theorem positive_real_interpolation_iff_psd_pick_matrix
    {n : ℕ} (z y : Fin n → ℂ)
    (hz_distinct : Function.Injective z)
    (hz_unit : ∀ k : Fin n, 1 < ‖z k‖) :
    (∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f {w : ℂ | 1 < ‖w‖} ∧
      (∀ w : ℂ, 1 < ‖w‖ → 0 ≤ Complex.re (f w)) ∧
      ∀ k : Fin n, f (z k) = y k) ↔
    (let P : Matrix (Fin n) (Fin n) ℂ :=
      fun k l : Fin n => (y k + star (y l)) / (z k * star (z l) - 1)
     P.IsHermitian ∧
       ∀ x : Fin n → ℂ,
         0 ≤ Complex.re (dotProduct (fun i => star (x i)) (P.mulVec x))) := by
  sorry

end «problem-96»
