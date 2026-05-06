import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-199»

/- [BLOCK Exercise 6.14-(d) | 7 | thm]
Let z₁,ldots,zₙ ∈ C be distinct and satisfy |zₖ|>1 for k=1,ldots,n. Define F=≤ft{f:C→C| f is
analytic on {z∈C:|z|>1} and Re f(z)≥ 0 for all |z|>1}. Define K_{PR}=≤ft{y∈C^n | ∃ f∈F such that
f(zₖ)=yₖ,\ k=1,ldots,n}. For y=(y₁,ldots,yₙ)∈C^n, let P(y)∈H^n be the matrix with entries
P(y)_{kl}=frac{yₖ+y_l}{1-z_kz_l}, k,l=1,ldots,n, where H^n is the set of n× n Hermitian complex
matrices. Prove that K_{PR}={y∈C^n| P(y)succeq 0}.
-/
open Complex

theorem pick_nevanlinna_representation_iff_psd
    {n : ℕ} {z : Fin n → ℂ}
    (hz : Function.Injective z)
    (hz1 : ∀ k, 1 < ‖z k‖) :
    {y : Fin n → ℂ |
      ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f {w : ℂ | 1 < ‖w‖} ∧
        (∀ w : ℂ, 1 < ‖w‖ → 0 ≤ (f w).re) ∧
        ∀ k, f (z k) = y k} =
    {y : Fin n → ℂ |
      (Matrix.toEuclideanLin
        (((fun k l => (y k + star (y l)) / (z k * star (z l) - 1)) :
          Matrix (Fin n) (Fin n) ℂ))).IsPositive} := by
  sorry

end «problem-199»
