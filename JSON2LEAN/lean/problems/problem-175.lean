import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-175»

/- [BLOCK Exercise 6.3 | 1 | thm]
Let sₖ,yₖ∈ ℝ^n, let Bₖ∈ ℝ^{n×n} be invertible, and let Hₖ=Bₖ^{-1}. Assume s_kᵀ Bₖ s_kne 0 and y_kᵀ
s_kne 0, and define ρ_k=(y_kᵀ sₖ)^{-1}. Let B_{k+1}=Bₖ-(Bₖ sₖ s_kᵀ Bₖ)/(s_kᵀ Bₖ sₖ)+(yₖ y_kᵀ)/(y_kᵀ
sₖ) and H_{k+1}=(I-ρ_k sₖ y_kᵀ)Hₖ(I-ρ_k yₖ s_kᵀ)+ρ_k sₖ s_kᵀ, where I is the n× n identity matrix.
Show that H_{k+1}=B_{k+1}^{-1}.
-/
open Matrix

theorem bfgs_inverse_update_is_inverse
    {n : Type*} [Fintype n] [DecidableEq n]
    (sk yk : n → ℝ) (Bk Hk : Matrix n n ℝ)
    (hBk_inv : IsUnit Bk.det)
    (hHk : Hk = Bk⁻¹)
    (hskBkSk : (dotProduct sk (Bk *ᵥ sk)) ≠ 0)
    (hykTsk : (dotProduct yk sk) ≠ 0) :
    let ρk : ℝ := (dotProduct yk sk)⁻¹
    let Bk1 : Matrix n n ℝ :=
      Bk
        - ((dotProduct sk (Bk *ᵥ sk))⁻¹ : ℝ) • ((Bk * Matrix.vecMulVec sk sk) * Bk)
        + ((dotProduct yk sk)⁻¹ : ℝ) • Matrix.vecMulVec yk yk
    let Hk1 : Matrix n n ℝ :=
      (((1 : Matrix n n ℝ) - ρk • Matrix.vecMulVec sk yk) * Hk *
        ((1 : Matrix n n ℝ) - ρk • Matrix.vecMulVec yk sk))
        + ρk • Matrix.vecMulVec sk sk
    Hk1 = Bk1⁻¹ := by
  sorry

end «problem-175»