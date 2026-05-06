import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-109»

/- [BLOCK Exercise 8.20 | 27 | thm]
Let C = {x ∈ ℝ^n : x₁ A₁ + ... + xₙ Aₙ <= B}, where Aᵢ and B are real symmetric m x m matrices, and
assume int(C) is nonempty. Let x_ac minimize φ(x) = -log det(B - sum xᵢ Aᵢ) on the positive definite
domain, and let H be the Hessian of φ at x_ac. Define E_inner = {x : (x-x_ac)ᵀ H (x-x_ac) <= 1} and
E_outer = {x : (x-x_ac)ᵀ H (x-x_ac) <= m(m-1)}. Prove E_inner subseteq C subseteq E_outer.
-/
theorem logDetBarrier_ellipsoid_bounds
    {n m : ℕ}
    (hm : 2 ≤ m)
    (C : Set (Fin n → ℝ))
    (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (x_ac : Fin n → ℝ)
    (phi : (Fin n → ℝ) → ℝ)
    (hA_symm : ∀ i, (A i)ᵀ = A i)
    (hB_symm : Bᵀ = B)
    (hC :
      C =
        {x | Matrix.PosSemidef (B - ∑ i, (x i) • A i)})
    (hC_interior : (interior C).Nonempty)
    (hC_bounded : Bornology.IsBounded C)
    (hphi :
      phi =
        fun x => -Real.log (Matrix.det (B - ∑ i, (x i) • A i)))
    (hx_ac_min :
      x_ac ∈ {x | Matrix.PosDef (B - ∑ i, (x i) • A i)} ∧
        ∀ x, x ∈ {x | Matrix.PosDef (B - ∑ i, (x i) • A i)} → phi x_ac ≤ phi x)
    (hHessian :
      ContDiffAt ℝ 2 phi x_ac ∧
        ∀ i j,
          H i j =
            (fderiv ℝ
              (fun y => (fderiv ℝ phi y) (Pi.single j (1 : ℝ)))
              x_ac) (Pi.single i (1 : ℝ)))
    (hH_symm : H.IsSymm)
    (hH_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (H.mulVec v)) :
    {x | (∑ i, ∑ j, (x i - x_ac i) * ((H i j) * (x j - x_ac j))) ≤ 1} ⊆ C ∧
      C ⊆ {x | (∑ i, ∑ j, (x i - x_ac i) * ((H i j) * (x j - x_ac j))) ≤ ((m : ℝ) * ((m : ℝ) - 1))} := by
  sorry

end «problem-109»
