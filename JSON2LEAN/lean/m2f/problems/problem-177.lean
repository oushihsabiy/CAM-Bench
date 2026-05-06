import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-177»
/-
Let G ∈ ℝ^{n×n} and A ∈ ℝ^{m × n}. Define K = [G & Aᵀ; A & 0] ∈ ℝ^{(n + m)×(n + m)}, where Aᵀ is the
ᵀ
of A and 0 is the m × m zero matrix. Assume that K is invertible. Prove that rank(A) = m.
-/
theorem rank_eq_of_block_kkt_invertible
    {m n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hK :
      Function.Injective
        (Matrix.toLin'
          (Matrix.fromBlocks G A.transpose A 0 :
            Matrix (Sum (Fin n) (Fin m)) (Sum (Fin n) (Fin m)) ℝ))) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = m := by
  -- First show that a vector in the kernel of `Aᵀ` gives a kernel vector of the KKT block map.
  have transpose_kernel_vector_eq_zero :
      ∀ y : Fin m → ℝ, Matrix.toLin' A.transpose y = 0 → y = 0 := by
    intro y hy
    have hy' : A.transpose *ᵥ y = 0 := by
      simpa [Matrix.toLin'_apply] using hy
    have hblock :
        Matrix.toLin'
            (Matrix.fromBlocks G A.transpose A 0 :
              Matrix (Sum (Fin n) (Fin m)) (Sum (Fin n) (Fin m)) ℝ)
            (Sum.elim (0 : Fin n → ℝ) y) = 0 := by
      -- Compute the block action on the vector supported only in the `Fin m` coordinates.
      rw [Matrix.toLin'_apply, Matrix.fromBlocks_mulVec]
      ext i
      cases i with
      | inl i =>
          simp [hy']
      | inr i =>
          simp
    have hzero : Sum.elim (0 : Fin n → ℝ) y = (0 : Sum (Fin n) (Fin m) → ℝ) := by
      -- Injectivity of the KKT map forces this kernel vector to vanish.
      apply hK
      simpa using hblock
    -- Reading the `Fin m` coordinates of the vanished block vector gives `y = 0`.
    funext i
    exact congrFun hzero (Sum.inr i)
  -- Kernel-triviality gives injectivity of the transpose linear map.
  have hAt_injective : Function.Injective (Matrix.toLin' A.transpose) := by
    intro y z hyz
    have hsub : Matrix.toLin' A.transpose (y - z) = 0 := by
      rw [LinearMap.map_sub, hyz, sub_self]
    have hz : y - z = 0 := transpose_kernel_vector_eq_zero (y - z) hsub
    exact sub_eq_zero.mp hz
  -- Injectivity identifies the finrank of the transpose range with the domain dimension `m`.
  have hAt_range :
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' A.transpose)) = m := by
    simpa using LinearMap.finrank_range_of_inj (R := ℝ) (f := Matrix.toLin' A.transpose)
      hAt_injective
  have hAt_rank : A.transpose.rank = m := by
    rw [Matrix.rank, ← Matrix.toLin'_apply']
    exact hAt_range
  have hA_rank : A.rank = m := by
    rw [← Matrix.rank_transpose (R := ℝ) (A := A)]
    exact hAt_rank
  -- Finally rewrite `Matrix.rank` back to the finrank of the range of `A.toLin'`.
  rw [Matrix.rank, ← Matrix.toLin'_apply'] at hA_rank
  exact hA_rank

end «problem-177»
