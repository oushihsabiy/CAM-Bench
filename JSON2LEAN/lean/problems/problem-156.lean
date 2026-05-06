import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-156»

/- [BLOCK Exercise 16.8 | 14 | thm]
Let A ∈ ℝ^{m × n} satisfy m< n and rank(A)=m. Show that there exist an orthogonal matrix Q ∈ ℝ^{n×n}
with Q^{T}Q=QQ^{T}=Iₙ, and an upper triangular matrix hat U ∈ ℝ^{m × m}, such that AQ=[ 0 & hat U ],
where 0 is the m × (n-m) zero matrix.
-/
open Matrix

theorem exists_orthogonal_right_factor_with_zero_block_upperTriangular
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (hmn : m < n) (hrank : Matrix.rank A = m) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      Q.transpose * Q = 1 ∧
      Q * Q.transpose = 1 ∧
      ∃ U : Matrix (Fin m) (Fin m) ℝ,
        (∀ i j : Fin m, j < i → U i j = 0) ∧
        ∃ e : Fin n ≃ Fin (n - m) ⊕ Fin m,
          Matrix.reindex (Equiv.refl _) e (A * Q) =
            Matrix.fromCols (0 : Matrix (Fin m) (Fin (n - m)) ℝ) U := by
  sorry

end «problem-156»