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
  sorry

end «problem-177»