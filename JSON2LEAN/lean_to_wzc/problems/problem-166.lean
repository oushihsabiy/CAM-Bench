import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-166»
/-
Let K = [ P & Aᵀ; A & 0 ], where P ∈ S_ + ^n, A ∈ ℝ^{p× n}, and rank(A) = p < n. Let N(M) = {x| Mx =
0} and R(M) denote the nullspace and range of a matrix M, respectively. Prove that the following
statements are equivalent: K is nonsingular, N(P)cap N(A) = {0}, ∀ x∈ ℝ^n, Ax = 0 and xne 0 implies
xᵀ P x > 0, Fᵀ P F succ 0 for any F∈ ℝ^{n× (n - p)} satisfying R(F) = N(A), ∃ Q ∈ S_ + ^p such that
P + Aᵀ
Q A succ 0.
-/
theorem kkt_matrix_nonsingular_iff_conditions
    {n p : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin p) (Fin n) ℝ)
    (hP_symm : P.IsSymm) (hP_psd : ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (P.mulVec x))
    (hA_rank : Matrix.rank A = p) (hpn : p < n) :
    let K := Matrix.fromBlocks P Aᵀ A (0 : Matrix (Fin p) (Fin p) ℝ)
    let cond1 : Prop := K.det ≠ 0
    let cond2 : Prop :=
      ((LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
        (LinearMap.ker A.toLin' : Submodule ℝ (Fin n → ℝ)) = ⊥)
    let cond3 : Prop :=
      ∀ x : Fin n → ℝ, A.mulVec x = 0 → x ≠ 0 → 0 < dotProduct x (P.mulVec x)
    let cond4 : Prop :=
      ∀ F : Matrix (Fin n) (Fin (n - p)) ℝ,
        LinearMap.range F.toLin' = LinearMap.ker A.toLin' →
        Matrix.PosDef (Fᵀ * P * F)
    let cond5 : Prop :=
      ∃ Q : Matrix (Fin p) (Fin p) ℝ,
        Q.IsSymm ∧
        (∀ y : Fin p → ℝ, 0 ≤ dotProduct y (Q.mulVec y)) ∧
        Matrix.PosDef (P + Aᵀ * Q * A)
    (cond1 ↔ cond2) ∧
    (cond1 ↔ cond3) ∧
    (cond1 ↔ cond4) ∧
    (cond1 ↔ cond5) := by
  sorry

end «problem-166»