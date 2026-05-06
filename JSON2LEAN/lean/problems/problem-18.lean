import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-18»
/-
For a cone $K ⊆ 𝕊^n$, its dual cone is defined by $$K^*: = {Y ∈ 𝕊^n | ⟨ Y, X ⟩ ≥ 0 for all X ∈ K}.
$$
-/
def dualCone {n : ℕ}
    (K : Set (Matrix (Fin n) (Fin n) ℝ)) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {Y | Y.IsSymm ∧ ∀ X, X ∈ K → Matrix.trace (Y * X) ≥ 0}

/-
A cone $K$ in an inner - product space is called self - dual if $K^* = K$, where $$K^*: = {y | ⟨ y,
x ⟩
≥ 0 for all x ∈ K}. $$
-/
def IsSelfDualCone {n : ℕ}
    (K : Set (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  dualCone K = K

/-
Let 𝕊^n be the vector space consisting of all n × n real symmetric matrices, with inner product
defined by ⟨ X, Y⟩: = tr(XY), ∀ X, Y ∈ 𝕊^n. Define the positive semidefinite cone 𝕊_ + ^n: = {X ∈
𝕊^n
| X ⪰ 0}, where X ⪰ 0 means that X is a positive semidefinite matrix. For any cone K ⊆ 𝕊^n, its dual
cone is defined by K^*: = {Y ∈ 𝕊^n | ⟨ Y, X⟩ ≥ 0, ∀ X ∈ K}. Prove that (𝕊_ + ^n)^* = 𝕊_ + ^n. That
is,
𝕊_ + ^n is a self - dual cone.
-/
theorem psdCone_isSelfDual {n : ℕ} :
    IsSelfDualCone
      {X : Matrix (Fin n) (Fin n) ℝ |
        X.IsSymm ∧ ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (X.mulVec v)} := by
  sorry
end «problem-18»
