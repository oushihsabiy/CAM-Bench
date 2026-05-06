import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-22»
/-
On S^n, the trace inner product is the bilinear form langle A, Brangle = tr(AB) for all A, B ∈ S^n.
-/
def traceInnerProduct {n : Type} [Fintype n] [DecidableEq n]
    (A B : {M : Matrix n n ℝ // M.IsSymm}) : ℝ :=
  Matrix.trace (A.1 * B.1)

/-
A symmetric matrix D ∈ S^n with D_{ii} = 0 for all i is a Euclidean distance matrix if and only if
xᵀ D x ≤ 0 for all x ∈ ℝ^n satisfying 1ᵀ x = 0.
-/
def dualCone {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Set E) : Set E :=
  {y | ∀ x ∈ K, 0 ≤ ⟪y, x⟫}

/-
Exercise 2.36 | 9 | thm

Let Sⁿ be the vector space of real symmetric n × n matrices, equipped with the trace inner product
⟨A, B⟩ = tr(AB), and let 1 ∈ ℝⁿ be the all - ones vector. Define

K = {D ∈ Sⁿ | D_{ii} = 0 for i = 1, …, n, and xᵀ D x ≤ 0 for all x ∈ ℝⁿ with 1ᵀ x = 0}.

Thus K is the cone of Euclidean distance matrices. Let V ∈ ℝ^{n×(n - 1)} be defined by

V_{ij} = {1 - 1/n if i = j, - 1/n if i ≠ j}

for i = 1, …, n and j = 1, …, n - 1. Prove that K is a convex cone and that its dual cone

K* = {Y ∈ Sⁿ | ⟨Y, D⟩ ≥ 0 for all D ∈ K}

is given by

K* = {V W Vᵀ + diag(u) | W ⪯ 0, u ∈ ℝⁿ}.
-/
theorem dualCone_of_euclideanDistanceMatrices_eq_vwvT_add_diag
    {n : ℕ} (hn : 1 < n) :
    let V : Matrix (Fin n) (Fin (n - 1)) ℝ :=
      fun i j => if (i : ℕ) = (j : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ))
    let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
      {D | D.IsSymm ∧ (∀ i, D i i = 0) ∧
        ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
          dotProduct x (D.mulVec x) ≤ 0}
    Convex ℝ K ∧
      (∀ a b, 0 ≤ a → 0 ≤ b → ∀ A ∈ K, ∀ B ∈ K, a • A + b • B ∈ K) ∧
      {Y : Matrix (Fin n) (Fin n) ℝ | Y.IsSymm ∧ ∀ D ∈ K, 0 ≤ Matrix.trace (Y * D)} =
        {Y : Matrix (Fin n) (Fin n) ℝ |
          Y.IsSymm ∧
          ∃ W : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ, ∃ u : Fin n → ℝ,
            Y = V * W * V.transpose + Matrix.diagonal u ∧
            W.IsSymm ∧
            ∀ x : Fin (n - 1) → ℝ, dotProduct x (W.mulVec x) ≤ 0} := by
  sorry

end «problem-22»
