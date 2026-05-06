import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-37»
/-
For a cone K subseteq ℝ^n, its dual cone is K* = {y ∈ ℝ^n | xᵀ y > = 0 for all x in K}.
-/
def dualCone {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  { y | ∀ x, x ∈ K → 0 ≤ dotProduct x y }

/-
A cone C subseteq ℝ^n is pointed if for every y in C, the condition - y in C implies y = 0.
-/
def IsPointed {n : ℕ} (C : Set (Fin n → ℝ)) : Prop :=
  ∀ y, y ∈ C → -y ∈ C → y = 0

/-
Let K subseteq ℝ^n be a convex cone, and define its dual cone by K* = {y ∈ ℝ^n | xᵀ y > = 0 for all
x in K}. A cone C subseteq ℝ^n is pointed if whenever y in C and - y in C, then y = 0. Prove that if
K has nonempty interior, then K* is pointed.
-/
theorem dualCone_isPointed_of_interior_nonempty {n : ℕ} (K : Set (Fin n → ℝ))
    (hconv : Convex ℝ K)
    (hcone_add : ∀ ⦃x y : Fin n → ℝ⦄, x ∈ K → y ∈ K → x + y ∈ K)
    (hcone_smul : ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → a • x ∈ K)
    (hinter : (interior K).Nonempty) :
    IsPointed (dualCone K) := by
  sorry

end «problem-37»