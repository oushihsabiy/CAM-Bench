import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-85»
/-
The second - order cone in ℝ^(n + 1) is the set K: = {(x, t) ∈ ℝ^(n + 1) | t ≥ ‖x‖_2}.
-/
def secondOrderCone (n : ℕ) : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  {p | ‖p.1‖ ≤ p.2}


/-
Let the second - order cone be K: = {(x, t)∈ ℝ^(n + 1) | t ≥ ‖x‖_2}, where x∈ ℝ^n, t∈ ℝ, and ‖x‖_2
is
the Euclidean norm. Its dual cone is defined by K^*: = {(y, s)∈ ℝ^(n + 1) | ⟨ x, y⟩ + ts ≥ 0, ∀ (x,
t)∈ K}, where ⟨ x, y⟩ is the standard inner product in ℝ^n. Prove that the second - order cone K is
self - dual.
-/
open scoped RealInnerProductSpace

theorem secondOrderCone_isSelfDual (n : ℕ) :
    {q : EuclideanSpace ℝ (Fin n) × ℝ |
      ∀ p ∈ secondOrderCone n, 0 ≤ ⟪p.1, q.1⟫ + p.2 * q.2} = secondOrderCone n := by
  sorry


end «problem-85»