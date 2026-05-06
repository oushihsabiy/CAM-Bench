import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-46»
/-
For a set C ⊆ ℝ^n and a point x₀ ∈ C, the normal cone of C at x₀ is defined by N_C(x₀): = {y ∈ ℝ^n |
yᵀ(x - x₀) ≤ 0 for all x ∈ C}.
-/
def normalCone (C : Set (Fin n → ℝ)) (x₀ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | ∀ x, x ∈ C → dotProduct y (x - x₀) ≤ 0}

/-
For a system of inequality constraints a_iᵀ x ≤ bᵢ, the active set at a point x₀ is I(x₀): = {i |
a_iᵀ x₀ = bᵢ}, that is, the set of indices of the constraints active at x₀.
-/
def activeSet {m : ℕ} (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) : Set (Fin m) :=
  {i | dotProduct (a i) x₀ = b i}

/-
A polyhedron is a set of the form P = {x ∈ ℝ^n | Ax ≤ b}, for some matrix A ∈ ℝ^m× n and vector b ∈
ℝ^m, where the inequality is interpreted componentwise.
-/
def polyhedron {m : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, dotProduct (A i) x ≤ b i}

/-
Let C ⊆ ℝ^n and let x₀ ∈ ∂ C. Define the normal cone of C at x₀ by N_C(x₀): = {y ∈ ℝ^n | yᵀ(x - x₀)
≤
0 for all x ∈ C}. Prove that N_C(x₀) is a convex cone.
-/
theorem normalCone_is_convex_cone (C : Set (Fin n → ℝ)) (x₀ : Fin n → ℝ) :
    Convex ℝ (normalCone C x₀) ∧
      ∀ ⦃y : Fin n → ℝ⦄, y ∈ normalCone C x₀ → ∀ a : ℝ, 0 ≤ a → a • y ∈ normalCone C x₀ := by
  sorry

/-
Let P = {x ∈ ℝ^n | Ax preceq b}, where A ∈ ℝ^{m× n}, b ∈ ℝ^m, and Ax preceq b means (Ax)_i ≤ bᵢ for
i = 1, ..., m. Let x₀ ∈ ∂ P, and let I(x₀): = {i ∈ {1, ..., m} | a_iᵀ x₀ = bᵢ}, where a_iᵀ is the i
- th
row of A. Prove that N_P(x₀) = {\sum_{i ∈ I(x₀)} λ_i aᵢ | λ_i ≥ 0 for all i ∈ I(x₀)}.
-/
theorem normalCone_polyhedron_eq_nonneg_active_combinations {m : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) :
    x₀ ∈ frontier (polyhedron A b) →
    normalCone (polyhedron A b) x₀ =
      {y | ∃ μ : Fin m → ℝ,
        (∀ i, 0 ≤ μ i) ∧
        (∀ i, i ∉ activeSet A b x₀ → μ i = 0) ∧
        y = ∑ i, (μ i) • (A i)} := by
  sorry

end «problem-46»