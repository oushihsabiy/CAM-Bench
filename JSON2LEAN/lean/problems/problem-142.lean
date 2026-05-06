import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-142»

-- Exercise_3_22

/-
Exercise 3.22 | 25 | thm

Let n ∈ ℕ, let ℝ₊ⁿ := {x = (x₁, …, xₙ) ∈ ℝⁿ ∣ xᵢ ≥ 0 for i = 1, …, n}, and let C ⊆ ℝ₊ⁿ be a nonempty
closed, bounded, convex set with 0 ∈ C. Let c ∈ ℝ₊ⁿ, and for k = 1, …, n, let eₖ ∈ ℝⁿ be the k-th
standard unit vector. Define C̃ := cl(ℝ₊ⁿ ∖ C), where cl(·) denotes closure ∈ ℝⁿ. Show that the
linear function x ↦ cᵀx attains a minimum over C̃ at some point αeₖ with α ≥ 0 and k ∈ {1, …, n}.
-/
theorem linear_min_on_closure_nonnegative_compl_attained_on_axis
    (n : ℕ)
    (C : Set (Fin n → ℝ))
    (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C)
    (hC_bdd : Bornology.IsBounded C)
    (hC_convex : Convex ℝ C)
    (h0C : (0 : Fin n → ℝ) ∈ C)
    (hC_nonneg : ∀ x ∈ C, ∀ i, 0 ≤ x i)
    (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hn : 0 < n) :
    let Ctilde : Set (Fin n → ℝ) := closure ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} \ C)
    ∃ α : ℝ, ∃ k : Fin n,
      0 ≤ α ∧
        (α • (fun i => if i = k then (1 : ℝ) else 0)) ∈ Ctilde ∧
        (∀ y ∈ Ctilde,
          ∑ i, c i * ((α • (fun j => if j = k then (1 : ℝ) else 0)) i) ≤
            ∑ i, c i * y i) := by
  sorry

/- [BLOCK Exercise 3.22 | 26 | thm]
Let n ∈ ℕ, let ℝ_+^n := {x=(x₁,dots,xₙ)∈ ℝ^n | xᵢ ≥ 0 for i=1,dots,n}, and let C ⊆ ℝ_+^n be a
nonempty closed, bounded, convex set with 0 ∈ C. Let c ∈ ℝ_+^n, and for k=1,dots,n, let eₖ ∈ ℝ^n be
the k-th standard unit vector. Define tilde C := cl(ℝ_+^n setminus C), where cl(·) denotes closure ∈
ℝ^n. Conclude that minimizing cᵀ x over tilde C reduces to solving n one-dimensional optimization
problems.
-/
theorem linear_min_on_closure_nonnegative_compl_reduces_to_axis_problems
    (n : ℕ)
    (C : Set (Fin n → ℝ))
    (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C)
    (hC_bdd : Bornology.IsBounded C)
    (hC_convex : Convex ℝ C)
    (h0C : (0 : Fin n → ℝ) ∈ C)
    (hC_nonneg : ∀ x ∈ C, ∀ i, 0 ≤ x i)
    (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hn : 0 < n) :
    ∃ k : Fin n, ∃ α : ℝ,
      0 ≤ α ∧
        (α • (fun i => if i = k then (1 : ℝ) else 0)) ∈
          closure ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} \ C) ∧
        (∀ y ∈ closure ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} \ C),
          ∑ i, c i * ((α • (fun j => if j = k then (1 : ℝ) else 0)) i) ≤
            ∑ i, c i * y i) := by
  sorry

end «problem-142»