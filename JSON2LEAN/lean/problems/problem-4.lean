import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-4»
/-
Let N, n ∈ ℕ with N ≥ 1. Let x₁, ..., x_N ∈ ℝ^n and μ ∈ ℝ^n. For π = (π_1, ..., π_N) ∈ ℝ^N, define
f(π) = - \sum_{i = 1}^N π_i log π_i, with the convention 0 log 0 = 0. Define the feasible set C = {π
∈
ℝ^N | π_i ≥ 0 for i = 1, ..., N, \sum_{i = 1}^N π_i = 1, \sum_{i = 1}^N π_i xᵢ = μ}. Consider the
optimization problem maximize f(π) subject to π ∈ C.
-/
open scoped BigOperators

/-
Let N, n ∈ ℕ with N ≥ 1. Let x₁, …, x_N ∈ ℝⁿ and μ ∈ ℝⁿ.
-/
structure MaximumEntropyProblem where
  N : ℕ
  n : ℕ
  hN : 1 ≤ N
  x : Fin N → (Fin n → ℝ)
  μ : Fin n → ℝ

/-
For π = (π₁, …, π_N) ∈ ℝ^N, define

f(π) = - ∑_{i = 1}^N π_i log π_i,

with the convention 0 log 0 = 0.
-/
def MaximumEntropyProblem.entropyTerm (t : ℝ) : ℝ :=
  if t = 0 then 0 else -t * Real.log t

/-
For π = (π₁, …, π_N) ∈ ℝ^N, define

f(π) = - ∑_{i = 1}^N π_i log π_i,

with the convention 0 log 0 = 0.
-/
def MaximumEntropyProblem.objective (P : MaximumEntropyProblem) (π : Fin P.N → ℝ) : ℝ :=
  ∑ i, MaximumEntropyProblem.entropyTerm (π i)

/-
C = {π ∈ ℝ^N | π_i ≥ 0 for i = 1, ..., N, \sum_{i = 1}^N π_i = 1, \sum_{i = 1}^N π_i xᵢ = μ}.
-/
def MaximumEntropyProblem.IsFeasible (P : MaximumEntropyProblem) (π : Fin P.N → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧
    (∑ i, π i = 1) ∧
      ∀ j, ∑ i, π i * P.x i j = P.μ j

/-
Consider the optimization problem: maximize f(π) subject to π ∈ C.
-/
theorem maximumEntropyProblem_is_convexOptimizationProblem
    (P : MaximumEntropyProblem) :
    ConcaveOn ℝ {π : Fin P.N → ℝ | ∀ i, 0 ≤ π i} P.objective ∧
      Convex ℝ {π : Fin P.N → ℝ | P.IsFeasible π} := by
  sorry
end «problem-4»