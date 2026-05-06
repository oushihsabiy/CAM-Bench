import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-128»
/-
Given a differentiable function f: ℝ^n → ℝ, an iterative method is called a ∇descent iteration if it
generates points by x^(k + 1) = x^(k) - α_k ∇ f(x^(k)), with step sizes α_k > 0.
-/
def IsGradientDescentIteration {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (_hf : Differentiable ℝ f) (x : ℕ → Fin n → ℝ) (α : ℕ → ℝ) : Prop :=
  ∀ k : ℕ,
    x (k + 1) = x k - α k • (fun i => (fderiv ℝ f (x k)) (Pi.single i (1 : ℝ))) ∧ 0 < α k

/-
Given x ∈ ℝ^n and a search direction p ∈ ℝ^n, an exact line search chooses α ∈ ℝ such that f(x + α
p) = min_t ∈ ℝ f(x + tp).
-/
def IsExactLineSearch {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x p : Fin n → ℝ) (α : ℝ) : Prop :=
  ∀ t : ℝ, f (x + α • p) ≤ f (x + t • p)

/-
Exercise 8.1 - (b) | 8 | algo

Starting from x^{(0)} = (γ, 1), consider the ∇descent iteration with exact line search: x^{(k + 1)}
=
x^{(k)} - αₖ ∇f(x^{(k)}), k ≥ 0, where αₖ ∈ ℝ satisfies f(x^{(k)} - αₖ ∇f(x^{(k)})) = min_{α ∈ ℝ}
f(x^{(k)} - α ∇f(x^{(k)})).
-/
structure GradientDescentWithExactLineSearch where
  γ : ℝ
  f : (Fin 2 → ℝ) → ℝ
  hf : Differentiable ℝ f
  x : ℕ → Fin 2 → ℝ
  α : ℕ → ℝ
  x0 : x 0 = ![γ, 1]
  gradient_descent : IsGradientDescentIteration f hf x α
  exact_line_search : ∀ k : ℕ,
    IsExactLineSearch f (x k)
      (-(fun i => (fderiv ℝ f (x k)) (Pi.single i (1 : ℝ))))
      (α k)

theorem gradient_descent_with_exact_line_search_coordinates
    (A : GradientDescentWithExactLineSearch) (hγ : 1 < A.γ)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2) :
    ∀ k : ℕ,
      A.x k 0 = A.γ * ((A.γ - 1) / (A.γ + 1)) ^ k ∧
      A.x k 1 = (-((A.γ - 1) / (A.γ + 1))) ^ k := by
  sorry

/-
Let γ ≥ 1, and define f: ℝ^2 → ℝ by f(x₁, x₂) = γ x₁^2 - x₂^2. Starting from x^{(0)} = (γ, 1),
consider ∇descent with exact line search: x^{(k + 1)} = x^{(k)} - α_k ∇ f(x^{(k)}), k ≥ 0, where α_k
∈ ℝ
satisfies f(x^{(k)} - α_k ∇ f(x^{(k)})) = min_{α ∈ ℝ} f(x^{(k)} - α ∇ f(x^{(k)})). Show that x^{(k)}
→
(0, 0) and that f is unbounded below.
-/
theorem gradient_descent_with_exact_line_search_converges_to_zero_and_unbounded_below
    (A : GradientDescentWithExactLineSearch) (hγ : 1 < A.γ)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2)
    (hcoords :
      ∀ k : ℕ,
        A.x k 0 = A.γ * ((A.γ - 1) / (A.γ + 1)) ^ k ∧
        A.x k 1 = (-((A.γ - 1) / (A.γ + 1))) ^ k) :
    Tendsto A.x atTop (𝓝 0) ∧
      ∀ M : ℝ, ∃ x : Fin 2 → ℝ, A.f x < M := by
  sorry
end «problem-128»
