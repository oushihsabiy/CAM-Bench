import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-184»

/- [BLOCK Exercise 17.9 | 10 | defn]
For a nonempty closed convex set C ⊆ ℝ^n, the projection of y ∈ ℝ^n onto C is the unique point
P_C(y) ∈ C such that ‖y-P_C(y)‖ ≤ ‖y-z‖ for all z ∈ C.
-/
open scoped BigOperators

def IsProjection {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (y x : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  x ∈ C ∧
    (∀ z ∈ C, ‖y - x‖ ≤ ‖y - z‖) ∧
    (∀ x' : EuclideanSpace ℝ (Fin n),
      x' ∈ C → (∀ z ∈ C, ‖y - x'‖ ≤ ‖y - z‖) → x' = x)

/- [BLOCK Exercise 17.9 | 11 | defn]
For the problem min f(x) subject to gᵢ(x) ≤ 0 and hⱼ(x)=0, the Karush--Kuhn--Tucker conditions are
that there exist multipliers λ_i ≥ 0 and nu_j such that
∇ f(x)+sum_i λ_i ∇ gᵢ(x)+sum_j nu_j ∇ hⱼ(x)=0,
gᵢ(x)≤ 0, hⱼ(x)=0, λ_i gᵢ(x)=0 for all i.
-/
open scoped RealInnerProductSpace

def kktConditions {n m p : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ lam : Fin m → ℝ, ∃ nu : Fin p → ℝ,
    gradient f x + ∑ i, lam i • gradient (g i) x + ∑ j, nu j • gradient (h j) x = 0 ∧
      (∀ i, g i x ≤ 0) ∧
      (∀ j, h j x = 0) ∧
      (∀ i, 0 ≤ lam i) ∧
      (∀ i, lam i * g i x = 0)

/- [BLOCK Exercise 17.9 | 12 | defn]
A bound-constrained problem is an optimization problem of the form min f(x) subject to l ≤ x ≤ u
componentwise, where l,u ∈ ℝ^n are given vectors with lᵢ ≤ uᵢ.
-/
structure BoundConstrainedProblem (n : ℕ) where
  f : EuclideanSpace ℝ (Fin n) → ℝ
  l : EuclideanSpace ℝ (Fin n)
  u : EuclideanSpace ℝ (Fin n)
  bounds_ordered : ∀ i : Fin n, l i ≤ u i

def BoundConstrainedProblem.isFeasible {n : ℕ} (P : BoundConstrainedProblem n)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ i : Fin n, P.l i ≤ x i ∧ x i ≤ P.u i

/-
Exercise 17.9 | 13 | opt_prob

Let n ∈ ℕ, let l, u ∈ ℝⁿ satisfy lᵢ ≤ uᵢ for each i = 1, …, n, and let φ : ℝⁿ → ℝ be continuously
differentiable. Consider the optimization problem

minimize φ(x) subject to x ∈ ℝⁿ and l ≤ x ≤ u,

where the inequalities are componentwise, and define the feasible set by

[l, u] := {x ∈ ℝⁿ : l ≤ x ≤ u}.
-/
structure BoxConstrainedOptimizationProblem (n : ℕ) where
  φ : EuclideanSpace ℝ (Fin n) → ℝ
  φ_contDiff : ContDiff ℝ 1 φ
  l : EuclideanSpace ℝ (Fin n)
  u : EuclideanSpace ℝ (Fin n)
  bounds_ordered : ∀ i : Fin n, l i ≤ u i

def BoxConstrainedOptimizationProblem.feasibleSet {n : ℕ} (P : BoxConstrainedOptimizationProblem n) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i : Fin n, P.l i ≤ x i ∧ x i ≤ P.u i}

/-
Exercise 17.9 | 14 | thm

Let n ∈ ℕ, let l, u ∈ ℝ^n satisfy lᵢ ≤ uᵢ for each i = 1, …, n, and let φ : ℝ^n → ℝ be continuously
differentiable. Consider the bound-constrained optimization problem

min_{x ∈ ℝ^n} φ(x) subject to l ≤ x ≤ u,

where the inequalities are componentwise, and define the feasible set by

[l, u] := {x ∈ ℝ^n : l ≤ x ≤ u}.

Define the projection P(·, l, u) : ℝ^n → [l, u] componentwise by

P(g, l, u)ᵢ =
{
lᵢ, if gᵢ ≤ lᵢ,
gᵢ, if lᵢ < gᵢ < uᵢ,
uᵢ, if gᵢ ≥ uᵢ,
}

for i = 1, …, n. Verify that the Karush–Kuhn–Tucker conditions for this bound-constrained problem
are equivalent to

x - P(x - ∇φ(x), l, u) = 0.
-/
theorem kktConditions_iff_eq_projection_fixed_point
    {n : ℕ}
    (P : BoxConstrainedOptimizationProblem n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (kktConditions P.φ
      (fun i y =>
        if h : i.1 < n then
          y ⟨i.1, h⟩ - P.u ⟨i.1, h⟩
        else
          let j : Fin n :=
            ⟨i.1 - n, by
              have hi : i.1 < n + n := i.2
              have hge : n ≤ i.1 := Nat.le_of_not_lt h
              omega⟩
          P.l j - y j)
      (fun j _ => False.elim (Fin.elim0 j))
      x) ↔
      x -
          (fun i =>
            max (P.l i) (min (x i - gradient P.φ x i) (P.u i))) =
        0 := by
  sorry

end «problem-184»
