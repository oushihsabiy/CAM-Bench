import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-187»

/- [BLOCK Exercise 3.15-(c) | 22 | defn]
A set C ⊆ ℝ^{n+1} is pointed if C cap (-C) = {0}.
-/
def Pointed (C : Set (Fin (Nat.succ n) → ℝ)) : Prop :=
  C ∩ Neg.neg '' C = ({0} : Set (Fin (Nat.succ n) → ℝ))

/- [BLOCK Exercise 3.15-(c) | 23 | opt_prob]
Consider the convex optimization problem
aligned
minimize quad & cᵀ x ;
subject\ to quad & fᵢ(x) ≤ 0, quad i=1,ldots,m, ;
& Ax=b,
aligned
where x ∈ ℝ^n, c ∈ ℝ^n, A ∈ ℝ^{p × n}, b ∈ ℝ^p, and each fᵢ : ℝ^n → ℝ is convex with dom fᵢ = ℝ^n
for i=1,ldots,m.
-/
structure ConvexOptimizationProblem where
  n : ℕ
  m : ℕ
  p : ℕ
  c : Fin n → ℝ
  A : Matrix (Fin p) (Fin n) ℝ
  b : Fin p → ℝ
  f : Fin m → (Fin n → ℝ) → ℝ

def ConvexOptimizationProblem.isFeasible
    (P : ConvexOptimizationProblem) (x : Fin P.n → ℝ) : Prop :=
  (∀ i : Fin P.m, P.f i x ≤ 0) ∧ P.A.mulVec x = P.b

def ConvexOptimizationProblem.objective
    (P : ConvexOptimizationProblem) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.c j * x j

/- [BLOCK Exercise 3.15-(c) | 24 | thm]
Consider the convex optimization problem
aligned
minimize quad & cᵀ x ;
subject\ to quad & fᵢ(x) ≤ 0, quad i=1,ldots,m, ;
& Ax=b,
aligned
where x ∈ ℝ^n, c ∈ ℝ^n, A ∈ ℝ^{p × n}, b ∈ ℝ^p, and each fᵢ : ℝ^n → ℝ is convex with dom fᵢ = ℝ^n
for i=1,ldots,m.
Define
K = cl≤ft{(x,t) ∈ ℝ^{n+1} | t>0, t fᵢ(x/t) ≤ 0 for i=1,ldots,m },
where cl denotes closure ∈ ℝ^{n+1}.
Assume that the set
{x ∈ ℝ^n | fᵢ(x) ≤ 0, quad i=1,ldots,m}
is bounded.
A set C ⊆ ℝ^{n+1} is pointed if
C cap (-C) = {0}.
Show that K is pointed.
-/
theorem K_pointed_of_bounded_feasible_set
    (P : ConvexOptimizationProblem)
    (hconvex_f : ∀ i : Fin P.m, ConvexOn ℝ (Set.univ : Set (Fin P.n → ℝ)) (P.f i))
    (hfeasible : {x : Fin P.n → ℝ | P.isFeasible x}.Nonempty)
    (hbounded :
      Bornology.IsBounded
        {x : Fin P.n → ℝ | P.isFeasible x}) :
    Pointed
      (closure
        {xt : Fin (Nat.succ P.n) → ℝ |
          0 < xt 0 ∧
          (∀ i : Fin P.m,
            xt 0 * P.f i
              (fun j : Fin P.n => xt (Fin.succ j) / xt 0) ≤ 0) ∧
          P.A.mulVec (fun j : Fin P.n => xt (Fin.succ j) / xt 0) = P.b}) := by
  sorry

end «problem-187»
