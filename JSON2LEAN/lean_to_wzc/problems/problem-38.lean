import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-38»
/- [BLOCK Exercise 3.15-(b) | 19 | defn]
A set S ⊆ ℝ^n has nonempty interior if there exist x ∈ S and varepsilon > 0 such that {y ∈ ℝ^n :
‖y-x‖ < varepsilon} ⊆ S.
-/
def HasNonemptyInterior {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ x ∈ S, ∃ ε > 0, Metric.ball x ε ⊆ S

/- [BLOCK Exercise 3.15-(b) | 20 | opt_prob]
Consider the convex optimization problem
aligned
minimize quad & cᵀ x ;
subject to quad & fᵢ(x) ≤ 0, quad i=1,ldots,m, ;
& Ax=b.
aligned
-/
structure ConvexOptimizationProblem where
  n : ℕ
  m : ℕ
  c : EuclideanSpace ℝ (Fin n)
  f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ
  A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)
  b : EuclideanSpace ℝ (Fin m)

open scoped RealInnerProductSpace

def ConvexOptimizationProblem.isFeasible (P : ConvexOptimizationProblem)
    (x : EuclideanSpace ℝ (Fin P.n)) : Prop :=
  (∀ i : Fin P.m, P.f i x ≤ 0) ∧ P.A x = P.b

def ConvexOptimizationProblem.objectiveValue (P : ConvexOptimizationProblem)
    (x : EuclideanSpace ℝ (Fin P.n)) : ℝ :=
  ⟪P.c, x⟫

/- [BLOCK Exercise 3.15-(b) | 21 | thm]
Consider the convex optimization problem where x ∈ ℝ^n, c ∈ ℝ^n, A ∈ ℝ^{p × n}, b ∈ ℝ^p, and each fᵢ
: ℝ^n → ℝ is convex with dom fᵢ = ℝ^n for i=1,ldots,m. Introduce t ∈ ℝ and define K = cl≤ft{(x,t) ∈
ℝ^{n+1} | t fᵢ(x/t) ≤ 0, quad i=1,ldots,m, quad t>0 }, where cl(·) denotes closure ∈ ℝ^{n+1}. Assume
there exists x ∈ ℝ^n such that fᵢ(x) < 0, quad i=1,ldots,m. Show that K has nonempty interior ∈
ℝ^{n+1}.
-/
theorem cone_closure_has_nonempty_interior
    (P : ConvexOptimizationProblem)
    (hconvex : ∀ i : Fin P.m, ConvexOn ℝ Set.univ (P.f i))
    (x_tilde : EuclideanSpace ℝ (Fin P.n))
    (hSlater : ∀ i : Fin P.m, P.f i x_tilde < 0) :
    HasNonemptyInterior
      (closure
        {z : EuclideanSpace ℝ (Fin (P.n + 1)) |
          0 < z 0 ∧
          (∀ i : Fin P.m,
            z 0 * P.f i
                (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin P.n)).symm
                  (fun j : Fin P.n => z j.succ / z 0) : EuclideanSpace ℝ (Fin P.n))) ≤ 0)}) := by
  sorry

end «problem-38»
