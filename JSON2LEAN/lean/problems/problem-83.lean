import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-83»
/-
Consider the entropy minimization problem: minimize f(x) = \sum_{i = 1}^n xᵢ log xᵢ subject to A x =
b, with domain R_{+ +}^n. Here A is p by n with rank(A) = p < n, and assume there exists a strictly
positive feasible point x with A x = b.
-/
open BigOperators

/-
b, with domain R_{+ +}^n. Here A is p by n with rank(A) = p < n, and assume there exists a strictly
-/
structure EntropyMinimizationProblem where
  n : ℕ
  p : ℕ
  hpn : p < n
  A : Matrix (Fin p) (Fin n) ℝ
  rank_eq : A.rank = p
  b : Fin p → ℝ
  strictFeasiblePointExists : ∃ x : Fin n → ℝ, (∀ i : Fin n, 0 < x i) ∧ A.mulVec x = b

/-
b, with domain R_{+ +}^n. Here A is p by n with rank(A) = p < n, and assume there exists a strictly
-/
def EntropyMinimizationProblem.objective (P : EntropyMinimizationProblem) (x : Fin P.n → ℝ) : ℝ :=
  ∑ i : Fin P.n, x i * Real.log (x i)

/-
b, with domain R_{+ +}^n. Here A is p by n with rank(A) = p < n, and assume there exists a strictly
-/
def EntropyMinimizationProblem.isFeasible (P : EntropyMinimizationProblem) (x : Fin P.n → ℝ) : Prop :=
  (∀ i : Fin P.n, 0 < x i) ∧ P.A.mulVec x = P.b

/-
For the entropy minimization problem above, show that there exists a unique optimal solution x*.
-/
theorem entropy_minimization_problem_has_unique_optimal_solution
    (P : EntropyMinimizationProblem) :
    ∃! x : Fin P.n → ℝ,
      P.isFeasible x ∧
        ∀ y : Fin P.n → ℝ, P.isFeasible y → P.objective x ≤ P.objective y := by
  sorry
end «problem-83»
