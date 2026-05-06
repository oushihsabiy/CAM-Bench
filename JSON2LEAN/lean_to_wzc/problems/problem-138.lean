import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-138»
/-
For the problem min_x f(x) subject to inequality constraints gᵢ(x) ≤ 0, the Karush - Kuhn - Tucker
conditions at x* assert that there exist multipliers λ_i* ≥ 0 such that gᵢ(x*) ≤ 0 for all i (primal
feasibility), λ_i* gᵢ(x*) = 0 for all i (complementary slackness), and, when differentiable, ∇ f(x*)
+ sum_i λ_i* ∇ gᵢ(x*) = 0 (stationarity).
-/
open scoped BigOperators

def KarushKuhnTuckerConditions
    {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (xStar : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ lam : Fin m → ℝ,
    (∀ i, 0 ≤ lam i) ∧
    (∀ i, g i xStar ≤ 0) ∧
    (∀ i, lam i * g i xStar = 0) ∧
    (gradient f xStar + ∑ i, lam i • gradient (g i) xStar = 0)


/-
Consider the exponential constrained optimization problem. Determine whether this problem satisfies
the KKT conditions at its optimal solution.
-/
theorem exponentialConstrainedOptimizationProblem_has_no_optimal_solution_and_no_kkt_point :
    let f : EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun x => Real.exp (x 0) + Real.exp (x 1)
    let g : Fin 1 → EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun _ x => (x 0) ^ 2 / x 1
    Set.Nonempty {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin 2), x 1 ≠ 0 ∧ g 0 x ≤ 0 ∧ f x = r} ∧
    BddBelow {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin 2), x 1 ≠ 0 ∧ g 0 x ≤ 0 ∧ f x = r} ∧
    sInf {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin 2), x 1 ≠ 0 ∧ g 0 x ≤ 0 ∧ f x = r} = 0 ∧
    ¬ ∃ xStar : EuclideanSpace ℝ (Fin 2),
      xStar 1 ≠ 0 ∧
      g 0 xStar ≤ 0 ∧
      (∀ x : EuclideanSpace ℝ (Fin 2), x 1 ≠ 0 → g 0 x ≤ 0 → f xStar ≤ f x) ∧
      KarushKuhnTuckerConditions f g xStar := by
  sorry


end «problem-138»
