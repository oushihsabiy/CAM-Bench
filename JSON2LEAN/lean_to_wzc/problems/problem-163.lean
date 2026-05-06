import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-163»
/-
maximize & \sum_{j = 1}^n log fⱼ; subject to & fⱼ > 0, j = 1, ..., n,; & Rf < c
-/
structure NetworkUtilityMaximizationProblem where
  n : ℕ
  R : Matrix (Fin n) (Fin n) ℝ
  c : Fin n → ℝ
  objective : (Fin n → ℝ) → ℝ := fun f => ∑ j : Fin n, Real.log (f j)
  feasible : (Fin n → ℝ) → Prop := fun f =>
    (∀ j : Fin n, 0 < f j) ∧
      (∀ i : Fin n, (∑ j : Fin n, R i j * f j) < c i)

def NetworkUtilityMaximizationProblem.is_feasible (p : NetworkUtilityMaximizationProblem) :
    (Fin p.n → ℝ) → Prop :=
  p.feasible

/-
Let m, n ∈ ℕ, let R ∈ ℝ^{m × n} satisfy R_{ij} = cases 1, & if flow j passes through link i,; 0, &
otherwise, cases and let c = (c₁, ..., cₘ) ∈ ℝ^m satisfy cᵢ > 0 for all i. Define F = {f∈ ℝ^n | fⱼ >
0 for all j and (Rf)_i < cᵢ for all i = 1, ..., m}. Assume F is nonempty, and define U(f) = \sum_{j
=
1}^n log fⱼ (f∈ F). Define U^{max} = sup_{f∈ F} U(f). Prove that the flow rates maximizing the
utility, ignoring latency, are exactly the optimal solutions of the network utility maximization
problem, and that its optimal value is U^{max}.
-/
theorem network_utility_maximizers_are_exactly_optimal_solutions
    (n : ℕ)
    (R : Matrix (Fin n) (Fin n) ℝ)
    (hR01 : ∀ i : Fin n, ∀ j : Fin n, R i j = 0 ∨ R i j = 1)
    (c : Fin n → ℝ)
    (h_c_pos : ∀ i : Fin n, 0 < c i)
    (h_nonempty : ∃ f : Fin n → ℝ,
      (∀ j : Fin n, 0 < f j) ∧ ∀ i : Fin n, (∑ j : Fin n, R i j * f j) < c i)
    (hUmax_spec :
      let p : NetworkUtilityMaximizationProblem := { n := n, R := R, c := c }
      let Umax : ℝ := sSup (p.objective '' {f | p.is_feasible f})
      ∀ f : Fin n → ℝ,
        p.is_feasible f →
          ((p.objective f = Umax) ↔
            ∀ g : Fin n → ℝ, p.is_feasible g → p.objective g ≤ p.objective f)) :
    let p : NetworkUtilityMaximizationProblem := { n := n, R := R, c := c }
    let Umax : ℝ := sSup (p.objective '' {f | p.is_feasible f})
    (∀ f : Fin n → ℝ,
        p.is_feasible f →
          ((p.objective f = Umax) ↔
            (∀ g : Fin n → ℝ, p.is_feasible g → p.objective g ≤ p.objective f))) := by
  sorry

end «problem-163»
