import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-45»
/-
For a problem with objective function f₀ and inequality constraint functions fᵢ, the dual function
is the map g: ℝ^m → ℝ cup {- ∞} defined by g(λ) = inf_x∈ ℝ^n(f₀(x) + sum_i = 1^m λ_i fᵢ(x)).
-/
def dualFeasible {m : ℕ} (lam : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, 0 ≤ lam i

/-
For t > 0, the centering problem is to minimize the logarithmic barrier objective x mapsto t
f₀(x) - sum_i = 1^m log(- fᵢ(x)) over the strict feasible set {x∈ ℝ^n| fᵢ(x) < 0 ∀ i}.
-/
def strictFeasibleSet {α : Type*} {m : ℕ} (fi : Fin m → α → ℝ) : Set α :=
  {x | ∀ i : Fin m, fi i x < 0}

def centeringObjective {α : Type*} {m : ℕ} (t : ℝ) (f0 : α → ℝ)
    (fi : Fin m → α → ℝ) (x : α) : EReal :=
  if _ : 0 < t then
    if _ : ∀ i : Fin m, fi i x < 0 then
      (t * f0 x : EReal) - ∑ i : Fin m, (Real.log (-fi i x) : EReal)
    else
      ⊤
  else
    ⊤

/-
Given inequality constraint functions fᵢ, the logarithmic barrier is the extended - real - valued
function B defined by B(x) = - sum_i = 1^m log(- fᵢ(x)) for points satisfying fᵢ(x) < 0 for all i,
and
B(x) = + ∞ otherwise.
-/
structure ConvexInequalityConstrainedProblem (m : ℕ) where
  n : ℕ
  f0 : (Fin n → ℝ) → ℝ
  fi : Fin m → (Fin n → ℝ) → ℝ

def ConvexInequalityConstrainedProblem.isFeasible {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) (x : Fin P.n → ℝ) : Prop :=
  ∀ i : Fin m, P.fi i x ≤ 0

def ConvexInequalityConstrainedProblem.feasibleSet {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) : Set (Fin P.n → ℝ) :=
  {x | P.isFeasible x}

def ConvexInequalityConstrainedProblem.objective {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) : (Fin P.n → ℝ) → ℝ :=
  P.f0

/-
Its dual problem is maximize & g(λ); subject to & λ_i ≥ 0, i = 1, ..., m. array
-/
theorem centeringObjective_bounded_below_on_strictFeasibleSet
    {m : ℕ} (P : ConvexInequalityConstrainedProblem m)
    (hf0_convex : ConvexOn ℝ Set.univ P.f0)
    (hfi_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (P.fi i))
    (hlag_bounded :
      ∃ lam : Fin m → ℝ,
        dualFeasible lam ∧
        (∀ i : Fin m, 0 < lam i) ∧
        ∃ γ : ℝ, ∀ x : Fin P.n → ℝ,
          γ ≤ P.f0 x + ∑ i : Fin m, lam i * P.fi i x) :
    ∀ t : ℝ, 0 < t →
      ∃ C : EReal, ∀ x ∈ strictFeasibleSet P.fi, C ≤ centeringObjective t P.f0 P.fi x := by
  sorry

end «problem-45»
