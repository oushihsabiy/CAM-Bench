import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-68»
/-
For functions h₀, f₁, ..., fₘ: ℝ^n → ℝ, the dual function is the map g: ℝ^m → ℝ - ∞ defined by g(μ)
=
\inf_{x∈ ℝ^n}(h₀(x) + \sum_{i = 1}^m μ_i fᵢ(x)).
-/
open scoped BigOperators

def dualFunction {n m : ℕ} (h₀ : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ) :
    (Fin m → ℝ) → EReal :=
  fun μ =>
    sInf {r : EReal | ∃ x : Fin n → ℝ, r = ((h₀ x + ∑ i, μ i * f i x : ℝ) : EReal)}

/-
A vector μ∈ ℝ^m is dual feasible if μ_i ≥ 0 for each i = 1, ..., m.
-/
def DualFeasible {m : ℕ} (μ : Fin m → ℝ) : Prop :=
  ∀ i, 0 ≤ μ i

/-
Consider a problem of the form minimize & h₀(x); subject toquad & fᵢ(x) ≤ 0, i = 1, ..., m.
-/
structure ConvexInequalityConstrainedProblem (n m : ℕ) where
  h₀ : (Fin n → ℝ) → ℝ
  f : Fin m → (Fin n → ℝ) → ℝ

def ConvexInequalityConstrainedProblem.IsFeasible {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m) (x : Fin n → ℝ) : Prop :=
  ∀ i, P.f i x ≤ 0

def ConvexInequalityConstrainedProblem.objective {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m) (x : Fin n → ℝ) : ℝ :=
  P.h₀ x

def ConvexInequalityConstrainedProblem.dualFunction {n m : ℕ}
    (_ : ConvexInequalityConstrainedProblem n m) : (Fin m → ℝ) → EReal :=
  fun _ => 0

def ConvexInequalityConstrainedProblem.DualFeasible {n m : ℕ}
    (_ : ConvexInequalityConstrainedProblem n m) (μ : Fin m → ℝ) : Prop :=
  ∀ i, 0 ≤ μ i

/-
Consider the convex optimization problems minimize & f₀(x); subject toquad & fᵢ(x) ≤ 0, i =
1, ..., m, 13 and minimize & f̃_0(x) = exp(f₀(x)); subject toquad & fᵢ(x) ≤ 0, i = 1, ..., m, 14
where fᵢ: ℝ^n→ℝ for i = 0, 1, ..., m are convex and differentiable.
-/
structure ExponentialObjectiveConvexProblem (n m : ℕ) where
  f₀ : (Fin n → ℝ) → ℝ
  f : Fin m → (Fin n → ℝ) → ℝ

def ExponentialObjectiveConvexProblem.baseProblem {n m : ℕ}
    (P : ExponentialObjectiveConvexProblem n m) : ConvexInequalityConstrainedProblem n m :=
  { h₀ := P.f₀
    f := P.f }

def ExponentialObjectiveConvexProblem.exponentialObjective {n m : ℕ}
    (P : ExponentialObjectiveConvexProblem n m) : (Fin n → ℝ) → ℝ :=
  fun x => Real.exp (P.f₀ x)

def ExponentialObjectiveConvexProblem.exponentialProblem {n m : ℕ}
    (P : ExponentialObjectiveConvexProblem n m) : ConvexInequalityConstrainedProblem n m :=
  { h₀ := P.exponentialObjective
    f := P.f }

def ExponentialObjectiveConvexProblem.IsFeasible {n m : ℕ}
    (P : ExponentialObjectiveConvexProblem n m) (x : Fin n → ℝ) : Prop :=
  P.baseProblem.IsFeasible x

/-
Let L(x, λ) = f₀(x) + \sum_{i = 1}^m λ_i fᵢ(x), tilde L(x, tildeλ) = exp(f₀(x)) + \sum_{i = 1}^m
tildeλ_i fᵢ(x). For a convex inequality - constrained problem, its dual function is g(μ) = \inf_{x∈
ℝ^n}(h₀(x) + \sum_{i = 1}^m μ_i fᵢ(x)), and μ∈ ℝ^m is dual feasible if μ_i ≥ 0 for i = 1, ..., m.
Consider convex programs (13) and (14). Suppose λ is dual feasible for problem (13), and bar x
minimizes f₀(x) + \sum_{i = 1}^m λ_i fᵢ(x). Show that, for an appropriate choice of tildeλ, the
point
bar x also minimizes exp(f₀(x)) + \sum_{i = 1}^m tildeλ_i fᵢ(x), and that tildeλ is dual feasible
for
problem (14).
-/
theorem exp_reweighted_lagrangian_minimizer
    {n m : ℕ} (P : ExponentialObjectiveConvexProblem n m) (lam : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hf₀_convex : ConvexOn ℝ Set.univ P.f₀)
    (hf_convex : ∀ i, ConvexOn ℝ Set.univ (P.f i))
    (hf₀_differentiable : Differentiable ℝ P.f₀)
    (hf_differentiable : ∀ i, Differentiable ℝ (P.f i))
    (hlam : P.baseProblem.DualFeasible lam)
    (hmin :
      ∀ x : Fin n → ℝ,
        P.f₀ xbar + ∑ i, lam i * P.f i xbar ≤ P.f₀ x + ∑ i, lam i * P.f i x)
    : ∃ lam_tilde : Fin m → ℝ,
        P.exponentialProblem.DualFeasible lam_tilde ∧
          ∀ x : Fin n → ℝ,
            Real.exp (P.f₀ xbar) + ∑ i, lam_tilde i * P.f i xbar ≤
              Real.exp (P.f₀ x) + ∑ i, lam_tilde i * P.f i x := by
  sorry

end «problem-68»
