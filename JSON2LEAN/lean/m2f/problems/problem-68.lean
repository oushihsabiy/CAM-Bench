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

/-- Scaling a componentwise nonnegative multiplier by a nonnegative scalar preserves
dual feasibility. -/
lemma dual_feasible_mul_nonneg {m : ℕ} {c : ℝ} (hc : 0 ≤ c) {μ : Fin m → ℝ}
    (hμ : ∀ i, 0 ≤ μ i) : ∀ i, 0 ≤ c * μ i := by
  -- Each component stays nonnegative under multiplication by a nonnegative scalar.
  intro i
  exact mul_nonneg hc (hμ i)

/-- Pulling a scalar out of a finite sum of weighted constraint values. -/
lemma scaled_sum_rewrite {m : ℕ} (c : ℝ) (μ : Fin m → ℝ) (g : Fin m → ℝ) :
    (∑ i, (c * μ i) * g i) = c * ∑ i, μ i * g i := by
  -- Distribute the scalar across the finite sum and reassociate each summand.
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring

/-- A first-order lower bound on the exponential transfers the original Lagrangian
comparison to the rescaled exponential objective. -/
lemma exp_linearization_bound {a b sbar s : ℝ} (h : a + sbar ≤ b + s) :
    Real.exp a + Real.exp a * sbar ≤ Real.exp b + Real.exp a * s := by
  have h_exp_nonneg : 0 ≤ Real.exp a := (Real.exp_pos a).le
  have h_tangent : Real.exp a + Real.exp a * (b - a) ≤ Real.exp b := by
    -- Apply `1 + t ≤ exp t` at `t = b - a`, then scale by `exp a`.
    have h_add_one := Real.add_one_le_exp (b - a)
    have h_mul := mul_le_mul_of_nonneg_left h_add_one h_exp_nonneg
    have h_mul' : Real.exp a * (1 + (b - a)) ≤ Real.exp a * Real.exp (b - a) := by
      simpa [add_comm] using h_mul
    calc
      Real.exp a + Real.exp a * (b - a) = Real.exp a * (1 + (b - a)) := by ring
      _ ≤ Real.exp a * Real.exp (b - a) := h_mul'
      _ = Real.exp b := by
        rw [← Real.exp_add]
        congr 1
        ring
  have h_shift : sbar ≤ (b - a) + s := by
    linarith
  have h_scaled_shift : Real.exp a * sbar ≤ Real.exp a * ((b - a) + s) := by
    -- Multiply the shifted inequality by the positive exponential factor.
    exact mul_le_mul_of_nonneg_left h_shift h_exp_nonneg
  -- Combine the tangent lower bound with the scaled comparison of constraint sums.
  calc
    Real.exp a + Real.exp a * sbar ≤ Real.exp a + Real.exp a * ((b - a) + s) := by
      linarith
    _ = (Real.exp a + Real.exp a * (b - a)) + Real.exp a * s := by ring
    _ ≤ Real.exp b + Real.exp a * s := by
      linarith [h_tangent]

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
  let lam_tilde : Fin m → ℝ := fun i => Real.exp (P.f₀ xbar) * lam i
  refine ⟨lam_tilde, ?_, ?_⟩
  · -- The rescaled multiplier remains dual feasible because the exponential factor is positive.
    intro i
    simpa [lam_tilde] using
      dual_feasible_mul_nonneg ((Real.exp_pos (P.f₀ xbar)).le) hlam i
  · -- Rewrite the original minimizer inequality in terms of the scaled constraint sums.
    intro x
    set sbar : ℝ := ∑ i, lam i * P.f i xbar
    set s : ℝ := ∑ i, lam i * P.f i x
    have hbase : P.f₀ xbar + sbar ≤ P.f₀ x + s := by
      simpa [sbar, s] using hmin x
    have hscalar :
        Real.exp (P.f₀ xbar) + Real.exp (P.f₀ xbar) * sbar ≤
          Real.exp (P.f₀ x) + Real.exp (P.f₀ xbar) * s :=
      exp_linearization_bound hbase
    have hsbar_rewrite :
        (∑ i, lam_tilde i * P.f i xbar) = Real.exp (P.f₀ xbar) * sbar := by
      -- Pull the common exponential factor out of the finite sum at `xbar`.
      simpa [lam_tilde, sbar, mul_assoc] using
        scaled_sum_rewrite (c := Real.exp (P.f₀ xbar)) (μ := lam) (g := fun i => P.f i xbar)
    have hs_rewrite :
        (∑ i, lam_tilde i * P.f i x) = Real.exp (P.f₀ xbar) * s := by
      -- The same factorization applies to the comparison point `x`.
      simpa [lam_tilde, s, mul_assoc] using
        scaled_sum_rewrite (c := Real.exp (P.f₀ xbar)) (μ := lam) (g := fun i => P.f i x)
    -- Substitute the scaled-sum identities into the scalar exponential bound.
    rw [hsbar_rewrite, hs_rewrite]
    exact hscalar

end «problem-68»
