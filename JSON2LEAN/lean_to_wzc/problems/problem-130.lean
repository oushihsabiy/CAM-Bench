import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-130»
/-
For an extended - real - valued function f: ℝ^n→ℝ + ∞, the perspective closure of (t, x)mapsto t
f(x/t) is
the extension defined by g(t, x) = t f(x/t) for t > 0, and by g(0, x) = liminf_τdownarrow 0, y→ x τ
f(y/τ). For the exponential power term used below, on the domain x ≥ 0 this gives g(0, 0) = 0
and g(0, x) = +∞ for x > 0; negative x is intentionally kept outside the convex-program domain.
-/
def perspectiveClosure (f : ℝ → EReal) : ℝ → ℝ → EReal
  | t, x =>
      if _ : 0 < t then
        (t : EReal) * f (x / t)
      else if _ : t = 0 then
        Filter.liminf
          (fun p : ℝ × ℝ => ((p.1 : EReal) * f (p.2 / p.1)))
          ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝 x))
      else
        ⊤

/-
If f: ℝ^n → ℝ + ∞, its perspective is the function g: (0, ∞)× ℝ^n→ ℝ + ∞ defined by g(t, x) = t
f(x/t),
t > 0.
-/
def perspective (f : ℝ → EReal) : {t : ℝ // 0 < t} → ℝ → EReal
  | t, x => ((t : ℝ) : EReal) * f (x / (t : ℝ))

def logScaleShift (n : ℕ) (T : ℝ) : EReal :=
  ∑ _ : Fin n, (Real.log T : EReal)

/-
Let n ∈ ℕ, let aᵢ > 0 for i = 1, ..., n, and let b > 0, T > 0, and P^{max}∈ℝ. Consider the
optimization problem in the variables r = (r₁, ..., rₙ)∈ℝ^n and t = (t₁, ..., tₙ)∈ℝ^n: maximize &
\sum_{i = 1}^n log rᵢ; subject to & (1)/(T)\sum_{i = 1}^n tᵢ aᵢ(e^{bTr_i/tᵢ} - 1) ≤ P^{max},; &
\sum_{i =
1}^n tᵢ = T,; & tᵢ ≥ 0 (i = 1, ..., n), where each term is interpreted via the perspective closure:
if tᵢ = 0 and rᵢ = 0, then tᵢ e^{bTr_i/tᵢ} = 0, while if tᵢ = 0 and rᵢ > 0, the power is + ∞.
-/
structure TimeAllocationPowerMaximization where
  n : ℕ
  n_pos : 0 < n
  a : Fin n → ℝ
  a_pos : ∀ i, 0 < a i
  b : ℝ
  b_pos : 0 < b
  T : ℝ
  T_pos : 0 < T
  Pmax : ℝ

def TimeAllocationPowerMaximization.powerTerm
    (P : TimeAllocationPowerMaximization)
    (t r : Fin P.n → ℝ)
    (i : Fin P.n) : EReal :=
  perspectiveClosure
    (fun x => ((P.a i) : EReal) * (EReal.exp (P.b * P.T * x) - 1))
    (t i) (r i)

def TimeAllocationPowerMaximization.totalPower
    (P : TimeAllocationPowerMaximization)
    (t r : Fin P.n → ℝ) : EReal :=
  ((P.T : EReal)⁻¹) * ∑ i, P.powerTerm t r i

def TimeAllocationPowerMaximization.timeConstraint
    (P : TimeAllocationPowerMaximization)
    (t : Fin P.n → ℝ) : Prop :=
  ∑ i, t i = P.T

def TimeAllocationPowerMaximization.nonnegativeTimes
    (P : TimeAllocationPowerMaximization)
    (t : Fin P.n → ℝ) : Prop :=
  ∀ i, 0 ≤ t i

def TimeAllocationPowerMaximization.positiveRates
    (P : TimeAllocationPowerMaximization)
    (r : Fin P.n → ℝ) : Prop :=
  ∀ i, 0 < r i

def TimeAllocationPowerMaximization.feasible
    (P : TimeAllocationPowerMaximization)
    (r t : Fin P.n → ℝ) : Prop :=
  P.totalPower t r ≤ P.Pmax ∧ P.timeConstraint t ∧ P.nonnegativeTimes t

def TimeAllocationPowerMaximization.objective
    (P : TimeAllocationPowerMaximization)
    (r : Fin P.n → ℝ) : EReal :=
  if _ : ∀ i, 0 < r i then
    ∑ i, (Real.log (r i) : EReal)
  else
    ⊥

/-
minimize & - \sum_{i = 1}^n log xᵢ; subject to & (1)/(T)\sum_{i = 1}^n aᵢ(tᵢ e^{b xᵢ/tᵢ} - tᵢ) ≤
P^{max},; & \sum_{i = 1}^n tᵢ = T,; & tᵢ ≥ 0 (i = 1, ..., n),; & xᵢ > 0 (i = 1, ..., n), where xᵢ =
T
rᵢ for i = 1, ..., n.
-/
structure ConvexReformulatedProgram where
  n : ℕ
  n_pos : 0 < n
  a : Fin n → ℝ
  a_pos : ∀ i, 0 < a i
  b : ℝ
  b_pos : 0 < b
  T : ℝ
  T_pos : 0 < T
  Pmax : ℝ

def ConvexReformulatedProgram.powerTerm
    (P : ConvexReformulatedProgram)
    (t x : Fin P.n → ℝ)
    (i : Fin P.n) : EReal :=
  perspectiveClosure
    (fun y => ((P.a i) : EReal) * (EReal.exp (P.b * y) - 1))
    (t i) (x i)

def ConvexReformulatedProgram.totalPower
    (P : ConvexReformulatedProgram)
    (t x : Fin P.n → ℝ) : EReal :=
  ((P.T : EReal)⁻¹) * ∑ i, P.powerTerm t x i

def ConvexReformulatedProgram.timeConstraint
    (P : ConvexReformulatedProgram)
    (t : Fin P.n → ℝ) : Prop :=
  ∑ i, t i = P.T

def ConvexReformulatedProgram.nonnegativeTimes
    (P : ConvexReformulatedProgram)
    (t : Fin P.n → ℝ) : Prop :=
  ∀ i, 0 ≤ t i

def ConvexReformulatedProgram.positiveVariables
    (P : ConvexReformulatedProgram)
    (x : Fin P.n → ℝ) : Prop :=
  ∀ i, 0 < x i

def ConvexReformulatedProgram.feasible
    (P : ConvexReformulatedProgram)
    (x t : Fin P.n → ℝ) : Prop :=
  P.totalPower t x ≤ P.Pmax ∧
    P.timeConstraint t ∧
    P.nonnegativeTimes t ∧
    P.positiveVariables x

def ConvexReformulatedProgram.objective
    (P : ConvexReformulatedProgram)
    (x : Fin P.n → ℝ) : EReal :=
  -∑ i, (Real.log (x i) : EReal)

def ConvexReformulatedProgram.rateVariables
    (P : ConvexReformulatedProgram)
    (x : Fin P.n → ℝ)
    (i : Fin P.n) : ℝ :=
  x i / P.T

/-
Let n ∈ ℕ, let aᵢ > 0 for i = 1, ..., n, and let b > 0, T > 0, and P^{max}∈ℝ. Consider the
optimization problem time allocation power maximization. Prove that this problem is equivalent to
the convex optimization problem convex reformulated program.
-/
theorem timeAllocationPowerMaximization_equiv_convexReformulatedProgram
    (p : TimeAllocationPowerMaximization) :
    ∃ q : ConvexReformulatedProgram,
      ∃ hqn : q.n = p.n,
        (∀ i : Fin q.n, q.a i = p.a (Fin.cast hqn i)) ∧
        q.b = p.b ∧
        q.T = p.T ∧
        q.Pmax = p.Pmax ∧
        (∀ r t : Fin p.n → ℝ,
          q.feasible
              (fun i : Fin q.n => p.T * r (Fin.cast hqn i))
              (fun i : Fin q.n => t (Fin.cast hqn i)) ↔
            p.feasible r t ∧ p.positiveRates r) ∧
        (∀ x t : Fin q.n → ℝ,
          p.feasible
              (fun i : Fin p.n => x (Fin.cast hqn.symm i) / p.T)
              (fun i : Fin p.n => t (Fin.cast hqn.symm i)) ∧
            p.positiveRates (fun i : Fin p.n => x (Fin.cast hqn.symm i) / p.T) ↔
            q.feasible x t) ∧
        (∀ r : Fin p.n → ℝ,
          p.positiveRates r →
            q.objective (fun i : Fin q.n => p.T * r (Fin.cast hqn i)) =
              -p.objective r - logScaleShift p.n p.T) ∧
        (∀ x : Fin q.n → ℝ,
          q.positiveVariables x →
            p.objective (fun i : Fin p.n => x (Fin.cast hqn.symm i) / p.T) =
              -q.objective x - logScaleShift q.n q.T) ∧
        (∀ v : EReal,
          (∃ r t : Fin p.n → ℝ,
            p.feasible r t ∧ p.positiveRates r ∧ p.objective r = v) ↔
            ∃ x t : Fin q.n → ℝ,
              q.feasible x t ∧ q.objective x = -v - logScaleShift p.n p.T) ∧
        ((∃ r t : Fin p.n → ℝ,
            p.feasible r t ∧
            p.positiveRates r ∧
            ∀ r' t' : Fin p.n → ℝ,
              p.feasible r' t' ∧ p.positiveRates r' →
                p.objective r' ≤ p.objective r) ↔
          ∃ x t : Fin q.n → ℝ,
            q.feasible x t ∧
            ∀ x' t' : Fin q.n → ℝ,
              q.feasible x' t' →
                q.objective x ≤ q.objective x') := by
  sorry

/-
Let n ∈ ℕ, let aᵢ > 0 for i = 1, ..., n, and let b > 0, T > 0, and P^{max}∈ℝ. Consider the convex
optimization problem convex reformulated program. Prove also that the objective - \sum_{i = 1}^n log
xᵢ is convex and that the constraint function (t, x) mapsto (1)/(T)\sum_{i = 1}^n aᵢ(tᵢ e^{b
xᵢ/tᵢ} - tᵢ) is convex on the domain tᵢ ≥ 0, xᵢ ≥ 0, so the reformulated problem is a convex
optimization problem. The final feasible set uses xᵢ > 0 for the logarithmic objective and the
time-allocation equality; the perspective power term is evaluated through its lower-semicontinuous
closure at tᵢ = 0, so no division by zero occurs.
-/
theorem convexReformulatedProgram_isConvexOptimization
    (p : ConvexReformulatedProgram) :
    ConvexOn ℝ
      { x : Fin p.n → ℝ | ∀ i, 0 < x i }
      (fun x : Fin p.n → ℝ => -∑ i, Real.log (x i)) ∧
    (∀ x : Fin p.n → ℝ,
      p.positiveVariables x →
        p.objective x = (((-∑ i, Real.log (x i)) : ℝ) : EReal)) ∧
    let D : Set ((Fin p.n → ℝ) × (Fin p.n → ℝ)) :=
      { z | p.nonnegativeTimes z.1 ∧ ∀ i, 0 ≤ z.2 i }
    Convex ℝ D ∧
    ∀ z z' : (Fin p.n → ℝ) × (Fin p.n → ℝ), ∀ θ : ℝ,
      z ∈ D →
      z' ∈ D →
      0 ≤ θ →
      θ ≤ 1 →
      p.totalPower
          (fun i => θ * z.1 i + (1 - θ) * z'.1 i)
          (fun i => θ * z.2 i + (1 - θ) * z'.2 i) ≤
        ((θ : EReal) * p.totalPower z.1 z.2 +
          ((1 - θ : ℝ) : EReal) * p.totalPower z'.1 z'.2) ∧
    let feasibleSet : Set ((Fin p.n → ℝ) × (Fin p.n → ℝ)) :=
      { z |
        p.timeConstraint z.1 ∧
        p.nonnegativeTimes z.1 ∧
        p.positiveVariables z.2 ∧
        p.totalPower z.1 z.2 ≤ p.Pmax }
    Convex ℝ feasibleSet := by
  sorry

end «problem-130»
