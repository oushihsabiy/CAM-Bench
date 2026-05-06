import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-13»
/-
Exercise 8.11 | 12 | defn

The damped Newton method uses the Newton direction δx^{(k)} = −(∇²f(x^{(k)}))⁻¹ ∇f(x^{(k)}) and
updates x^{(k + 1)} = x^{(k)} + t^{(k)}δx^{(k)}, where t^{(k)} ∈ (0, 1].
-/

def ScalarNewtonMethod
    (f : ℝ → ℝ) (deriv : ℝ → ℝ) (secondDeriv : ℝ → ℝ)
    (xStar x0 : ℝ) (hx0_lt_xStar : x0 < xStar) : ℕ → ℝ
  | 0 => x0
  | k + 1 => ScalarNewtonMethod f deriv secondDeriv xStar x0 hx0_lt_xStar k
      - deriv (ScalarNewtonMethod f deriv secondDeriv xStar x0 hx0_lt_xStar k) /
          secondDeriv (ScalarNewtonMethod f deriv secondDeriv xStar x0 hx0_lt_xStar k)

def ScalarNewtonDirection
    (deriv : ℝ → ℝ) (secondDeriv : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv x / secondDeriv x

def ScalarFullNewtonArmijo
    (f : ℝ → ℝ) (deriv : ℝ → ℝ) (secondDeriv : ℝ → ℝ) (α x : ℝ) : Prop :=
  let d := ScalarNewtonDirection deriv secondDeriv x
  f (x + d) ≤ f x + α * deriv x * d

/-
Exercise 8.11 | 16 | algo

The damped Newton method with backtracking line search is defined by δx^{(k)} = - f′(x^{(k)}) /
f″(x^{(k)}), x^{(k + 1)} = x^{(k)} + t^{(k)}δx^{(k)}, where t^{(k)} ∈ (0, 1] is the first element of
the sequence 1, β, β², …, with fixed α ∈ (0, 1/2) and β ∈ (0, 1), such that f(x^{(k)} +
t^{(k)}δx^{(k)}) ≤ f(x^{(k)}) + α t^{(k)} f′(x^{(k)})δx^{(k)}.
-/
structure ScalarDampedNewtonBacktracking where
  f : ℝ → ℝ
  deriv : ℝ → ℝ
  secondDeriv : ℝ → ℝ
  α : ℝ
  β : ℝ
  x0 : ℝ
  hα : 0 < α ∧ α < (1 / 2 : ℝ)
  hβ : 0 < β ∧ β < 1
  x : ℕ → ℝ
  t : ℕ → ℝ
  hx0 : x 0 = x0
  ht_bounds : ∀ k : ℕ, 0 < t k ∧ t k ≤ 1
  hstep : ∀ k : ℕ,
    x (k + 1) = x k + t k * (-deriv (x k) / secondDeriv (x k))
  ht_first : ∀ k : ℕ,
    ∃ m : ℕ,
      t k = β ^ m ∧
      f (x k + t k * (-deriv (x k) / secondDeriv (x k))) ≤
        f (x k) + α * t k * deriv (x k) * (-deriv (x k) / secondDeriv (x k)) ∧
      ∀ j : ℕ, j < m →
        ¬ (f (x k + (β ^ j) * (-deriv (x k) / secondDeriv (x k))) ≤
            f (x k) + α * (β ^ j) * deriv (x k) * (-deriv (x k) / secondDeriv (x k)))

def ScalarDampedNewtonBacktracking.direction (N : ScalarDampedNewtonBacktracking) (x : ℝ) : ℝ :=
  -N.deriv x / N.secondDeriv x

def ScalarDampedNewtonBacktracking.armijoAt (N : ScalarDampedNewtonBacktracking) (x : ℝ)
    (t : ℝ) : Prop :=
  N.f (x + t * N.direction x) ≤ N.f x + N.α * t * N.deriv x * N.direction x

def ScalarDampedNewtonBacktracking.stepSize (N : ScalarDampedNewtonBacktracking) (x : ℝ) : Prop :=
  ∃ k : ℕ,
    let t : ℝ := N.β ^ k
    N.armijoAt x t ∧
      ∀ j : ℕ, j < k → ¬N.armijoAt x (N.β ^ j)

def ScalarDampedNewtonBacktracking.step (N : ScalarDampedNewtonBacktracking) (x : ℝ)
    (t : ℝ) : ℝ :=
  x + t * N.direction x

def ScalarDampedNewtonBacktracking.iterate (N : ScalarDampedNewtonBacktracking)
    (stepSize : ℕ → ℝ) : ℕ → ℝ
  | 0 => N.x0
  | k + 1 => N.step (N.iterate stepSize k) (stepSize k)

/-
Let f: ℝ→ℝ be a C^{3} function that is strongly convex and smooth on ℝ, and assume that f'''(x) ≤ 0
for all x∈ ℝ. Let x*∈ ℝ be the minimizer of f. Since f is strongly convex, x* is unique, f'(x*) = 0,
and f''(x) > 0 for all x∈ℝ. Define Newton's method by x^{(k + 1)} =
x^{(k)} - \frac{f'(x^{(k)})}{f''(x^{(k)})}, k = 0, 1, 2, ..., with initial point x^{(0)} < x*. Also
define damped Newton backtracking by δ x^{(k)} = - \frac{f'(x^{(k)})}{f''(x^{(k)})}, x^{(k + 1)} =
x^{(k)} + t^{(k)}δ x^{(k)}, where t^{(k)}∈(0, 1] is the first element of the sequence 1, β, β^{2},
...,
with fixed α∈(0, 1/2) and β∈(0, 1), such that f(x^{(k)} + t^{(k)}δ x^{(k)}) ≤ f(x^{(k)}) + α t^{(k)}
f'(x^{(k)})δ x^{(k)}. Show that the Newton iterates x^{(k)} converge monotonically to x*, and that
t^{(k)} = 1 for all k. More precisely, each full Newton step is a nonnegative step that stays in
the interval (-∞, x*], satisfies the full-step Armijo condition, decreases the objective, and hence
is the first backtracking trial.
-/
theorem scalar_newton_monotone_converges_and_backtracking_unit_steps
    (f : ℝ → ℝ)
    (xStar x0 α β : ℝ)
    (hx0_lt_xStar : x0 < xStar)
    (hC3 : ContDiff ℝ 3 f)
    (hstrong_convex : ∃ m : ℝ, 0 < m ∧ ∀ x : ℝ, m ≤ deriv^[2] f x)
    (hsmooth : ∃ L : ℝ, 0 ≤ L ∧ ∀ x : ℝ, deriv^[2] f x ≤ L)
    (hthird_nonpos : ∀ x : ℝ, deriv^[3] f x ≤ 0)
    (hminimizer : ∀ x : ℝ, f xStar ≤ f x)
    (hderiv_xStar : deriv f xStar = 0)
    (hsecond_pos : ∀ x : ℝ, 0 < deriv^[2] f x)
    (hα : 0 < α ∧ α < (1 / 2 : ℝ))
    (hβ : 0 < β ∧ β < 1) :
    (∀ k : ℕ,
      let xk := ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar k
      let xnext := ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar (k + 1)
      let dk := ScalarNewtonDirection (deriv f) (deriv^[2] f) xk
      x0 ≤ xk ∧
      xk ≤ xStar ∧
      deriv f xk ≤ 0 ∧
      xk ≤ xnext ∧
      xnext ≤ xStar ∧
      0 < (deriv^[2] f) xk ∧
      0 ≤ dk ∧
      xnext = xk + dk ∧
      ScalarFullNewtonArmijo f (deriv f) (deriv^[2] f) α xk ∧
      f xStar ≤ f xnext ∧
      f xnext ≤ f xk) ∧
    Tendsto (ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar) atTop (𝓝 xStar) ∧
    -- backtracking always accepts the full Newton step (t^(k) = 1 for all k)
    (∀ N : ScalarDampedNewtonBacktracking,
      N.f = f →
      N.deriv = deriv f →
      N.secondDeriv = deriv^[2] f →
      N.α = α →
      N.β = β →
      N.x0 = x0 →
      N.x = ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar →
      ∀ k : ℕ, N.t k = 1) := by
  sorry

end «problem-13»
