import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-98»
/-
For a minimization problem with optimal value p*, a scalar M is a lower bound, or lower - bound
estimate, if M ≤ p*.
-/
def IsLowerBoundEstimate (pStar M : ℝ) : Prop := M ≤ pStar

/-
Consider the optimization problem min_{x ∈ ℝ^n} f(x) ext{s. t.} cᵢ(x) = 0, i ∈ E, where E is the
index set of equality constraints and cᵢ: ℝ^n o ℝ are continuous functions.
-/
structure EqualityConstrainedOptimizationProblem where
  n : ℕ
  E : Type
  eq_constraints : Set E
  finite_eq_constraints : eq_constraints.Finite
  f : (Fin n → ℝ) → ℝ
  c : E → (Fin n → ℝ) → ℝ
  continuous_f : Continuous f
  continuous_c : ∀ i : E, Continuous (c i)

def EqualityConstrainedOptimizationProblem.isFeasible
    (p : EqualityConstrainedOptimizationProblem) (x : Fin p.n → ℝ) : Prop :=
  ∀ i ∈ p.eq_constraints, p.c i x = 0

def EqualityConstrainedOptimizationProblem.objectiveValue
    (p : EqualityConstrainedOptimizationProblem) (x : Fin p.n → ℝ) : ℝ :=
  p.f x

/-
The Morrison method is defined iteratively as follows: for each k, let x^k = argmin_{x ∈ ℝ^n} v(Mₖ,
x), and update M_{k + 1} = Mₖ + sqrt(v(Mₖ, x^k)).
-/
structure MorrisonMethod where
  problem : EqualityConstrainedOptimizationProblem
  v : ℝ → (Fin problem.n → ℝ) → ℝ
  M : ℕ → ℝ
  x : ℕ → Fin problem.n → ℝ
  v_nonneg : ∀ M x, 0 ≤ v M x
  x_is_argmin : ∀ k : ℕ, IsMinOn (v (M k)) Set.univ (x k)
  updateStep : ∀ k : ℕ, M (k + 1) = M k + Real.sqrt (v (M k) (x k))

def MorrisonMethod.stepValue (mm : MorrisonMethod) (k : ℕ) : ℝ :=
  mm.v (mm.M k) (mm.x k)

def MorrisonMethod.nextM (mm : MorrisonMethod) (k : ℕ) : ℝ :=
  mm.M k + Real.sqrt (mm.stepValue k)

/-
Consider the equality - constrained optimization problem. Let x* be an optimal solution of this
problem, so f(x*) is the optimal value. Given a lower - bound estimate M of the optimal value
satisfying M ≤ f(x*), define the auxiliary function v(M, x) = [f(x) - M]^2 + \sum_{i∈ E} cᵢ^2(x).
The
Morrison method is defined iteratively as follows: for each k, let x^k = argmin_{x ∈ ℝ^n} v(Mₖ, x),
and update M_{k + 1} = Mₖ + sqrt(v(Mₖ, x^k)). Prove that if at some iteration Mₖ ≤ f(x*), then necessarily
M_{k + 1} ≤ f(x*).
-/
theorem MorrisonMethod_nextM_le_optimal_of_current_le_optimal
    (mm : MorrisonMethod)
    (k : ℕ)
    (xStar : Fin mm.problem.n → ℝ)
    (hxStar_feasible : mm.problem.isFeasible xStar)
    (hxStar_optimal : ∀ x : Fin mm.problem.n → ℝ,
      mm.problem.isFeasible x → mm.problem.f xStar ≤ mm.problem.f x)
    (hv : ∀ M : ℝ, ∀ x : Fin mm.problem.n → ℝ,
      mm.v M x =
        (mm.problem.f x - M) ^ 2 +
          ∑' i, by
            classical
            exact if i ∈ mm.problem.eq_constraints then (mm.problem.c i x) ^ 2 else 0)
    (hMlb : IsLowerBoundEstimate (mm.problem.f xStar) (mm.M k)) :
    mm.nextM k ≤ mm.problem.f xStar := by
  classical
  -- Compare the chosen iterate with the feasible reference point `xStar` via the argmin property.
  have hstep_le_v : mm.stepValue k ≤ mm.v (mm.M k) xStar := by
    simpa [MorrisonMethod.stepValue] using
      (isMinOn_iff.mp (mm.x_is_argmin k)) xStar (by simp)
  -- Each penalty summand vanishes at a feasible point because all equality constraints are zero there.
  have hpenalty_term_zero :
      ∀ i : mm.problem.E,
        (if i ∈ mm.problem.eq_constraints then (mm.problem.c i xStar) ^ 2 else 0) = 0 := by
    intro i
    by_cases hi : i ∈ mm.problem.eq_constraints
    · simp [hi, hxStar_feasible i hi]
    · simp [hi]
  -- Hence the whole penalty series is the zero series.
  have hpenalty_tsum_zero :
      (∑' i, if i ∈ mm.problem.eq_constraints then (mm.problem.c i xStar) ^ 2 else 0) = 0 := by
    have hzero_fun :
        (fun i : mm.problem.E =>
          if i ∈ mm.problem.eq_constraints then (mm.problem.c i xStar) ^ 2 else 0) =
        fun _ : mm.problem.E => (0 : ℝ) := by
      funext i
      exact hpenalty_term_zero i
    rw [hzero_fun]
    exact (tsum_zero : ∑' i : mm.problem.E, (0 : ℝ) = 0)
  -- Rewriting `v` at `xStar` leaves only the squared objective gap.
  have hv_xStar : mm.v (mm.M k) xStar = (mm.problem.f xStar - mm.M k) ^ 2 := by
    rw [hv, hpenalty_tsum_zero]
    simp
  -- The lower-bound hypothesis makes the objective gap nonnegative, so the square root simplifies cleanly.
  have hgap_nonneg : 0 ≤ mm.problem.f xStar - mm.M k := by
    exact sub_nonneg.mpr (by simpa [IsLowerBoundEstimate] using hMlb)
  -- Transport the comparison through `sqrt` to bound the next update increment.
  have hsqrt_le : Real.sqrt (mm.stepValue k) ≤ mm.problem.f xStar - mm.M k := by
    have hsq_le : mm.stepValue k ≤ (mm.problem.f xStar - mm.M k) ^ 2 := by
      calc
        mm.stepValue k ≤ mm.v (mm.M k) xStar := hstep_le_v
        _ = (mm.problem.f xStar - mm.M k) ^ 2 := hv_xStar
    calc
      Real.sqrt (mm.stepValue k) ≤ Real.sqrt ((mm.problem.f xStar - mm.M k) ^ 2) :=
        Real.sqrt_le_sqrt hsq_le
      _ = |mm.problem.f xStar - mm.M k| := Real.sqrt_sq_eq_abs _
      _ = mm.problem.f xStar - mm.M k := abs_of_nonneg hgap_nonneg
  -- Expanding `nextM` turns the bound on the increment into the desired bound on the updated lower estimate.
  rw [MorrisonMethod.nextM]
  linarith

end «problem-98»
