import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-6»
/-
A point x^* is a strict local minimizer of f if there exists a neighborhood U of x^* such that f(x)
> f(x^ * ) for all x ∈ U ∖ {x^*}.
-/
def IsStrictLocalMin {X Y : Type*} [TopologicalSpace X] [Preorder Y] (f : X → Y) (xstar : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ xstar ∈ U ∧ ∀ ⦃x : X⦄, x ∈ U → x ≠ xstar → f xstar < f x


/-
Consider the unconstrained optimization problem min_(x ∈ ℝ^n) f(x), where f: ℝ^n → ℝ is twice
continuously differentiable in some open neighborhood of the point x^*.
-/
open scoped RealInnerProductSpace

/-- The second Fréchet derivative of the cubic vanishes at the origin. -/
lemma cubic_second_fderiv_at_zero :
    fderiv ℝ (fderiv ℝ (fun x : ℝ => x ^ 3)) 0 = 0 := by
  -- Differentiate the scalar coefficient in the explicit formula for the cubic derivative.
  have hcoeff : HasFDerivAt (fun y : ℝ => 3 * y ^ 2) (0 : ℝ →L[ℝ] ℝ) 0 := by
    simpa using (((hasDerivAt_pow 2 (0 : ℝ)).const_mul (3 : ℝ)).hasFDerivAt)
  -- Route correction: rewrite `fderiv` using the power rule before differentiating once more.
  have hsecond :
      HasFDerivAt (fun y : ℝ => fderiv ℝ (fun x : ℝ => x ^ 3) y)
        ((0 : ℝ →L[ℝ] ℝ).smulRight (ContinuousLinearMap.id ℝ ℝ)) 0 := by
    simpa [fderiv_pow_ring] using hcoeff.smul_const (ContinuousLinearMap.id ℝ ℝ)
  -- Identify the Fréchet derivative and then simplify the zero scalar action.
  calc
    fderiv ℝ (fderiv ℝ (fun x : ℝ => x ^ 3)) 0 =
        ContinuousLinearMap.smulRight (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) := hsecond.fderiv
    _ = 0 := by
      ext
      simp

/-- The cubic function is not a local minimum at the origin. -/
lemma cubic_not_isLocalMin_at_zero : ¬ IsLocalMin (fun x : ℝ => x ^ 3) 0 := by
  intro hlocal
  -- Unfold the local minimum statement into a neighborhood condition on the nonnegative sublevel set.
  have hnhds : {x : ℝ | 0 ≤ x ^ 3} ∈ 𝓝 (0 : ℝ) := by
    simpa [IsLocalMin, IsMinFilter] using hlocal
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hball⟩
  -- Pick a nearby negative point and force its cubic value to be negative.
  have hxmem : (-ε / 2 : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hxneg : (-ε / 2 : ℝ) - 0 < 0 := by nlinarith
    rw [abs_of_neg hxneg]
    nlinarith
  have hnonneg : 0 ≤ ((-ε / 2 : ℝ) ^ 3) := hball hxmem
  have hhalfpos : 0 < (ε / 2 : ℝ) := by nlinarith
  have hcube : 0 < (ε / 2 : ℝ) ^ 3 := by positivity
  have hpow : ((-ε / 2 : ℝ) ^ 3) = -((ε / 2 : ℝ) ^ 3) := by ring
  nlinarith [hnonneg, hcube, hpow]

theorem cubic_counterexample_not_local_min :
    ∃ (f : ℝ → ℝ) (xstar : ℝ),
      (∃ U : Set ℝ, U ∈ 𝓝 xstar ∧ ContDiffOn ℝ 2 f U) ∧
      HasFDerivAt f (0 : ℝ →L[ℝ] ℝ) xstar ∧
      (∀ v : ℝ, 0 ≤ (fderiv ℝ (fderiv ℝ f) xstar) v v) ∧
      ¬ IsLocalMin f xstar := by
  -- Use the cubic as the standard second-order necessary-condition counterexample.
  refine ⟨fun x : ℝ => x ^ 3, 0, ?_⟩
  constructor
  · -- The cubic is smooth on the whole real line, so any neighborhood of `0` works.
    refine ⟨Set.univ, by simp, ?_⟩
    simpa using (contDiff_id.pow 3).contDiffOn
  constructor
  · -- The first derivative vanishes at the origin because the cubic derivative is `3x^2`.
    convert ((hasDerivAt_pow 3 (0 : ℝ)).hasFDerivAt :
        HasFDerivAt (fun x : ℝ => x ^ 3)
          (ContinuousLinearMap.toSpanSingleton ℝ ((3 : ℝ) * 0 ^ (3 - 1))) 0) using 1
    ext
    simp
  constructor
  · -- The Hessian vanishes at the origin, so its quadratic form is nonnegative.
    intro v
    rw [cubic_second_fderiv_at_zero]
    simp
  · -- The cubic changes sign across the origin, so `0` cannot be a local minimum.
    exact cubic_not_isLocalMin_at_zero

/-
Consider the unconstrained minimization problem min_(x ∈ ℝ^n) f(x), where the function f: ℝ^n → ℝ is
twice continuously differentiable in some open neighborhood of the point x^*. The following
conclusions are known: if x^* is a local minimizer, then necessarily ∇ f(x^*) = 0, ∇^2 f(x^*) ⪰ 0.
If ∇ f(x^ * ) = 0, ∇^2 f(x^* ) ≻ 0, then x^* is a strict local minimizer. Here, ∇ f(x^*) denotes the
gradient of f at x^ * , and ∇^2 f(x^* ) denotes the Hessian matrix of f at x^*; ∇^2 f(x^*) ⪰ 0 means
that this matrix is positive semidefinite, and ∇^2 f(x^*) ≻ 0 means that this matrix is positive
definite. If there exists a neighborhood U of x^* such that f(x) ≥ f(x^*) for every x ∈ U, then x^*
is called a local minimizer; if f(x) > f(x^* ) for every x ∈ U∖{x^*}, then x^* is called a strict
local minimizer. Construct a function f and a point x^* such that x^* is a strict local minimizer,
but the positive definiteness requirement in the second - order sufficient condition is not
satisfied;
that is, it is not necessarily true that ∇ f(x^* ) = 0, ∇^2 f(x^*) ≻ 0. In other words, give an
example to show that a strict local minimizer does not necessarily have to satisfy that the Hessian
is positive definite at that point.
-/
/-- A nonzero real number has strictly positive fourth power. -/
lemma fourth_pow_pos_of_ne_zero {x : ℝ} (hx : x ≠ 0) : 0 < x ^ 4 := by
  -- Square once to get a positive quantity, then square again to match the fourth power.
  have hxsq : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hpos : 0 < (x ^ 2) ^ 2 := sq_pos_of_ne_zero hxsq
  calc
    0 < (x ^ 2) ^ 2 := hpos
    _ = x ^ 4 := by ring

/-- The second Fréchet derivative of the quartic vanishes at the origin. -/
lemma quartic_second_fderiv_at_zero :
    fderiv ℝ (fderiv ℝ (fun x : ℝ => x ^ 4)) 0 = 0 := by
  -- Differentiate the scalar coefficient in the explicit formula for the quartic derivative.
  have hcoeff : HasFDerivAt (fun y : ℝ => 4 * y ^ 3) (0 : ℝ →L[ℝ] ℝ) 0 := by
    simpa using (((hasDerivAt_pow 3 (0 : ℝ)).const_mul (4 : ℝ)).hasFDerivAt)
  -- Route correction: rewrite `fderiv` using the power rule before differentiating once more.
  have hsecond :
      HasFDerivAt (fun y : ℝ => fderiv ℝ (fun x : ℝ => x ^ 4) y)
        ((0 : ℝ →L[ℝ] ℝ).smulRight (ContinuousLinearMap.id ℝ ℝ)) 0 := by
    simpa [fderiv_pow_ring] using hcoeff.smul_const (ContinuousLinearMap.id ℝ ℝ)
  -- Identify the Fréchet derivative and then simplify the zero scalar action.
  calc
    fderiv ℝ (fderiv ℝ (fun x : ℝ => x ^ 4)) 0 =
        ContinuousLinearMap.smulRight (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) := hsecond.fderiv
    _ = 0 := by
      ext
      simp

theorem strict_local_minimizer_without_positive_definite_hessian :
    ∃ (f : ℝ → ℝ) (xstar : ℝ),
      (∃ U : Set ℝ, U ∈ 𝓝 xstar ∧ ContDiffOn ℝ 2 f U) ∧
      IsStrictLocalMin f xstar ∧
      HasFDerivAt f (0 : ℝ →L[ℝ] ℝ) xstar ∧
      (∃ v : ℝ, v ≠ 0 ∧ (fderiv ℝ (fderiv ℝ f) xstar) v v = 0) := by
  -- Use the quartic: it has a strict local minimum at the origin, but its Hessian degenerates there.
  refine ⟨fun x : ℝ => x ^ 4, 0, ?_⟩
  constructor
  · -- The quartic is smooth on all of `ℝ`.
    refine ⟨Set.univ, by simp, ?_⟩
    simpa using (contDiff_id.pow 4).contDiffOn
  constructor
  · -- Every nonzero point has strictly larger value than `0` under the quartic.
    refine ⟨Set.univ, isOpen_univ, by simp, ?_⟩
    intro x _ hx
    simpa using fourth_pow_pos_of_ne_zero hx
  constructor
  · -- The first derivative vanishes at the origin because the quartic derivative is `4x^3`.
    convert ((hasDerivAt_pow 4 (0 : ℝ)).hasFDerivAt :
        HasFDerivAt (fun x : ℝ => x ^ 4)
          (ContinuousLinearMap.toSpanSingleton ℝ ((4 : ℝ) * 0 ^ (4 - 1))) 0) using 1
    ext
    simp
  · -- The Hessian is zero at the origin, so it is not positive definite.
    refine ⟨1, by norm_num, ?_⟩
    rw [quartic_second_fderiv_at_zero]
    simp

end «problem-6»
