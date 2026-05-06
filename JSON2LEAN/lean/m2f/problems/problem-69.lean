import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-69»
/-
For a function f: ℝ^n → ℝ cup {+ ∞}, its convex conjugate f*: ℝ^n → ℝ cup {+ ∞} is defined by f*(y)
=
sup_{x∈ℝ^n}(yᵀ x - f(x)).
-/
def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup {r : EReal | ∃ x : Fin n → ℝ, r = (∑ i : Fin n, (y i) * (x i)) - f x}

/-
Given an optimization problem with objective function f₀, inequality constraint functions fᵢ, and
equality constraint functions hⱼ, the dual function is g(λ, nu) = inf_x (f₀(x) + sum_i λ_i fᵢ(x) +
sum_j
nu_j hⱼ(x)), with domain consisting of the multipliers for which the infimum is well defined.
-/
def newtonStepOneDimMax
    (g' g'' : ℝ → ℝ)
    (ν : ℝ) :
    Option ℝ :=
  if _h : g'' ν = 0 then
    none
  else
    some (-(g' ν) / (g'' ν))

/-
A simple operation count model for one Newton step in the separable dual problem: evaluate the
`n` coordinates contributing to g', evaluate the `n` coordinates contributing to g'', and then
perform a constant number of scalar operations.
-/
def separableEqualityDualNewtonStepOpCount (n : ℕ) : ℕ :=
  2 * n + 3

/-
Consider the optimization problem minimize & \sum_{i = 1}^n fᵢ(xᵢ); subject to &
\sum_{i = 1}^n xᵢ = 1, array with decision variable x = (x₁, ..., xₙ)∈ℝ^n, where each
function fᵢ: ℝ→ℝ is twice differentiable and satisfies fᵢ''(z) ≥ m > 0 for all z∈ℝ, i = 1, ..., n.
-/
structure SeparableEqualityConstrainedProblem where
  n : ℕ
  f : Fin n → ℝ → ℝ
  m : ℝ
  m_pos : 0 < m
  twiceDifferentiable : ∀ i : Fin n, ContDiff ℝ 2 (f i)
  secondDerivLowerBound : ∀ i : Fin n, ∀ z : ℝ, m ≤ deriv (deriv (f i)) z

/-
Define the dual function by g(nu) = - nu - \sum_{i = 1}^n fᵢ*(- nu), nu∈ℝ. For each nu∈ℝ, define
x(nu)∈ℝ^n by xᵢ(nu) = (fᵢ')^{- 1}(- nu), equivalently, xᵢ(nu) = (fᵢ*)'(- nu).
-/
def separableConvexConjugateReal
    (P : SeparableEqualityConstrainedProblem) :
    (ℝ → EReal) × (ℝ → Fin P.n → ℝ) :=
  let fi_conj : Fin P.n → ℝ → EReal :=
    fun i y => convexConjugate (fun z : Fin 1 → ℝ => (P.f i (z 0) : EReal)) (fun _ => y)
  let g : ℝ → EReal :=
    fun ν => ((-ν : ℝ) : EReal) - ∑ i : Fin P.n, fi_conj i (-ν)
  let x : ℝ → Fin P.n → ℝ :=
    fun ν i => deriv (fun y => (fi_conj i y).toReal) (-ν)
  (g, x)

def separableEqualityDualFunction
    (P : SeparableEqualityConstrainedProblem) :
    ℝ → EReal :=
  (separableConvexConjugateReal P).1

def separableEqualityDualX
    (P : SeparableEqualityConstrainedProblem) :
    ℝ → Fin P.n → ℝ :=
  (separableConvexConjugateReal P).2

structure SeparableEqualityDualData (P : SeparableEqualityConstrainedProblem) where
  dualFunction : ℝ → EReal
  x : ℝ → Fin P.n → ℝ

structure SeparableEqualityDualNewtonStepComputation
    (P : SeparableEqualityConstrainedProblem)
    (D : SeparableEqualityDualData P)
    (ν : ℝ) where
  gradientValue : ℝ
  curvatureValue : ℝ
  step : ℝ
  opCount : ℕ
  curvature_ne_zero : curvatureValue ≠ 0

/-
maximize g(ν).
-/
structure DualMaximizationProblem
    (P : SeparableEqualityConstrainedProblem) where
  objective : ℝ → EReal

def DualMaximizationProblem.mkDefault
    (P : SeparableEqualityConstrainedProblem) : DualMaximizationProblem P :=
  { objective := separableEqualityDualFunction P }

def DualMaximizationProblem.feasibleSet
    {P : SeparableEqualityConstrainedProblem} (_ : DualMaximizationProblem P) : Set ℝ :=
  Set.univ

/-- If a scalar convex conjugate is evaluated at a derivative value, the supremum is attained at
the corresponding primal point. -/
lemma scalar_convexConjugate_eq_of_deriv {f : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) {x y : ℝ} (hx : DifferentiableAt ℝ f x)
    (hy : deriv f x = y) :
    convexConjugate (fun z : Fin 1 → ℝ => (f (z 0) : EReal)) (fun _ => y) =
      (((y * x - f x : ℝ)) : EReal) := by
  -- Compare each candidate against the supporting line at the primal point `x`.
  have h_upper_real : ∀ z : Fin 1 → ℝ, y * z 0 - f (z 0) ≤ y * x - f x := by
    intro z
    rcases lt_trichotomy (z 0) x with hzx | rfl | hzx
    · have hslope : slope f (z 0) x ≤ deriv f x := by
        simpa using hconv.slope_le_deriv (by simp) (by simp) hzx hx
      have hmul : f x - f (z 0) ≤ y * (x - z 0) := by
        have hslope' : slope f (z 0) x ≤ y := by
          simpa [hy] using hslope
        have hxz : 0 < x - z 0 := sub_pos.mpr hzx
        exact (div_le_iff₀ hxz).mp (by
          simpa [slope, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using hslope')
      linarith
    · linarith
    · have hslope : deriv f x ≤ slope f x (z 0) := by
        simpa using hconv.deriv_le_slope (by simp) (by simp) hzx hx
      have hmul : y * (z 0 - x) ≤ f (z 0) - f x := by
        have hslope' : y ≤ slope f x (z 0) := by
          simpa [hy] using hslope
        have hxz : 0 < z 0 - x := sub_pos.mpr hzx
        exact (le_div_iff₀ hxz).mp (by
          simpa [slope, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using hslope')
      linarith
  -- The supporting-line inequality bounds the whole supremum from above.
  have h_bdd :
      BddAbove {r : EReal | ∃ z : Fin 1 → ℝ,
        r = (∑ i : Fin 1, (fun _ => y) i * z i) -
          (fun z' : Fin 1 → ℝ => (f (z' 0) : EReal)) z} := by
    refine ⟨(((y * x - f x : ℝ)) : EReal), ?_⟩
    intro r hr
    rcases hr with ⟨z, rfl⟩
    have hz :
        (((y * z 0 - f (z 0) : ℝ)) : EReal) ≤ (((y * x - f x : ℝ)) : EReal) := by
      exact_mod_cast h_upper_real z
    simpa [Fin.sum_univ_one] using hz
  unfold convexConjugate
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · refine ⟨(((y * x - f x : ℝ)) : EReal), ⟨(fun _ : Fin 1 => x), ?_⟩⟩
      simp
    intro r hr
    rcases hr with ⟨z, rfl⟩
    have hz :
        (((y * z 0 - f (z 0) : ℝ)) : EReal) ≤ (((y * x - f x : ℝ)) : EReal) := by
      exact_mod_cast h_upper_real z
    simpa [Fin.sum_univ_one] using hz
  · refine le_csSup h_bdd ?_
    refine ⟨(fun _ : Fin 1 => x), ?_⟩
    simp

/-- The derivative of each strongly convex scalar coordinate has a global inverse whose derivative
is the reciprocal of the second derivative. -/
lemma coordinate_inverse_of_deriv
    (P : SeparableEqualityConstrainedProblem) (i : Fin P.n) :
    ∃ ψ : ℝ → ℝ,
      (∀ y, deriv (P.f i) (ψ y) = y) ∧
      (∀ y, HasDerivAt ψ (1 / deriv (deriv (P.f i)) (ψ y)) y) := by
  let φ : ℝ → ℝ := deriv (P.f i)
  have hC2 : ContDiff ℝ 2 (P.f i) := P.twiceDifferentiable i
  have hφ_cont : Continuous φ := by
    simpa [φ] using hC2.continuous_deriv (by norm_num)
  have hφ_diff : Differentiable ℝ φ := by
    simpa [φ] using hC2.differentiable_deriv_two
  have hφ_C1 : ContDiff ℝ 1 φ := by
    simpa [φ] using hC2.deriv'
  have hφ_second_lower : ∀ z, P.m ≤ deriv φ z := by
    intro z
    simpa [φ] using P.secondDerivLowerBound i z
  have hφ_deriv_pos : ∀ z, 0 < deriv φ z := by
    intro z
    exact lt_of_lt_of_le P.m_pos (hφ_second_lower z)
  have hφ_strict : StrictMono φ := strictMono_of_deriv_pos hφ_deriv_pos
  have hφ_surj : Function.Surjective φ := by
    intro y
    let R : ℝ := (|y - φ 0| + 1) / P.m
    have hR_pos : 0 < R := by
      have : 0 < |y - φ 0| + 1 := by positivity
      exact div_pos this P.m_pos
    have hleft_growth : P.m * R ≤ φ 0 - φ (-R) := by
      have hmono := mul_sub_le_image_sub_of_le_deriv hφ_diff hφ_second_lower (by linarith : -R ≤ 0)
      simpa [R] using hmono
    have hright_growth : P.m * R ≤ φ R - φ 0 := by
      have hmono := mul_sub_le_image_sub_of_le_deriv hφ_diff hφ_second_lower (by linarith : 0 ≤ R)
      simpa [R] using hmono
    have hmul : P.m * R = |y - φ 0| + 1 := by
      dsimp [R]
      field_simp [P.m_pos.ne']
    have hleft_lt : φ (-R) < y := by
      have habs : -(|y - φ 0|) ≤ y - φ 0 := by
        simpa using neg_abs_le (y - φ 0)
      linarith
    have hright_lt : y < φ R := by
      have habs : y - φ 0 ≤ |y - φ 0| := by
        simpa using le_abs_self (y - φ 0)
      linarith
    have hy_mem : y ∈ Set.Icc (φ (-R)) (φ R) := by
      exact ⟨le_of_lt hleft_lt, le_of_lt hright_lt⟩
    have hsurjIcc :=
      hφ_cont.continuousOn.surjOn_Icc (s := Set.univ) (a := -R) (b := R) (by simp) (by simp)
    rcases hsurjIcc hy_mem with ⟨x, -, hx⟩
    exact ⟨x, hx⟩
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective φ hφ_strict hφ_surj
  refine ⟨e.symm, ?_, ?_⟩
  · intro y
    -- The order isomorphism gives the inverse equation globally.
    simpa [e, φ] using StrictMono.orderIsoOfSurjective_self_symm_apply φ hφ_strict hφ_surj y
  · intro y
    -- Route correction: differentiate the exact inverse identity instead of the conjugate first.
    have hφ_hasDeriv : HasDerivAt φ (deriv φ (e.symm y)) (e.symm y) := by
      exact (hφ_C1.contDiffAt.hasStrictDerivAt (by norm_num)).hasDerivAt
    have hφ_deriv_ne : deriv φ (e.symm y) ≠ 0 := (hφ_deriv_pos (e.symm y)).ne'
    have hrightInv : ∀ᶠ z in 𝓝 y, φ (e.symm z) = z := by
      exact Filter.Eventually.of_forall fun z =>
        StrictMono.orderIsoOfSurjective_self_symm_apply φ hφ_strict hφ_surj z
    have hψ_cont : ContinuousAt e.symm y := e.symm.continuous.continuousAt
    have hψ :
        HasDerivAt e.symm ((deriv φ (e.symm y))⁻¹) y :=
      HasDerivAt.of_local_left_inverse hψ_cont hφ_hasDeriv hφ_deriv_ne hrightInv
    simpa [φ, one_div] using hψ

/-
Consider the separable equality - constrained problem. For each i, let fᵢ* be the convex conjugate
of
fᵢ, fᵢ*(y) = sup_{x∈ℝ} (yx - fᵢ(x)). Assume that fᵢ* and (fᵢ*)' are readily computable, and that for
any scalar nu∈ℝ, the equation fᵢ'(x) = nu can be solved for x. Define the dual function by g(nu) =
- nu - \sum_{i = 1}^n fᵢ*(- nu), nu∈ℝ. For each nu∈ℝ, define x(nu)∈ℝ^n by xᵢ(nu) = (fᵢ')^{- 1}(-
nu),
equivalently xᵢ(nu) = (fᵢ*)'(- nu). Prove that the dual problem is the dual maximization problem,
and that g'(nu) = \sum_{i = 1}^n xᵢ(nu) - 1, g''(nu) = - \sum_{i = 1}^n (1)/(fᵢ''(xᵢ(nu))).
-/
theorem separableEqualityDual_derivatives
    (P : SeparableEqualityConstrainedProblem)
    (hfin : ∀ ν : ℝ, separableEqualityDualFunction P ν ≠ ⊤ ∧ separableEqualityDualFunction P ν ≠ ⊥)
    (hconj_fin :
      ∀ ν : ℝ, ∀ i : Fin P.n,
        convexConjugate (fun z : Fin 1 → ℝ => (P.f i (z 0) : EReal)) (fun _ => -ν) ≠ ⊤ ∧
          convexConjugate (fun z : Fin 1 → ℝ => (P.f i (z 0) : EReal)) (fun _ => -ν) ≠ ⊥)
    (hconj_diff :
      ∀ ν : ℝ, ∀ i : Fin P.n,
        DifferentiableAt ℝ
          (fun y : ℝ =>
            (convexConjugate (fun z : Fin 1 → ℝ => (P.f i (z 0) : EReal)) (fun _ => y)).toReal)
          (-ν))
    (hg_twice :
      ∀ ν : ℝ,
        DifferentiableAt ℝ (fun t : ℝ => (separableEqualityDualFunction P t).toReal) ν ∧
          DifferentiableAt ℝ
            (fun t : ℝ => deriv (fun s : ℝ => (separableEqualityDualFunction P s).toReal) t) ν) :
    (∀ ν : ℝ,
      ∀ i : Fin P.n,
        deriv (P.f i) (separableEqualityDualX P ν i) = -ν) ∧
    ((DualMaximizationProblem.mkDefault P).objective = separableEqualityDualFunction P ∧
      (DualMaximizationProblem.mkDefault P).feasibleSet = Set.univ) ∧
    (∀ ν : ℝ,
      deriv (fun t : ℝ => ((separableEqualityDualFunction P t).toReal)) ν
        = (∑ i : Fin P.n, separableEqualityDualX P ν i) - 1) ∧
    (∀ ν : ℝ,
      deriv (fun t : ℝ => deriv (fun s : ℝ => ((separableEqualityDualFunction P s).toReal)) t) ν
        = -∑ i : Fin P.n, (1 / deriv (deriv (P.f i)) (separableEqualityDualX P ν i))) := by
  classical
  let fiConj : Fin P.n → ℝ → EReal :=
    fun i y => convexConjugate (fun z : Fin 1 → ℝ => (P.f i (z 0) : EReal)) (fun _ => y)
  let ψ : Fin P.n → ℝ → ℝ := fun i => Classical.choose (coordinate_inverse_of_deriv P i)
  have hψ_deriv : ∀ i : Fin P.n, ∀ y : ℝ, deriv (P.f i) (ψ i y) = y := by
    intro i y
    exact (Classical.choose_spec (coordinate_inverse_of_deriv P i)).1 y
  have hψ_hasDeriv :
      ∀ i : Fin P.n, ∀ y : ℝ,
        HasDerivAt (ψ i) (1 / deriv (deriv (P.f i)) (ψ i y)) y := by
    intro i y
    exact (Classical.choose_spec (coordinate_inverse_of_deriv P i)).2 y
  -- First keep the whole dual objective finite at the `EReal` level so that `toReal_sub`
  -- can be applied before any scalar-conjugate substitution.
  have hsum_finite :
      ∀ s : Finset (Fin P.n), ∀ t : ℝ,
        (Finset.sum s fun i => fiConj i (-t)) ≠ ⊤ ∧
          (Finset.sum s fun i => fiConj i (-t)) ≠ ⊥ := by
    intro s t
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha hs =>
        rcases hs with ⟨hs_top, hs_bot⟩
        rcases hconj_fin t a with ⟨ha_top, ha_bot⟩
        constructor
        · simpa [Finset.sum_insert ha, fiConj] using
            EReal.add_ne_top ha_top hs_top
        · simpa [Finset.sum_insert ha, fiConj] using
            (EReal.add_ne_bot_iff.2 ⟨ha_bot, hs_bot⟩)
  -- After that finiteness reduction, the dual objective becomes a real finite sum.
  have hsum_toReal :
      ∀ s : Finset (Fin P.n), ∀ t : ℝ,
        (Finset.sum s fun i => fiConj i (-t)).toReal
          = Finset.sum s fun i => (fiConj i (-t)).toReal := by
    intro s t
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha hs =>
        rcases hsum_finite s t with ⟨hs_top, hs_bot⟩
        rcases hconj_fin t a with ⟨ha_top, ha_bot⟩
        rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.toReal_add ha_top ha_bot hs_top hs_bot,
          hs]
  have hdual_toReal :
      ∀ t : ℝ,
        (separableEqualityDualFunction P t).toReal
          = -t - ∑ i : Fin P.n, (fiConj i (-t)).toReal := by
    intro t
    rcases hsum_finite Finset.univ t with ⟨hs_top, hs_bot⟩
    rw [separableEqualityDualFunction, separableConvexConjugateReal, EReal.toReal_sub]
    · simp [fiConj, hsum_toReal]
    · simp
    · simp
    · exact hs_top
    · exact hs_bot
  have hdual_toReal_fun :
      (fun t : ℝ => (separableEqualityDualFunction P t).toReal)
        = fun t : ℝ => -t - ∑ i : Fin P.n, (fiConj i (-t)).toReal := by
    funext t
    exact hdual_toReal t
  -- Each scalar coordinate is convex because its derivative is monotone.
  have hcoord_convex : ∀ i : Fin P.n, ConvexOn ℝ Set.univ (P.f i) := by
    intro i
    have hC2 : ContDiff ℝ 2 (P.f i) := P.twiceDifferentiable i
    have hdiff : Differentiable ℝ (P.f i) := hC2.differentiable (by norm_num)
    have hderiv_diff : Differentiable ℝ (deriv (P.f i)) := hC2.differentiable_deriv_two
    have hderiv_mono : Monotone (deriv (P.f i)) := by
      exact monotone_of_deriv_nonneg hderiv_diff fun z =>
        le_trans P.m_pos.le (P.secondDerivLowerBound i z)
    exact Monotone.convexOn_univ_of_deriv hdiff hderiv_mono
  -- Route correction: compute each conjugate derivative only after taking `toReal`,
  -- so all subsequent differentiation stays in `ℝ`.
  have hcoord_value :
      ∀ i : Fin P.n, ∀ y : ℝ,
        (fiConj i y).toReal = y * ψ i y - P.f i (ψ i y) := by
    intro i y
    have hdiff_at : DifferentiableAt ℝ (P.f i) (ψ i y) := by
      exact (P.twiceDifferentiable i).differentiable (by norm_num) (ψ i y)
    have hvalue :
        fiConj i y = (((y * ψ i y - P.f i (ψ i y) : ℝ)) : EReal) := by
      simpa [fiConj] using
        scalar_convexConjugate_eq_of_deriv (f := P.f i) (hcoord_convex i) hdiff_at (hψ_deriv i y)
    simpa using congrArg EReal.toReal hvalue
  have hcoord_hasDeriv :
      ∀ i : Fin P.n, ∀ y : ℝ,
        HasDerivAt (fun u : ℝ => (fiConj i u).toReal) (ψ i y) y := by
    intro i y
    have hfun :
        (fun u : ℝ => (fiConj i u).toReal)
          = fun u : ℝ => u * ψ i u - P.f i (ψ i u) := by
      funext u
      exact hcoord_value i u
    rw [hfun]
    have hψy :
        HasDerivAt (ψ i) (1 / deriv (deriv (P.f i)) (ψ i y)) y := hψ_hasDeriv i y
    have hmul :
        HasDerivAt (fun u : ℝ => u * ψ i u)
          (ψ i y + y * (1 / deriv (deriv (P.f i)) (ψ i y))) y := by
      simpa using (hasDerivAt_id y).mul hψy
    have hC1 : ContDiff ℝ 1 (P.f i) := (P.twiceDifferentiable i).of_le (by norm_num)
    have hfi :
        HasDerivAt (P.f i) (deriv (P.f i) (ψ i y)) (ψ i y) := by
      exact (hC1.contDiffAt.hasStrictDerivAt (by norm_num)).hasDerivAt
    have hcomp :
        HasDerivAt (fun u : ℝ => P.f i (ψ i u))
          (deriv (P.f i) (ψ i y) * (1 / deriv (deriv (P.f i)) (ψ i y))) y := by
      simpa using hfi.comp y hψy
    convert hmul.sub hcomp using 1
    rw [hψ_deriv i y]
    ring
  -- The chosen inverse branch agrees with the built-in dual coordinate definition.
  have hx_eq :
      ∀ ν : ℝ, ∀ i : Fin P.n, separableEqualityDualX P ν i = ψ i (-ν) := by
    intro ν i
    unfold separableEqualityDualX separableConvexConjugateReal
    simpa [fiConj] using (hcoord_hasDeriv i (-ν)).deriv
  have hcoord_deriv_target :
      ∀ ν : ℝ, ∀ i : Fin P.n, deriv (P.f i) (separableEqualityDualX P ν i) = -ν := by
    intro ν i
    rw [hx_eq ν i]
    exact hψ_deriv i (-ν)
  -- Differentiate the canonical real-valued dual objective once.
  have hfirst_formula :
      ∀ ν : ℝ,
        deriv (fun t : ℝ => ((separableEqualityDualFunction P t).toReal)) ν
          = (∑ i : Fin P.n, separableEqualityDualX P ν i) - 1 := by
    intro ν
    have hterm :
        ∀ i : Fin P.n,
          HasDerivAt (fun t : ℝ => (fiConj i (-t)).toReal) (-(ψ i (-ν))) ν := by
      intro i
      have hneg : HasDerivAt (fun t : ℝ => -t) (-1) ν := by
        simpa using (hasDerivAt_id ν).neg
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (hcoord_hasDeriv i (-ν)).comp ν hneg
    have hsum :
        HasDerivAt (fun t : ℝ => ∑ i : Fin P.n, (fiConj i (-t)).toReal)
          (∑ i : Fin P.n, -(ψ i (-ν))) ν := by
      simpa using (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hterm i)
    rw [hdual_toReal_fun]
    convert ((hasDerivAt_id ν).neg.sub hsum).deriv using 1
    simp [hx_eq ν, sub_eq_add_neg, Finset.sum_neg_distrib, add_comm]
  have hfirst_fun :
      (fun t : ℝ => deriv (fun s : ℝ => ((separableEqualityDualFunction P s).toReal)) t)
        = fun t : ℝ => (∑ i : Fin P.n, ψ i (-t)) - 1 := by
    funext t
    simpa [hx_eq t] using hfirst_formula t
  -- Differentiate the already-simplified first derivative to obtain the curvature formula.
  have hsecond_formula :
      ∀ ν : ℝ,
        deriv (fun t : ℝ => deriv (fun s : ℝ => ((separableEqualityDualFunction P s).toReal)) t) ν
          = -∑ i : Fin P.n, (1 / deriv (deriv (P.f i)) (separableEqualityDualX P ν i)) := by
    intro ν
    have hterm :
        ∀ i : Fin P.n,
          HasDerivAt (fun t : ℝ => ψ i (-t))
            (-(1 / deriv (deriv (P.f i)) (ψ i (-ν)))) ν := by
      intro i
      have hneg : HasDerivAt (fun t : ℝ => -t) (-1) ν := by
        simpa using (hasDerivAt_id ν).neg
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (hψ_hasDeriv i (-ν)).comp ν hneg
    have hsum :
        HasDerivAt (fun t : ℝ => ∑ i : Fin P.n, ψ i (-t))
          (∑ i : Fin P.n, -(1 / deriv (deriv (P.f i)) (ψ i (-ν)))) ν := by
      simpa using (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hterm i)
    rw [hfirst_fun]
    convert (hsum.sub (hasDerivAt_const ν (1 : ℝ))).deriv using 1
    simp [hx_eq ν, Finset.sum_neg_distrib]
  refine ⟨hcoord_deriv_target, ?_⟩
  refine ⟨?_, ?_⟩
  · constructor
    · rfl
    · rfl
  · refine ⟨hfirst_formula, hsecond_formula⟩

/-
Consider the separable equality - constrained problem. For each i, let fᵢ* be the convex conjugate
of
fᵢ, fᵢ*(y) = sup_{x∈ℝ} (yx - fᵢ(x)). Assume that fᵢ* and (fᵢ*)' are readily computable, and that for
any scalar nu∈ℝ, the equation fᵢ'(x) = nu can be solved for x. Define the dual function by g(nu) =
- nu - \sum_{i = 1}^n fᵢ*(- nu), nu∈ℝ. For each nu∈ℝ, define x(nu)∈ℝ^n by xᵢ(nu) = (fᵢ')^{- 1}(-
nu),
equivalently xᵢ(nu) = (fᵢ*)'(- nu). Hence prove that a Newton step for the dual problem can be
computed with computational complexity of order n.
-/
theorem separableEqualityDual_newtonStep_complexity_linear
    (P : SeparableEqualityConstrainedProblem)
    (D : SeparableEqualityDualData P)
    (hdenom :
      ∀ ν : ℝ,
        (∑ i : Fin P.n, (1 / deriv (deriv (P.f i)) (D.x ν i))) ≠ 0) :
    ∀ ν : ℝ,
      ∃ comp : SeparableEqualityDualNewtonStepComputation P D ν,
        some comp.step =
          newtonStepOneDimMax
            (fun t => (∑ i : Fin P.n, D.x t i) - 1)
            (fun t => -∑ i : Fin P.n, (1 / deriv (deriv (P.f i)) (D.x t i)))
            ν ∧
        comp.opCount = separableEqualityDualNewtonStepOpCount P.n ∧
        comp.opCount = 2 * P.n + 3 ∧
        comp.opCount ≤ 5 * P.n + 5 := by
  intro ν
  let gradientValue : ℝ := (∑ i : Fin P.n, D.x ν i) - 1
  let curvatureValue : ℝ := -∑ i : Fin P.n, (1 / deriv (deriv (P.f i)) (D.x ν i))
  have hcurv_ne : curvatureValue ≠ 0 := by
    simpa [curvatureValue] using neg_ne_zero.mpr (hdenom ν)
  refine ⟨
    { gradientValue := gradientValue
      curvatureValue := curvatureValue
      step := -(gradientValue) / curvatureValue
      opCount := separableEqualityDualNewtonStepOpCount P.n
      curvature_ne_zero := hcurv_ne }, ?_, ?_, ?_⟩
  · -- The curvature is nonzero, so the Newton step returns the expected scalar update.
    unfold newtonStepOneDimMax
    split_ifs with hif
    · exfalso
      exact hcurv_ne (by simpa [curvatureValue] using hif)
    · simp [gradientValue, curvatureValue]
  · rfl
  · constructor
    · rfl
    · dsimp [separableEqualityDualNewtonStepOpCount]
      linarith

end «problem-69»
