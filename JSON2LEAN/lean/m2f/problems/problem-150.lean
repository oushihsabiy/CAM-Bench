import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-150»

/- [BLOCK Exercise 17.7 | 5 | defn]
For inequality constraint functions cᵢ, the active set at a feasible point x is A(x)={i : cᵢ(x)=0},
that is, the set of indices of inequality constraints that are satisfied with equality.
-/
def activeSet {ι : Type*} {X : Type*} (c : ι → X → ℝ) (x : X) : Set ι :=
  {i | c i x = 0}

/- [BLOCK Exercise 17.7 | 6 | defn]
An equality constraint is a constraint of the form cᵢ(x)=0.
-/
def IsEqualityConstraint {X : Type*} (c : X → ℝ) : X → Prop :=
  fun x => c x = 0

/- [BLOCK Exercise 17.7 | 7 | defn]
An inequality constraint is a constraint of the form cᵢ(x)≥ 0, or equivalently -cᵢ(x)≤ 0, depending
on the sign convention.
-/
def IsInequalityConstraint {X : Type*} (c : X → ℝ) : X → Prop :=
  fun x => 0 ≤ c x

/- [BLOCK Exercise 17.7 | 8 | defn]
A point x is feasible for a family of constraints if it satisfies all equality constraints and all
inequality constraints.
-/
def IsFeasiblePoint {ι : Type*} {X : Type*} (eqs ineqs : ι → X → ℝ) (x : X) : Prop :=
  (∀ i : ι, eqs i x = 0) ∧ (∀ i : ι, 0 ≤ ineqs i x)

/- [BLOCK Exercise 17.7 | 9 | thm]
Let f:ℝ^n → ℝ and cᵢ:ℝ^n → ℝ for i ∈ EcupI be continuously differentiable, where E and I index the
equality and inequality constraints. For μ ≥ 0, define φ_1(x;μ)=f(x)+μsum_{i∈E} |cᵢ(x)|+μsum_{i∈I}
[cᵢ(x)]^-, where [t]^-=0,-t. Let x∈ℝ^n satisfy cᵢ(x)=0 quad for all i∈E, cᵢ(x)≥ 0 quad for all i∈I,
and define the active set A(x)={i∈I: cᵢ(x)=0}. For p∈ℝ^n, let D(φ_1(x;μ);p)=lim_{α→ 0^+}frac{φ_1(x+α
p;μ)-φ_1(x;μ)}{α}, provided the limit exists. Verify that
D(φ_1(x;μ);p)=
∇ f(x)ᵀ p
+μ sum_{i∈E} ≤ft|∇ cᵢ(x)ᵀ p|
+μ sum_{i∈Icap A(x)} ≤ft[∇ cᵢ(x)ᵀ p]^-.
17.28
-/
open scoped BigOperators

/-- A differentiable scalar field has the expected right-hand directional secant limit. -/
private lemma tendsto_directional_quotient_of_differentiable
    {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {xhat p : EuclideanSpace ℝ (Fin n)}
    (hg : DifferentiableAt ℝ g xhat) :
    Tendsto
      (fun α : ℝ => (g (xhat + α • p) - g xhat) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 ((fderiv ℝ g xhat) p)) := by
  -- Route correction: differentiate along the line `xhat + α • p` and read off the `fderiv` value.
  simpa [hg.lineDeriv_eq_fderiv (v := p), div_eq_mul_inv, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using
    (hg.hasFDerivAt.hasLineDerivAt p).tendsto_slope_zero_right

/-- If a differentiable function vanishes at the base point, the absolute-value quotient tends to
the absolute directional derivative. -/
private lemma tendsto_abs_directional_term_of_eq_zero
    {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {xhat p : EuclideanSpace ℝ (Fin n)}
    (hg : DifferentiableAt ℝ g xhat) (hgx : g xhat = 0) :
    Tendsto
      (fun α : ℝ => |g (xhat + α • p)| / α)
      (𝓝[>] (0 : ℝ)) (𝓝 |(fderiv ℝ g xhat) p|) := by
  have hrewrite :
      (fun α : ℝ => |g (xhat + α • p)| / α) =ᶠ[𝓝[>] (0 : ℝ)]
        fun α : ℝ => |(g (xhat + α • p) - g xhat) / α| := by
    -- On positive steps, divide after taking `abs` by turning the quotient into `abs` of a secant.
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hαinv : 0 ≤ α⁻¹ := inv_nonneg.mpr hα.le
    calc
      |g (xhat + α • p)| / α = |g (xhat + α • p)| * α⁻¹ := by rw [div_eq_mul_inv]
      _ = |g (xhat + α • p) * α⁻¹| := by rw [abs_mul, abs_of_nonneg hαinv]
      _ = |(g (xhat + α • p) - g xhat) / α| := by simp [hgx, div_eq_mul_inv]
  refine Tendsto.congr' hrewrite.symm ?_
  -- Continuity of `abs` transports the directional secant limit to the desired absolute-value limit.
  exact (continuous_abs.continuousAt.tendsto.comp
    (tendsto_directional_quotient_of_differentiable (g := g) (xhat := xhat) (p := p) hg))

/-- If a differentiable function vanishes at the base point, the negative-part quotient tends to
the negative part of the directional derivative. -/
private lemma tendsto_active_negative_part_term
    {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {xhat p : EuclideanSpace ℝ (Fin n)}
    (hg : DifferentiableAt ℝ g xhat) (hgx : g xhat = 0) :
    Tendsto
      (fun α : ℝ => max 0 (-g (xhat + α • p)) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 (max 0 (-(fderiv ℝ g xhat) p))) := by
  have hrewrite :
      (fun α : ℝ => max 0 (-g (xhat + α • p)) / α) =ᶠ[𝓝[>] (0 : ℝ)]
        fun α : ℝ => max 0 (-((g (xhat + α • p) - g xhat) / α)) := by
    -- On positive steps, scale the negative part through the quotient so the secant lemma applies.
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hαinv : 0 ≤ α⁻¹ := inv_nonneg.mpr hα.le
    calc
      max 0 (-g (xhat + α • p)) / α = max 0 (-g (xhat + α • p)) * α⁻¹ := by
        rw [div_eq_mul_inv]
      _ = max (0 * α⁻¹) ((-g (xhat + α • p)) * α⁻¹) := by
        rw [(max_mul_of_nonneg 0 (-g (xhat + α • p)) hαinv).symm]
      _ = max 0 (-((g (xhat + α • p) - g xhat) / α)) := by
        simp [hgx, div_eq_mul_inv, neg_mul]
  refine Tendsto.congr' hrewrite.symm ?_
  -- Continuity of `t ↦ max 0 (-t)` turns the secant-slope limit into the active-constraint limit.
  exact (((continuous_const.max continuous_neg).continuousAt.tendsto).comp
    (tendsto_directional_quotient_of_differentiable (g := g) (xhat := xhat) (p := p) hg))

/-- If a differentiable function is strictly positive at the base point, its negative-part quotient
is eventually zero along the positive ray. -/
private lemma tendsto_inactive_negative_part_term
    {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {xhat p : EuclideanSpace ℝ (Fin n)}
    (hg : DifferentiableAt ℝ g xhat) (hgx : 0 < g xhat) :
    Tendsto
      (fun α : ℝ => max 0 (-g (xhat + α • p)) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hline :
      Tendsto (fun α : ℝ => xhat + α • p) (𝓝[>] (0 : ℝ)) (𝓝 xhat) := by
    -- The line map `α ↦ xhat + α • p` tends to `xhat` as `α → 0`.
    have hcont : ContinuousAt (fun α : ℝ => xhat + α • p) 0 := by
      simpa using (continuousAt_const.add
        (continuousAt_id.smul continuousAt_const :
          ContinuousAt (fun α : ℝ => α • p) 0))
    have hline' :
        Tendsto (fun α : ℝ => xhat + α • p) (nhdsWithin 0 (Set.Ioi 0))
          (𝓝 ((fun α : ℝ => xhat + α • p) 0)) := by
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa [zero_smul] using hline'
  have hpos :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < g (xhat + α • p) := by
    -- Continuity preserves the strict positivity of `g xhat` for nearby positive steps.
    exact (hg.continuousAt.tendsto.comp hline).eventually (Ioi_mem_nhds hgx)
  have hzero :
      (fun α : ℝ => max 0 (-g (xhat + α • p)) / α) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => 0 := by
    -- Once the constraint stays positive, its negative part vanishes identically.
    filter_upwards [hpos] with α hα
    simp [max_eq_left (neg_nonpos.mpr hα.le)]
  exact Tendsto.congr' hzero.symm tendsto_const_nhds

theorem phi1_directionalDerivative_formula
    {n : ℕ} {ιE ιI : Type*}
    [Fintype ιE] [Fintype ιI]
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (cE : ιE → EuclideanSpace ℝ (Fin n) → ℝ)
    (cI : ιI → EuclideanSpace ℝ (Fin n) → ℝ)
    (xhat p : EuclideanSpace ℝ (Fin n))
    [DecidablePred fun i : ιI => i ∈ activeSet cI xhat]
    (μ : ℝ)
    (hfd : DifferentiableAt ℝ f xhat)
    (hcE : ∀ i : ιE, DifferentiableAt ℝ (cE i) xhat)
    (hcI : ∀ i : ιI, DifferentiableAt ℝ (cI i) xhat)
    (hμ : 0 ≤ μ)
    (hEq : ∀ i : ιE, cE i xhat = 0)
    (hIneq : ∀ i : ιI, 0 ≤ cI i xhat) :
    Tendsto
      (fun α : ℝ =>
        ((f (xhat + α • p)
            + μ * (∑ i : ιE, |cE i (xhat + α • p)|)
            + μ * (∑ i : ιI, max 0 (-cI i (xhat + α • p))))
          - (f xhat
            + μ * (∑ i : ιE, |cE i xhat|)
            + μ * (∑ i : ιI, max 0 (-cI i xhat)))) / α)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((fderiv ℝ f xhat) p
        + μ * (∑ i : ιE, |(fderiv ℝ (cE i) xhat) p|)
        + μ * (∑ i ∈ Finset.univ.filter (fun i : ιI => i ∈ activeSet cI xhat),
            max 0 (-(fderiv ℝ (cI i) xhat) p)))) := by
  let _ := hμ
  have hEqSum0 : ∑ i : ιE, |cE i xhat| = 0 := by
    -- Feasibility cancels every equality-penalty term at the base point.
    simp [hEq]
  have hIneqTerm0 : ∀ i : ιI, max 0 (-cI i xhat) = 0 := by
    intro i
    -- Feasibility also cancels every inequality-penalty term at the base point.
    rw [max_eq_left]
    linarith [hIneq i]
  have hIneqSum0 : ∑ i : ιI, max 0 (-cI i xhat) = 0 := by
    simp [hIneqTerm0]
  have hsplit :
      (fun α : ℝ =>
        ((f (xhat + α • p)
            + μ * (∑ i : ιE, |cE i (xhat + α • p)|)
            + μ * (∑ i : ιI, max 0 (-cI i (xhat + α • p))))
          - (f xhat
            + μ * (∑ i : ιE, |cE i xhat|)
            + μ * (∑ i : ιI, max 0 (-cI i xhat)))) / α) =
        fun α : ℝ =>
          (f (xhat + α • p) - f xhat) / α
            + (μ * (∑ i : ιE, |cE i (xhat + α • p)|)) / α
            + (μ * (∑ i : ιI, max 0 (-cI i (xhat + α • p)))) / α := by
    funext α
    -- Rewrite the exact-penalty quotient into objective, equality, and inequality directional terms.
    rw [hEqSum0, hIneqSum0]
    ring_nf
  rw [hsplit]
  have hf :
      Tendsto
        (fun α : ℝ => (f (xhat + α • p) - f xhat) / α)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ((fderiv ℝ f xhat) p)) := by
    -- The objective contribution is the standard right directional derivative.
    simpa using
      (tendsto_directional_quotient_of_differentiable
        (g := f) (xhat := xhat) (p := p) hfd)
  have hEqTerms :
      ∀ i : ιE,
        Tendsto
          (fun α : ℝ => |cE i (xhat + α • p)| / α)
          (nhdsWithin 0 (Set.Ioi 0))
          (𝓝 |(fderiv ℝ (cE i) xhat) p|) := by
    intro i
    -- Equality terms use `cE i xhat = 0` to reduce to the absolute secant-slope limit.
    simpa using
      (tendsto_abs_directional_term_of_eq_zero
        (g := cE i) (xhat := xhat) (p := p) (hcE i) (hEq i))
  have hEqSum :
      Tendsto
        (fun α : ℝ => ∑ i : ιE, |cE i (xhat + α • p)| / α)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (∑ i : ιE, |(fderiv ℝ (cE i) xhat) p|)) := by
    -- Sum the equality-term limits over the finite index set.
    exact tendsto_finset_sum Finset.univ fun i _ => hEqTerms i
  have hEqScaled :
      Tendsto
        (fun α : ℝ => (μ * (∑ i : ιE, |cE i (xhat + α • p)|)) / α)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (μ * (∑ i : ιE, |(fderiv ℝ (cE i) xhat) p|))) := by
    -- Move the scalar `μ` across the finite sum quotient to reuse the termwise equality limit.
    refine Tendsto.congr' ?_ (Filter.Tendsto.const_mul μ hEqSum)
    refine Filter.Eventually.of_forall ?_
    intro α
    simp [div_eq_mul_inv, Finset.mul_sum, mul_left_comm, mul_comm]
  have hIneqTerms :
      ∀ i : ιI,
        Tendsto
          (fun α : ℝ => max 0 (-cI i (xhat + α • p)) / α)
          (nhdsWithin 0 (Set.Ioi 0))
          (𝓝 (if i ∈ activeSet cI xhat then max 0 (-(fderiv ℝ (cI i) xhat) p) else 0)) := by
    intro i
    by_cases hi : i ∈ activeSet cI xhat
    · -- Active constraints satisfy `cI i xhat = 0`, so they contribute the negative-part limit.
      have hix : cI i xhat = 0 := by simpa [activeSet] using hi
      simpa [hi] using
        (tendsto_active_negative_part_term
          (g := cI i) (xhat := xhat) (p := p) (hcI i) hix)
    · -- Inactive constraints are strictly positive at `xhat`, so their quotient is eventually zero.
      have hineq_ne : cI i xhat ≠ 0 := by
        intro hzero
        exact hi (by simp [activeSet, hzero])
      have hineq_pos : 0 < cI i xhat := by
        exact lt_of_le_of_ne (hIneq i) (by simpa using hineq_ne.symm)
      simpa [hi] using
        (tendsto_inactive_negative_part_term
          (g := cI i) (xhat := xhat) (p := p) (hcI i) hineq_pos)
  have hIneqSum :
      Tendsto
        (fun α : ℝ => ∑ i : ιI, max 0 (-cI i (xhat + α • p)) / α)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (∑ i : ιI,
          if i ∈ activeSet cI xhat then max 0 (-(fderiv ℝ (cI i) xhat) p) else 0)) := by
    -- Sum the active and inactive inequality limits after the pointwise case split.
    exact tendsto_finset_sum Finset.univ fun i _ => hIneqTerms i
  have hIneqScaled :
      Tendsto
        (fun α : ℝ => (μ * (∑ i : ιI, max 0 (-cI i (xhat + α • p)))) / α)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (μ * (∑ i : ιI,
          if i ∈ activeSet cI xhat then max 0 (-(fderiv ℝ (cI i) xhat) p) else 0))) := by
    -- The same scalar/sum rewrite prepares the inequality family for the active-set limit.
    refine Tendsto.congr' ?_ (Filter.Tendsto.const_mul μ hIneqSum)
    refine Filter.Eventually.of_forall ?_
    intro α
    simp [div_eq_mul_inv, Finset.mul_sum, mul_left_comm, mul_comm]
  have hActiveSum :
      (∑ i : ιI,
        if i ∈ activeSet cI xhat then max 0 (-(fderiv ℝ (cI i) xhat) p) else 0) =
        ∑ i ∈ Finset.univ.filter (fun i : ιI => i ∈ activeSet cI xhat),
          max 0 (-(fderiv ℝ (cI i) xhat) p) := by
    -- Convert the `if`-sum over all inequalities into the filtered active-set sum on the RHS.
    simpa using
      (Finset.sum_filter
        (s := Finset.univ)
        (p := fun i : ιI => i ∈ activeSet cI xhat)
        (f := fun i : ιI => max 0 (-(fderiv ℝ (cI i) xhat) p))).symm
  have htotal :
      Tendsto
        (fun α : ℝ =>
          (f (xhat + α • p) - f xhat) / α
            + (μ * (∑ i : ιE, |cE i (xhat + α • p)|)) / α
            + (μ * (∑ i : ιI, max 0 (-cI i (xhat + α • p)))) / α)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (((fderiv ℝ f xhat) p
          + μ * (∑ i : ιE, |(fderiv ℝ (cE i) xhat) p|))
          + μ * (∑ i : ιI,
            if i ∈ activeSet cI xhat then max 0 (-(fderiv ℝ (cI i) xhat) p) else 0))) := by
    -- Combine the objective, equality, and inequality limits termwise.
    exact (hf.add hEqScaled).add hIneqScaled
  simpa [hActiveSum, add_assoc] using htotal

end «problem-150»
