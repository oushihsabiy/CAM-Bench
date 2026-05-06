import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-188»

open Set

/- [BLOCK Exercise 14.17 | 21 | thm]
Let x^{min},x^{max} ∈ ℝ satisfy x^{min} ≤ 0 ≤ x^{max}, and let φ:[x^{min},x^{max}] → ℝ be
differentiable. Assume φ(x) ≥ 0 quad for all x ∈ [0,x^{max}], φ(x) ≤ 0 quad for all x ∈ [x^{min},0].
Define E:[x^{min},x^{max}] → ℝ, E(x)=∈t₀^x φ(t)dt. Show that E is quasiconvex on [x^{min},x^{max}].
-/
/-- The energy increment between two points is the integral over the intervening interval. -/
lemma energy_increment_eq_intervalIntegral
    {xMin xMax : ℝ}
    (hord : xMin ≤ 0 ∧ 0 ≤ xMax)
    {φ : ℝ → ℝ}
    (hφ_diff : DifferentiableOn ℝ φ (Set.Icc xMin xMax))
    {x y : ℝ}
    (hx : x ∈ Set.Icc xMin xMax)
    (hy : y ∈ Set.Icc xMin xMax) :
    (∫ t in 0..y, φ t) - ∫ t in 0..x, φ t = ∫ t in x..y, φ t := by
  -- Pass from differentiability to continuity so interval integrability is automatic on compact pieces.
  have hφ_cont : ContinuousOn φ (Set.Icc xMin xMax) := hφ_diff.continuousOn
  have h0_mem : (0 : ℝ) ∈ Set.Icc xMin xMax := hord
  have h0y :
      IntervalIntegrable φ MeasureTheory.volume 0 y :=
    (hφ_cont.mono (Set.uIcc_subset_Icc h0_mem hy)).intervalIntegrable
  have h0x :
      IntervalIntegrable φ MeasureTheory.volume 0 x :=
    (hφ_cont.mono (Set.uIcc_subset_Icc h0_mem hx)).intervalIntegrable
  -- The interval-integral subtraction identity exactly matches the desired energy increment formula.
  simpa using intervalIntegral.integral_interval_sub_left h0y h0x

/-- The energy is antitone on the nonpositive side because the integrand there is nonpositive. -/
lemma energy_antitoneOn_left
    {xMin xMax : ℝ}
    (hord : xMin ≤ 0 ∧ 0 ≤ xMax)
    {φ : ℝ → ℝ}
    (hφ_diff : DifferentiableOn ℝ φ (Set.Icc xMin xMax))
    (hφ_nonpos : ∀ x ∈ Set.Icc xMin (0 : ℝ), φ x ≤ 0) :
    AntitoneOn (fun x => ∫ t in 0..x, φ t) (Set.Icc xMin 0) := by
  intro x hx y hy hxy
  have hx' : x ∈ Set.Icc xMin xMax := ⟨hx.1, hx.2.trans hord.2⟩
  have hy' : y ∈ Set.Icc xMin xMax := ⟨hy.1, hy.2.trans hord.2⟩
  have hincrement :=
    energy_increment_eq_intervalIntegral hord hφ_diff hx' hy'
  have hneg_nonneg : 0 ≤ ∫ t in x..y, -φ t := by
    -- On `[x,y] ⊆ [xMin,0]`, the negated integrand is pointwise nonnegative.
    refine intervalIntegral.integral_nonneg hxy ?_
    intro t ht
    have ht_left : t ∈ Set.Icc xMin (0 : ℝ) :=
      ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
    have hφt : φ t ≤ 0 := hφ_nonpos t ht_left
    simpa using neg_nonneg.mpr hφt
  have hinterval_nonpos : ∫ t in x..y, φ t ≤ 0 := by
    -- Rewriting the integral of `-φ` converts the nonnegativity statement into the desired upper bound.
    simpa [intervalIntegral.integral_neg] using hneg_nonneg
  -- Convert the interval-integral sign into the claimed order relation for the energy.
  exact sub_nonpos.mp <| by simpa [hincrement] using hinterval_nonpos

/-- The energy is monotone on the nonnegative side because the integrand there is nonnegative. -/
lemma energy_monotoneOn_right
    {xMin xMax : ℝ}
    (hord : xMin ≤ 0 ∧ 0 ≤ xMax)
    {φ : ℝ → ℝ}
    (hφ_diff : DifferentiableOn ℝ φ (Set.Icc xMin xMax))
    (hφ_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) xMax, 0 ≤ φ x) :
    MonotoneOn (fun x => ∫ t in 0..x, φ t) (Set.Icc 0 xMax) := by
  intro x hx y hy hxy
  have hx' : x ∈ Set.Icc xMin xMax := ⟨hord.1.trans hx.1, hx.2⟩
  have hy' : y ∈ Set.Icc xMin xMax := ⟨hord.1.trans hy.1, hy.2⟩
  have hincrement :=
    energy_increment_eq_intervalIntegral hord hφ_diff hx' hy'
  have hinterval_nonneg : 0 ≤ ∫ t in x..y, φ t := by
    -- On `[x,y] ⊆ [0,xMax]`, the integrand is pointwise nonnegative.
    refine intervalIntegral.integral_nonneg hxy ?_
    intro t ht
    have ht_right : t ∈ Set.Icc (0 : ℝ) xMax :=
      ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
    exact hφ_nonneg t ht_right
  -- Convert the interval-integral sign into monotonicity of the accumulated energy.
  exact sub_nonneg.mp <| by simpa [hincrement] using hinterval_nonneg

/-- For ordered endpoints, the energy at a convex combination is bounded by an endpoint value. -/
lemma integral_sign_split_quasiconvex_case_split
    {xMin xMax : ℝ}
    (hord : xMin ≤ 0 ∧ 0 ≤ xMax)
    {φ : ℝ → ℝ}
    (hφ_diff : DifferentiableOn ℝ φ (Set.Icc xMin xMax))
    (hφ_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) xMax, 0 ≤ φ x)
    (hφ_nonpos : ∀ x ∈ Set.Icc xMin (0 : ℝ), φ x ≤ 0)
    {x y a b : ℝ}
    (hx : x ∈ Set.Icc xMin xMax)
    (hy : y ∈ Set.Icc xMin xMax)
    (hxy : x ≤ y)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hab : a + b = 1) :
    (∫ t in 0..(a • x + b • y), φ t) ≤
      max (∫ t in 0..x, φ t) (∫ t in 0..y, φ t) := by
  let E : ℝ → ℝ := fun z => ∫ t in 0..z, φ t
  have hanti : AntitoneOn E (Set.Icc xMin 0) :=
    energy_antitoneOn_left hord hφ_diff hφ_nonpos
  have hmono : MonotoneOn E (Set.Icc 0 xMax) :=
    energy_monotoneOn_right hord hφ_diff hφ_nonneg
  let z : ℝ := a • x + b • y
  have hz_segment : z ∈ Set.Icc x y := by
    -- The convex combination stays inside the ordered interval `[x,y]`.
    have hx_seg : x ∈ Set.Icc x y := ⟨le_rfl, hxy⟩
    have hy_seg : y ∈ Set.Icc x y := ⟨hxy, le_rfl⟩
    simpa [z] using (convex_Icc x y) hx_seg hy_seg ha hb hab
  by_cases hy_nonpos : y ≤ 0
  · -- If both endpoints are on the left of the origin, antitonicity bounds the middle point by `x`.
    have hx_left : x ∈ Set.Icc xMin (0 : ℝ) := ⟨hx.1, hxy.trans hy_nonpos⟩
    have hz_left : z ∈ Set.Icc xMin (0 : ℝ) :=
      ⟨hx.1.trans hz_segment.1, hz_segment.2.trans hy_nonpos⟩
    have hz_le : E z ≤ E x := hanti hx_left hz_left hz_segment.1
    exact hz_le.trans (le_max_left _ _)
  · by_cases hx_nonneg : 0 ≤ x
    · -- If both endpoints are on the right of the origin, monotonicity bounds the middle point by `y`.
      have hy_right : y ∈ Set.Icc (0 : ℝ) xMax := ⟨hx_nonneg.trans hxy, hy.2⟩
      have hz_right : z ∈ Set.Icc (0 : ℝ) xMax :=
        ⟨hx_nonneg.trans hz_segment.1, hz_segment.2.trans hy.2⟩
      have hz_le : E z ≤ E y := hmono hz_right hy_right hz_segment.2
      exact hz_le.trans (le_max_right _ _)
    · -- In the mixed-sign case, the convex combination is controlled by whichever side of `0` it lands on.
      have hx_nonpos : x ≤ 0 := le_of_not_ge hx_nonneg
      have hy_nonneg : 0 ≤ y := le_of_lt (lt_of_not_ge hy_nonpos)
      have hx_left : x ∈ Set.Icc xMin (0 : ℝ) := ⟨hx.1, hx_nonpos⟩
      have hy_right : y ∈ Set.Icc (0 : ℝ) xMax := ⟨hy_nonneg, hy.2⟩
      rcases le_total z 0 with hz_nonpos | hz_nonneg
      · have hz_left : z ∈ Set.Icc xMin (0 : ℝ) := ⟨hx.1.trans hz_segment.1, hz_nonpos⟩
        have hz_le : E z ≤ E x := hanti hx_left hz_left hz_segment.1
        exact hz_le.trans (le_max_left _ _)
      · have hz_right : z ∈ Set.Icc (0 : ℝ) xMax := ⟨hz_nonneg, hz_segment.2.trans hy.2⟩
        have hz_le : E z ≤ E y := hmono hz_right hy_right hz_segment.2
        exact hz_le.trans (le_max_right _ _)

theorem integral_sign_split_quasiconvex
    {xMin xMax : ℝ}
    (hord : xMin ≤ 0 ∧ 0 ≤ xMax)
    {φ : ℝ → ℝ}
    (hφ_diff : DifferentiableOn ℝ φ (Set.Icc xMin xMax))
    (hφ_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) xMax, 0 ≤ φ x)
    (hφ_nonpos : ∀ x ∈ Set.Icc xMin (0 : ℝ), φ x ≤ 0) :
    QuasiconvexOn ℝ (Set.Icc xMin xMax) (fun x => ∫ t in 0..x, φ t) := by
  -- Rewrite quasiconvexity on an interval as the endpoint bound for convex combinations.
  rw [quasiconvexOn_iff_le_max]
  refine ⟨convex_Icc xMin xMax, ?_⟩
  intro x hx y hy a b ha hb hab
  rcases le_total x y with hxy | hyx
  · -- In the ordered case, use the dedicated sign-split estimate.
    exact integral_sign_split_quasiconvex_case_split hord hφ_diff hφ_nonneg hφ_nonpos
      hx hy hxy ha hb hab
  · -- Swapping the endpoints reduces the reverse-ordered case to the previous one.
    simpa [max_comm, add_comm, add_left_comm, add_assoc] using
      (integral_sign_split_quasiconvex_case_split hord hφ_diff hφ_nonneg hφ_nonpos
        hy hx hyx hb ha (by simpa [add_comm] using hab))

/- [BLOCK Exercise 14.17 | 22 | thm]
Let x^{min},x^{max} ∈ ℝ satisfy x^{min} ≤ 0 ≤ x^{max}, and let φ:[x^{min},x^{max}] → ℝ be
differentiable. Assume φ(x) ≥ 0 quad for all x ∈ [0,x^{max}], φ(x) ≤ 0 quad for all x ∈ [x^{min},0].
Define E:[x^{min},x^{max}] → ℝ, E(x)=∈t₀^x φ(t)dt. A spring is called monotonic if φ is
nondecreasing on [x^{min},x^{max}], meaning that for all x₁,x₂ ∈ [x^{min},x^{max}], x₁ ≤ x₂ implies
φ(x₁) ≤ φ(x₂). Show that E is convex on [x^{min},x^{max}] if and only if the spring is monotonic.
-/
/-- The primitive `x ↦ ∫ t in 0..x, φ t` has derivative `φ x` within the closed interval. -/
lemma energy_hasDerivWithinAt_eq_integrand
    {xMin xMax : ℝ}
    (hord : xMin ≤ 0 ∧ 0 ≤ xMax)
    {φ : ℝ → ℝ}
    (hφ_diff : DifferentiableOn ℝ φ (Set.Icc xMin xMax))
    {x : ℝ}
    (hx : x ∈ Set.Icc xMin xMax) :
    HasDerivWithinAt (fun z => ∫ t in 0..z, φ t) (φ x) (Set.Icc xMin xMax) x := by
  -- Pass from differentiability to continuity so the FTC hypotheses are available on every subinterval.
  have hφ_cont : ContinuousOn φ (Set.Icc xMin xMax) := hφ_diff.continuousOn
  have h0_mem : (0 : ℝ) ∈ Set.Icc xMin xMax := hord
  have h_int : IntervalIntegrable φ MeasureTheory.volume 0 x :=
    (hφ_cont.mono (Set.uIcc_subset_Icc h0_mem hx)).intervalIntegrable
  -- The closed interval membership provides the `FTCFilter` instance at `x`.
  have : Fact (x ∈ Set.Icc xMin xMax) := ⟨hx⟩
  -- Apply the interval FTC to the right endpoint variable of the primitive.
  exact intervalIntegral.integral_hasDerivWithinAt_right h_int
    (hφ_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x)
    (hφ_cont.continuousWithinAt hx)

/-- The derivative within the closed interval of the primitive is the integrand itself. -/
lemma energy_derivWithin_eq_integrand
    {xMin xMax : ℝ}
    (hord : xMin ≤ 0 ∧ 0 ≤ xMax)
    (hstrict : xMin < xMax)
    {φ : ℝ → ℝ}
    (hφ_diff : DifferentiableOn ℝ φ (Set.Icc xMin xMax))
    {x : ℝ}
    (hx : x ∈ Set.Icc xMin xMax) :
    derivWithin (fun z => ∫ t in 0..z, φ t) (Set.Icc xMin xMax) x = φ x := by
  -- On a genuine interval, uniqueness of the derivative within `Icc` lets us read off `derivWithin`.
  exact (energy_hasDerivWithinAt_eq_integrand hord hφ_diff hx).derivWithin
    ((uniqueDiffOn_Icc hstrict).uniqueDiffWithinAt hx)

/-- On interior points, the ordinary derivative of the primitive is the integrand. -/
lemma energy_deriv_eq_integrand_on_interior
    {xMin xMax : ℝ}
    (hord : xMin ≤ 0 ∧ 0 ≤ xMax)
    {φ : ℝ → ℝ}
    (hφ_diff : DifferentiableOn ℝ φ (Set.Icc xMin xMax))
    {x : ℝ}
    (hx : x ∈ interior (Set.Icc xMin xMax)) :
    deriv (fun z => ∫ t in 0..z, φ t) x = φ x := by
  have hxIcc : x ∈ Set.Icc xMin xMax := interior_subset hx
  have hIcc_nhds : Set.Icc xMin xMax ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  -- Upgrade the within-derivative to an ambient derivative because interior points see the full interval.
  exact (energy_hasDerivWithinAt_eq_integrand hord hφ_diff hxIcc).hasDerivAt hIcc_nhds |>.deriv

theorem integral_energy_convex_iff_monotone
    {xMin xMax : ℝ}
    (hord : xMin ≤ 0 ∧ 0 ≤ xMax)
    {φ : ℝ → ℝ}
    (hφ_diff : DifferentiableOn ℝ φ (Set.Icc xMin xMax))
    (hφ_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) xMax, 0 ≤ φ x)
    (hφ_nonpos : ∀ x ∈ Set.Icc xMin (0 : ℝ), φ x ≤ 0) :
    ConvexOn ℝ (Set.Icc xMin xMax) (fun x => ∫ t in 0..x, φ t) ↔
      MonotoneOn φ (Set.Icc xMin xMax) := by
  let E : ℝ → ℝ := fun x => ∫ t in 0..x, φ t
  have hφ_cont : ContinuousOn φ (Set.Icc xMin xMax) := hφ_diff.continuousOn
  have hxm : xMin ≤ xMax := hord.1.trans hord.2
  have h0_mem : (0 : ℝ) ∈ Set.Icc xMin xMax := hord
  have hE_cont : ContinuousOn E (Set.Icc xMin xMax) := by
    -- Continuity of the primitive on the whole interval comes from interval-integrability of `φ`.
    simpa [E, Set.uIcc_of_le hxm] using
      (intervalIntegral.continuousOn_primitive_interval' (μ := MeasureTheory.volume)
        (b₁ := xMin) (b₂ := xMax) (a := 0)
        (hφ_cont.intervalIntegrable_of_Icc hxm) (by simpa [Set.uIcc_of_le hxm] using h0_mem))
  constructor
  · intro hconv
    by_cases hstrict : xMin < xMax
    · have hE_diff : DifferentiableOn ℝ E (Set.Icc xMin xMax) := by
        intro x hx
        -- The within-FTC helper already gives differentiability on the closed interval.
        exact (energy_hasDerivWithinAt_eq_integrand hord hφ_diff hx).differentiableWithinAt
      have hE_mono : MonotoneOn (derivWithin E (Set.Icc xMin xMax)) (Set.Icc xMin xMax) :=
        hconv.monotoneOn_derivWithin hE_diff
      intro x hx y hy hxy
      -- Replace the derivative-within of the primitive by `φ` at both endpoints.
      rw [← energy_derivWithin_eq_integrand hord hstrict hφ_diff hx,
        ← energy_derivWithin_eq_integrand hord hstrict hφ_diff hy]
      exact hE_mono hx hy hxy
    · have hxeq : xMin = xMax := le_antisymm hxm (le_of_not_gt hstrict)
      have hxMin0 : xMin = 0 := le_antisymm hord.1 (by simpa [hxeq] using hord.2)
      have hxMax0 : xMax = 0 := hxeq.symm.trans hxMin0
      -- In the degenerate case `[xMin, xMax] = {0}`, monotonicity is automatic.
      subst xMin
      subst xMax
      simp [Set.Icc_self]
  · intro hmono
    have hE_diff : DifferentiableOn ℝ E (interior (Set.Icc xMin xMax)) := by
      intro x hx
      -- Interior points allow us to turn the FTC within-derivative into an ambient differentiability fact.
      have hxIcc : x ∈ Set.Icc xMin xMax := interior_subset hx
      have hIcc_nhds : Set.Icc xMin xMax ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
      exact ((energy_hasDerivWithinAt_eq_integrand hord hφ_diff hxIcc).hasDerivAt hIcc_nhds).differentiableAt.differentiableWithinAt
    have hE_deriv_mono : MonotoneOn (deriv E) (interior (Set.Icc xMin xMax)) := by
      intro x hx y hy hxy
      -- Rewrite the derivative of the primitive back to `φ`, then use monotonicity of `φ` on the ambient interval.
      rw [energy_deriv_eq_integrand_on_interior hord hφ_diff hx,
        energy_deriv_eq_integrand_on_interior hord hφ_diff hy]
      exact hmono (interior_subset hx) (interior_subset hy) hxy
    -- Apply the standard one-dimensional criterion: monotone derivative implies convexity.
    exact hE_deriv_mono.convexOn_of_deriv (convex_Icc xMin xMax) hE_cont hE_diff

end «problem-188»
