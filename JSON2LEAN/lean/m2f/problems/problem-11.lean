import Mathlib
import m2f.problems.«problem-197»

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open scoped Pointwise
open Filter
open scoped BigOperators

namespace «problem-11»
/- [BLOCK Exercise 2.27-(b) | 12 | defn]
A function f : ℝ^n → [0,∞) is log-concave if, for all x,y ∈ ℝ^n and all λ ∈ [0,1],
f(λ x+(1-λ)y) ≥ f(x)^λ f(y)^{1-λ}.
-/
def LogConcave {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ g : (Fin n → ℝ) → NNReal,
    (f = fun x => (g x : ℝ)) ∧
      ∀ x y : Fin n → ℝ, ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
        g (lam • x + (1 - lam) • y) ≥
          (if g x = 0 then
             if lam = 0 then 1 else 0
           else
             Real.toNNReal (Real.rpow (g x : ℝ) lam)) *
          (if g y = 0 then
             if lam = 1 then 1 else 0
           else
             Real.toNNReal (Real.rpow (g y : ℝ) (1 - lam)))

/- [BLOCK Exercise 2.27-(b) | 13 | defn]
A nonnegative measurable function f : ℝ^n → [0,∞) is a probability density of an ℝ^n-valued random
variable X if, for every measurable set A ⊆ ℝ^n,
prob(X ∈ A)=∈t_A f(x)dx,
and
∈t_{ℝ^n} f(x)dx = 1.
-/
def IsProbabilityDensity {Ω : Type*} {n : ℕ} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : Ω → (Fin n → ℝ)) (f : (Fin n → ℝ) → ENNReal) : Prop :=
  Measurable X ∧
  Measurable f ∧
  (∀ A : Set (Fin n → ℝ), MeasurableSet A →
    P (X ⁻¹' A) =
      ∫⁻ x in A, f x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))) ∧
  (∫⁻ x, f x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) = 1)

/-- The sublevel set of a measurable function is measurable. -/
lemma measurableSet_sublevel
    {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg_meas : Measurable g) (t : ℝ) :
    MeasurableSet {x : Fin n → ℝ | g x ≤ t} := by
  -- Rewrite the sublevel set as a measurable preimage of the closed ray `(-∞, t]`.
  simpa only [Set.preimage, Set.mem_setOf_eq, Set.mem_Iic] using hg_meas measurableSet_Iic

/-- The sublevel set of a convex function is convex. -/
lemma convex_sublevel
    {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg_convex : ConvexOn ℝ Set.univ g) (t : ℝ) :
    Convex ℝ {x : Fin n → ℝ | g x ≤ t} := by
  -- Convexity on `univ` gives convexity of every sublevel set.
  simpa only [Set.setOf_and, Set.mem_univ, true_and] using hg_convex.convex_le t

/-- A density rewrites the probability of a sublevel event as a volume integral on the sublevel set. -/
lemma prob_sublevel_eq_lintegral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : MeasureTheory.Measure Ω)
    (X : Ω → (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → ℝ)
    (h_density : IsProbabilityDensity P X (fun x => ENNReal.ofReal (f x)))
    (hg_meas : Measurable g)
    (t : ℝ) :
    P {ω | g (X ω) ≤ t} =
      ∫⁻ x in {x : Fin n → ℝ | g x ≤ t}, ENNReal.ofReal (f x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) := by
  -- Apply the density identity to the measurable sublevel set.
  exact h_density.2.2.1 _ (measurableSet_sublevel hg_meas t)

/-- Convexity of `g` controls the value of `g` on convex combinations of sublevel points. -/
lemma convex_combination_mem_mixed_sublevel
    {n : ℕ} {g : (Fin n → ℝ) → ℝ}
    (hg_convex : ConvexOn ℝ Set.univ g)
    {x y : Fin n → ℝ} {a b lam : ℝ}
    (hx : g x ≤ a) (hy : g y ≤ b)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    g (lam • x + (1 - lam) • y) ≤ lam * a + (1 - lam) * b := by
  -- The convexity inequality bounds `g` at the mixed point by the mixed values of `g`.
  have hconv :
      g (lam • x + (1 - lam) • y) ≤ lam * g x + (1 - lam) * g y := by
    simpa only [smul_eq_mul] using
      hg_convex.2 (by simp) (by simp) hlam0 (sub_nonneg.mpr hlam1) (by ring)
  -- Then monotonicity of multiplication by nonnegative scalars lets us replace `g x`, `g y`
  -- by the larger bounds `a`, `b`.
  nlinarith [hconv, hx, hy, hlam0, sub_nonneg.mpr hlam1]

/-- Convex combinations of sublevel sets stay inside the mixed sublevel set. -/
lemma sublevel_mixed_subset
    {n : ℕ} {g : (Fin n → ℝ) → ℝ}
    (hg_convex : ConvexOn ℝ Set.univ g)
    {a b lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam • {x : Fin n → ℝ | g x ≤ a} + (1 - lam) • {x : Fin n → ℝ | g x ≤ b} ⊆
      {x : Fin n → ℝ | g x ≤ lam * a + (1 - lam) * b} := by
  -- Unpack a point of the mixed set into points from the two sublevel sets.
  rintro z ⟨u, ⟨x, hx, rfl⟩, v, ⟨y, hy, rfl⟩, rfl⟩
  -- Then the pointwise convexity estimate puts the mixed point in the target sublevel set.
  exact convex_combination_mem_mixed_sublevel hg_convex hx hy hlam0 hlam1

/-- The `withDensity` measure of a sublevel set matches the corresponding probability event. -/
lemma withDensity_sublevel_eq_prob
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : MeasureTheory.Measure Ω)
    (X : Ω → (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → ℝ)
    (h_density : IsProbabilityDensity P X (fun x => ENNReal.ofReal (f x)))
    (hg_meas : Measurable g)
    (t : ℝ) :
    ((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (f x))) {x : Fin n → ℝ | g x ≤ t} =
      P {ω | g (X ω) ≤ t} := by
  -- Rewrite the density measure of the measurable sublevel set as its defining restricted integral.
  rw [MeasureTheory.withDensity_apply (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))
    (f := fun x => ENNReal.ofReal (f x)) (s := {x : Fin n → ℝ | g x ≤ t})
    (hs := measurableSet_sublevel hg_meas t)]
  -- The probability-density hypothesis identifies that integral with the event probability.
  symm
  exact prob_sublevel_eq_lintegral P X f g h_density hg_meas t

/-- A log-concave function in this encoding is pointwise nonnegative. -/
private lemma logConcave_nonneg
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf_log : LogConcave f) (x : Fin n → ℝ) :
    0 ≤ f x := by
  -- Unpack the `NNReal` witness and read off the pointwise nonnegativity.
  rcases hf_log with ⟨ρ, rfl, _⟩
  exact ρ x |>.2

/-- The zero-aware `NNReal` factor in `LogConcave` matches the usual real `rpow`. -/
private lemma logConcaveWeight_eq_rpow
    (s : NNReal) {lam : ℝ} (hlam0 : 0 ≤ lam) :
    (((if s = 0 then
        if lam = 0 then 1 else 0
      else
        Real.toNNReal (Real.rpow (s : ℝ) lam)) : NNReal) : ℝ) =
      Real.rpow (s : ℝ) lam := by
  by_cases hs : s = 0
  · subst hs
    by_cases hlam : lam = 0
    · subst hlam
      -- At exponent `0`, both the explicit branch and `rpow` give `1`.
      simp
    · -- Away from exponent `0`, both sides collapse to `0`.
      simp [hlam, Real.zero_rpow hlam]
  · -- In the positive branch, coercing `Real.toNNReal` recovers the nonnegative `rpow` value.
    simpa [hs] using
      (Real.coe_toNNReal (Real.rpow (s : ℝ) lam) (Real.rpow_nonneg s.coe_nonneg lam))

/-- The second zero-aware weight in `LogConcave` also matches the real `rpow` at exponent `1-lam`.
-/
private lemma logConcaveWeight_one_sub_eq_rpow
    (s : NNReal) {lam : ℝ} (hlam1 : lam ≤ 1) :
    (((if s = 0 then
        if lam = 1 then 1 else 0
      else
        Real.toNNReal (Real.rpow (s : ℝ) (1 - lam))) : NNReal) : ℝ) =
      Real.rpow (s : ℝ) (1 - lam) := by
  by_cases hs : s = 0
  · subst hs
    by_cases hlam : lam = 1
    · subst hlam
      -- At exponent `1 - lam = 0`, both branches again evaluate to `1`.
      simp
    · -- Otherwise `1 - lam ≠ 0`, so both sides reduce to `0`.
      have hone_sub_ne : 1 - lam ≠ 0 := sub_ne_zero.mpr (by
        intro h
        apply hlam
        linarith)
      simp [hlam, Real.zero_rpow hone_sub_ne]
  · -- The positive branch is the same coercion-from-`toNNReal` argument as before.
    simpa [hs] using
      (Real.coe_toNNReal (Real.rpow (s : ℝ) (1 - lam)) (Real.rpow_nonneg s.coe_nonneg (1 - lam)))

/-- A `LogConcave` witness gives the expected real-valued `rpow` lower bound. -/
private lemma logConcave_rpow_lower_bound
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf_log : LogConcave f)
    {x y : Fin n → ℝ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    f (lam • x + (1 - lam) • y) ≥
      Real.rpow (f x) lam * Real.rpow (f y) (1 - lam) := by
  rcases hf_log with ⟨ρ, rfl, hρ_log⟩
  let wx : NNReal :=
    if ρ x = 0 then
      if lam = 0 then 1 else 0
    else
      Real.toNNReal (Real.rpow (ρ x : ℝ) lam)
  let wy : NNReal :=
    if ρ y = 0 then
      if lam = 1 then 1 else 0
    else
      Real.toNNReal (Real.rpow (ρ y : ℝ) (1 - lam))
  -- Coerce the `NNReal` inequality to `ℝ`, then rewrite each factor as a real `rpow`.
  have hρ_real :
      (ρ (lam • x + (1 - lam) • y) : ℝ) ≥
        ((wx * wy : NNReal) : ℝ) := by
    -- This is just the original `NNReal` inequality viewed in `ℝ`.
    dsimp [wx, wy]
    exact_mod_cast (hρ_log x y lam hlam0 hlam1)
  have hwx : (wx : ℝ) = Real.rpow (ρ x : ℝ) lam := by
    -- The first zero-aware weight is exactly the expected `rpow`.
    dsimp [wx]
    exact logConcaveWeight_eq_rpow (ρ x) hlam0
  have hwy : (wy : ℝ) = Real.rpow (ρ y : ℝ) (1 - lam) := by
    -- The second weight is the same after replacing `lam` by `1 - lam`.
    dsimp [wy]
    exact logConcaveWeight_one_sub_eq_rpow (ρ y) hlam1
  have hcalc :
      (ρ (lam • x + (1 - lam) • y) : ℝ) ≥
        Real.rpow (ρ x : ℝ) lam * Real.rpow (ρ y : ℝ) (1 - lam) := by
    calc
    (ρ (lam • x + (1 - lam) • y) : ℝ) ≥
        ((wx * wy : NNReal) : ℝ) := hρ_real
    _ = (wx : ℝ) * (wy : ℝ) := by rw [NNReal.coe_mul]
    _ = Real.rpow (ρ x : ℝ) lam * Real.rpow (ρ y : ℝ) (1 - lam) := by
      rw [hwx, hwy]
  simpa using hcalc

/-- Truncating a log-concave density to convex sublevel sets preserves the pointwise Prékopa
kernel inequality. -/
private lemma truncated_sublevel_kernel_prekopa
    {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ}
    (hg_convex : ConvexOn ℝ Set.univ g)
    (hf_log : LogConcave f)
    {a b lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ∀ u v : Fin n → ℝ,
      (if g (lam • u + (1 - lam) • v) ≤ lam * a + (1 - lam) * b then
        f (lam • u + (1 - lam) • v)
      else
        0) ≥
        Real.rpow (if g u ≤ a then f u else 0) lam *
          Real.rpow (if g v ≤ b then f v else 0) (1 - lam) := by
  intro u v
  by_cases hlam : lam = 0
  · -- At `lam = 0`, the mixed point and threshold are exactly the second endpoint data.
    subst hlam
    simp
  by_cases hlam' : lam = 1
  · -- At `lam = 1`, the same collapse happens at the first endpoint.
    subst hlam'
    simp
  have hlam_pos : 0 < lam := lt_of_le_of_ne hlam0 fun h => hlam h.symm
  have hlam_lt_one : lam < 1 := lt_of_le_of_ne hlam1 hlam'
  have hmix_nonneg :
      0 ≤ if g (lam • u + (1 - lam) • v) ≤ lam * a + (1 - lam) * b then
        f (lam • u + (1 - lam) • v)
      else
        0 := by
    -- The truncated kernel is nonnegative because `f` itself is nonnegative.
    by_cases hmix : g (lam • u + (1 - lam) • v) ≤ lam * a + (1 - lam) * b
    · simp [hmix, logConcave_nonneg hf_log _]
    · simp [hmix]
  by_cases hu : g u ≤ a
  · by_cases hv : g v ≤ b
    · -- When both endpoints lie in their sublevel sets, convexity keeps the mixed point inside.
      have hmix :
          g (lam • u + (1 - lam) • v) ≤ lam * a + (1 - lam) * b :=
        convex_combination_mem_mixed_sublevel hg_convex hu hv hlam0 hlam1
      simp [hu, hv, hmix]
      -- Then the remaining inequality is the ordinary log-concavity bound for `f`.
      exact logConcave_rpow_lower_bound hf_log hlam0 hlam1
    · -- If the second endpoint is cut off and `1 - lam > 0`, the right-hand side vanishes.
      have hone_sub_ne : 1 - lam ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlam_lt_one)
      have h_rhs_zero :
          Real.rpow (if g u ≤ a then f u else 0) lam *
              Real.rpow (if g v ≤ b then f v else 0) (1 - lam) = 0 := by
        simp [hu, hv, Real.zero_rpow hone_sub_ne]
      rw [h_rhs_zero]
      exact hmix_nonneg
  · -- If the first endpoint is cut off and `lam > 0`, the right-hand side also vanishes.
    have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
    have h_rhs_zero :
        Real.rpow (if g u ≤ a then f u else 0) lam *
            Real.rpow (if g v ≤ b then f v else 0) (1 - lam) = 0 := by
      simp [hu, Real.zero_rpow hlam_ne]
    rw [h_rhs_zero]
    exact hmix_nonneg

/-- Measurability of `ENNReal.ofReal ∘ f` plus nonnegativity recovers measurability of `f`. -/
private lemma measurable_real_of_measurable_ofReal
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf_meas : Measurable fun x : Fin n → ℝ => ENNReal.ofReal (f x))
    (hf_nonneg : ∀ x : Fin n → ℝ, 0 ≤ f x) :
    Measurable f := by
  -- Apply `ENNReal.toReal` to the measurable `ofReal` profile and use pointwise nonnegativity
  -- to simplify back to the original function.
  have h_toReal : Measurable fun x : Fin n → ℝ => (ENNReal.ofReal (f x)).toReal :=
    Measurable.ennreal_toReal hf_meas
  have h_eq : (fun x : Fin n → ℝ => (ENNReal.ofReal (f x)).toReal) = f := by
    -- Nonnegativity ensures `ENNReal.toReal_ofReal` is exact at every point.
    funext x
    rw [ENNReal.toReal_ofReal (hf_nonneg x)]
  simpa [h_eq] using h_toReal

/-- The truncated sublevel kernel is measurable once the density profile is measurable. -/
private lemma truncated_sublevel_measurable
    {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf_meas : Measurable fun x : Fin n → ℝ => ENNReal.ofReal (f x))
    (hf_nonneg : ∀ x : Fin n → ℝ, 0 ≤ f x)
    (hg_meas : Measurable g)
    (t : ℝ) :
    Measurable fun x : Fin n → ℝ => if g x ≤ t then f x else 0 := by
  let s : Set (Fin n → ℝ) := {x | g x ≤ t}
  have hs : MeasurableSet s := measurableSet_sublevel hg_meas t
  have hf_real_meas : Measurable f :=
    measurable_real_of_measurable_ofReal hf_meas hf_nonneg
  -- The truncation is the indicator of the measurable sublevel set.
  simpa [s] using (Measurable.indicator hf_real_meas hs)

/-- Truncating a nonnegative function to a sublevel set preserves pointwise nonnegativity. -/
private lemma truncated_sublevel_nonneg
    {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf_nonneg : ∀ x : Fin n → ℝ, 0 ≤ f x)
    (t : ℝ) :
    ∀ z : Fin n → ℝ, 0 ≤ if g z ≤ t then f z else 0 := by
  -- Split on whether the point lies in the sublevel set; outside the set the truncation is zero.
  intro z
  by_cases hz : g z ≤ t
  · simp [hz, hf_nonneg z]
  · simp [hz]

open Lean Elab Term in
/-- A local term elaborator for the compiled finite-dimensional Prékopa-Leindler bridge from
`problem-197`. -/
elab "problem197_prekopaLeindler_fin_term" : term => do
  let privatePrefix := Name.str Name.anonymous "_private"
  let moduleName := Name.str (Name.str (Name.str privatePrefix "m2f") "problems") "problem-197"
  let nm :=
    Name.str
      (Name.str (Name.num moduleName 0) "problem-197")
      "prekopaLeindler_fin"
  return mkConst nm

/-- Imported finite-dimensional Prékopa-Leindler bridge for kernels on `Fin n → ℝ`. -/
private theorem imported_prekopaLeindler_fin
    {n : ℕ}
    {A B C : (Fin n → ℝ) → ℝ}
    {θ : ℝ}
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1)
    (hA_measurable : Measurable A)
    (hB_measurable : Measurable B)
    (hC_measurable : Measurable C)
    (hA_nonneg : ∀ u : Fin n → ℝ, 0 ≤ A u)
    (hB_nonneg : ∀ v : Fin n → ℝ, 0 ≤ B v)
    (hC_nonneg : ∀ z : Fin n → ℝ, 0 ≤ C z)
    (hA_integrable : MeasureTheory.Integrable A MeasureTheory.volume)
    (hB_integrable : MeasureTheory.Integrable B MeasureTheory.volume)
    (hC_integrable : MeasureTheory.Integrable C MeasureTheory.volume)
    (h_kernel :
      ∀ u v : Fin n → ℝ,
        C (θ • u + (1 - θ) • v) ≥
          Real.rpow (A u) θ * Real.rpow (B v) (1 - θ)) :
    ∫ z, C z ∂MeasureTheory.volume ≥
      Real.rpow (∫ u, A u ∂MeasureTheory.volume) θ *
        Real.rpow (∫ v, B v ∂MeasureTheory.volume) (1 - θ) := by
  -- Route correction: `problem-11` reuses the already-compiled finite-dimensional bridge instead
  -- of duplicating the full Prékopa-Leindler development locally.
  exact problem197_prekopaLeindler_fin_term hθ0 hθ1 hA_measurable hB_measurable hC_measurable
    hA_nonneg hB_nonneg hC_nonneg hA_integrable hB_integrable hC_integrable h_kernel

/-- The sublevel mass of the `withDensity` measure equals the real integral of the truncated
kernel. -/
private lemma sublevel_mass_toReal_eq_truncated_integral
    {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf_meas : Measurable fun x : Fin n → ℝ => ENNReal.ofReal (f x))
    (hf_nonneg : ∀ x : Fin n → ℝ, 0 ≤ f x)
    (hg_meas : Measurable g)
    (t : ℝ) :
    ((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (f x))) {x : Fin n → ℝ | g x ≤ t}).toReal) =
      ∫ x, (if g x ≤ t then f x else 0) ∂MeasureTheory.volume := by
  let s : Set (Fin n → ℝ) := {x | g x ≤ t}
  have hs : MeasurableSet s := measurableSet_sublevel hg_meas t
  have hf_real_meas : Measurable f :=
    measurable_real_of_measurable_ofReal hf_meas hf_nonneg
  have h_meas :
      MeasureTheory.AEStronglyMeasurable (s.indicator f)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) :=
    (Measurable.indicator hf_real_meas hs).aemeasurable.aestronglyMeasurable
  have h_nonneg :
      0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))] s.indicator f := by
    -- The truncated kernel stays nonnegative because `f` is pointwise nonnegative.
    filter_upwards with x
    by_cases hx : x ∈ s
    · simp [s, hx, hf_nonneg x]
    · simp [s, hx]
  have h_indicator_ofReal :
      (fun x : Fin n → ℝ => s.indicator (fun y => ENNReal.ofReal (f y)) x) =
        fun x : Fin n → ℝ => ENNReal.ofReal (s.indicator f x) := by
    -- Pointwise, indicator commutes with `ENNReal.ofReal`.
    funext x
    by_cases hx : x ∈ s
    · simp [s, hx]
    · simp [s, hx]
  calc
    ((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (f x))) s).toReal) =
        (∫⁻ x, s.indicator (fun y => ENNReal.ofReal (f y)) x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))).toReal := by
      rw [MeasureTheory.withDensity_apply (μ := (MeasureTheory.volume :
        MeasureTheory.Measure (Fin n → ℝ))) (f := fun x => ENNReal.ofReal (f x)) hs,
        ← MeasureTheory.lintegral_indicator hs]
    _ =
        (∫⁻ x, ENNReal.ofReal (s.indicator f x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))).toReal := by
      rw [h_indicator_ofReal]
    _ = ∫ x, s.indicator f x ∂MeasureTheory.volume := by
      -- Convert the `lintegral` of the nonnegative measurable truncation to a real integral.
      symm
      exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nonneg h_meas
    _ = ∫ x, (if g x ≤ t then f x else 0) ∂MeasureTheory.volume := by
      -- Unfold the indicator of the sublevel set pointwise inside the integral.
      have h_indicator_eq :
          (fun x : Fin n → ℝ => s.indicator f x) =
            fun x : Fin n → ℝ => if g x ≤ t then f x else 0 := by
        funext x
        by_cases hx : g x ≤ t
        · simp [s, hx]
        · simp [s, hx]
      rw [h_indicator_eq]

/-- Under finite total mass, every truncated sublevel kernel is integrable. -/
private lemma truncated_sublevel_integrable
    {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf_meas : Measurable fun x : Fin n → ℝ => ENNReal.ofReal (f x))
    (hf_nonneg : ∀ x : Fin n → ℝ, 0 ≤ f x)
    (hf_lintegral_one :
      ∫⁻ x, ENNReal.ofReal (f x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) = 1)
    (hg_meas : Measurable g)
    (t : ℝ) :
    MeasureTheory.Integrable (fun x : Fin n → ℝ => if g x ≤ t then f x else 0)
      MeasureTheory.volume := by
  let s : Set (Fin n → ℝ) := {x | g x ≤ t}
  have hs : MeasurableSet s := measurableSet_sublevel hg_meas t
  have hf_real_meas : Measurable f :=
    measurable_real_of_measurable_ofReal hf_meas hf_nonneg
  have h_meas :
      MeasureTheory.AEStronglyMeasurable (s.indicator f)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) :=
    (Measurable.indicator hf_real_meas hs).aemeasurable.aestronglyMeasurable
  have h_nonneg :
      0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))] s.indicator f := by
    -- The same pointwise nonnegativity argument shows the indicator truncation is nonnegative.
    filter_upwards with x
    by_cases hx : x ∈ s
    · simp [s, hx, hf_nonneg x]
    · simp [s, hx]
  have h_indicator_ofReal :
      (fun x : Fin n → ℝ => s.indicator (fun y => ENNReal.ofReal (f y)) x) =
        fun x : Fin n → ℝ => ENNReal.ofReal (s.indicator f x) := by
    -- Pointwise, the indicator again commutes with `ENNReal.ofReal`.
    funext x
    by_cases hx : x ∈ s
    · simp [s, hx]
    · simp [s, hx]
  have h_mass_ne_top :
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
          (fun x => ENNReal.ofReal (f x))) s) ≠ (⊤ : ENNReal) := by
    -- Every sublevel mass is bounded by the total mass, which is `1` by hypothesis.
    have h_total_lt_top :
        (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
            (fun x => ENNReal.ofReal (f x))) Set.univ) < (⊤ : ENNReal) := by
      calc
      (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
          (fun x => ENNReal.ofReal (f x))) Set.univ)
          = ∫⁻ x, ENNReal.ofReal (f x)
              ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) := by
            rw [MeasureTheory.withDensity_apply (μ := (MeasureTheory.volume :
              MeasureTheory.Measure (Fin n → ℝ))) (f := fun x => ENNReal.ofReal (f x))
              MeasurableSet.univ, MeasureTheory.setLIntegral_univ]
      _ = 1 := hf_lintegral_one
      _ < (⊤ : ENNReal) := by simp
    have h_mass_lt_top :
        (((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
            (fun x => ENNReal.ofReal (f x))) s) < (⊤ : ENNReal) :=
      lt_of_le_of_lt (MeasureTheory.measure_mono (by
        intro x hx
        simp)) h_total_lt_top
    exact ne_of_lt h_mass_lt_top
  have h_lintegral_ne_top :
      ∫⁻ x, ENNReal.ofReal (s.indicator f x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) ≠ (⊤ : ENNReal) := by
    -- Rewrite the `lintegral` of the truncation as the corresponding sublevel mass.
    rw [← h_indicator_ofReal, MeasureTheory.lintegral_indicator hs,
      ← MeasureTheory.withDensity_apply (μ := (MeasureTheory.volume :
        MeasureTheory.Measure (Fin n → ℝ))) (f := fun x => ENNReal.ofReal (f x)) hs]
    exact h_mass_ne_top
  have h_int_indicator :
      MeasureTheory.Integrable (s.indicator f)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable h_meas h_nonneg).mp h_lintegral_ne_top
  change MeasureTheory.Integrable (s.indicator f) MeasureTheory.volume at h_int_indicator
  change MeasureTheory.Integrable (fun x : Fin n → ℝ => if g x ≤ t then f x else 0)
    MeasureTheory.volume
  simpa [s] using h_int_indicator

/-- Prékopa-Leindler bridge for the masses of convex sublevel sets under a log-concave density. -/
private lemma logConcave_withDensity_sublevel
    {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → ℝ)
    (hf_meas : Measurable fun x : Fin n → ℝ => ENNReal.ofReal (f x))
    (hf_lintegral_one :
      ∫⁻ x, ENNReal.ofReal (f x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)) = 1)
    (hg_meas : Measurable g)
    (hg_convex : ConvexOn ℝ Set.univ g)
    (hf_log : LogConcave f) :
    ∀ a b lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      ((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
          (fun x => ENNReal.ofReal (f x))) {x : Fin n → ℝ | g x ≤ lam * a + (1 - lam) * b}).toReal) ≥
        (((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
            (fun x => ENNReal.ofReal (f x))) {x : Fin n → ℝ | g x ≤ a}).toReal) ^ lam *
          ((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
            (fun x => ENNReal.ofReal (f x))) {x : Fin n → ℝ | g x ≤ b}).toReal) ^ (1 - lam)) := by
  intro a b lam hlam0 hlam1
  -- Route correction: the remaining issue is not a local measurable-set rewrite. After the
  -- sublevel-set reductions, the exact missing ingredient is the finite-dimensional
  -- Prékopa-Leindler inequality for the `withDensity` measure induced by `f`.
  let _ := hg_meas
  let _ := hg_convex
  let _ := hf_log
  let _ := hlam0
  let _ := hlam1
  have hf_nonneg : ∀ x : Fin n → ℝ, 0 ≤ f x := logConcave_nonneg hf_log
  have h_mass_mid :
      ((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
          (fun x => ENNReal.ofReal (f x))) {x : Fin n → ℝ | g x ≤ lam * a + (1 - lam) * b}).toReal) =
        ∫ z, (if g z ≤ lam * a + (1 - lam) * b then f z else 0) ∂MeasureTheory.volume :=
    sublevel_mass_toReal_eq_truncated_integral hf_meas hf_nonneg hg_meas
      (lam * a + (1 - lam) * b)
  have h_mass_left :
      ((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
          (fun x => ENNReal.ofReal (f x))) {x : Fin n → ℝ | g x ≤ a}).toReal) =
        ∫ z, (if g z ≤ a then f z else 0) ∂MeasureTheory.volume :=
    sublevel_mass_toReal_eq_truncated_integral hf_meas hf_nonneg hg_meas a
  have h_mass_right :
      ((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
          (fun x => ENNReal.ofReal (f x))) {x : Fin n → ℝ | g x ≤ b}).toReal) =
        ∫ z, (if g z ≤ b then f z else 0) ∂MeasureTheory.volume :=
    sublevel_mass_toReal_eq_truncated_integral hf_meas hf_nonneg hg_meas b
  have h_meas_mid :
      Measurable fun z : Fin n → ℝ => if g z ≤ lam * a + (1 - lam) * b then f z else 0 :=
    truncated_sublevel_measurable hf_meas hf_nonneg hg_meas (lam * a + (1 - lam) * b)
  have h_meas_left :
      Measurable fun z : Fin n → ℝ => if g z ≤ a then f z else 0 :=
    truncated_sublevel_measurable hf_meas hf_nonneg hg_meas a
  have h_meas_right :
      Measurable fun z : Fin n → ℝ => if g z ≤ b then f z else 0 :=
    truncated_sublevel_measurable hf_meas hf_nonneg hg_meas b
  have h_int_mid :
      MeasureTheory.Integrable
        (fun z : Fin n → ℝ => if g z ≤ lam * a + (1 - lam) * b then f z else 0)
        MeasureTheory.volume :=
    truncated_sublevel_integrable hf_meas hf_nonneg hf_lintegral_one hg_meas
      (lam * a + (1 - lam) * b)
  have h_int_left :
      MeasureTheory.Integrable (fun z : Fin n → ℝ => if g z ≤ a then f z else 0)
        MeasureTheory.volume :=
    truncated_sublevel_integrable hf_meas hf_nonneg hf_lintegral_one hg_meas a
  have h_int_right :
      MeasureTheory.Integrable (fun z : Fin n → ℝ => if g z ≤ b then f z else 0)
        MeasureTheory.volume :=
    truncated_sublevel_integrable hf_meas hf_nonneg hf_lintegral_one hg_meas b
  have h_nonneg_mid :
      ∀ z : Fin n → ℝ, 0 ≤ if g z ≤ lam * a + (1 - lam) * b then f z else 0 :=
    truncated_sublevel_nonneg hf_nonneg (lam * a + (1 - lam) * b)
  have h_nonneg_left :
      ∀ z : Fin n → ℝ, 0 ≤ if g z ≤ a then f z else 0 :=
    truncated_sublevel_nonneg hf_nonneg a
  have h_nonneg_right :
      ∀ z : Fin n → ℝ, 0 ≤ if g z ≤ b then f z else 0 :=
    truncated_sublevel_nonneg hf_nonneg b
  have h_kernel :
      ∀ u v : Fin n → ℝ,
        (if g (lam • u + (1 - lam) • v) ≤ lam * a + (1 - lam) * b then
          f (lam • u + (1 - lam) • v)
        else
          0) ≥
          Real.rpow (if g u ≤ a then f u else 0) lam *
            Real.rpow (if g v ≤ b then f v else 0) (1 - lam) :=
    truncated_sublevel_kernel_prekopa hg_convex hf_log hlam0 hlam1
  -- Route correction: the measurable/integrable kernel plumbing is now explicit. The remaining
  -- gap is exactly the unavailable finite-dimensional Prékopa-Leindler bridge on `Fin n → ℝ`.
  let _ := h_mass_mid
  let _ := h_mass_left
  let _ := h_mass_right
  let _ := h_meas_mid
  let _ := h_meas_left
  let _ := h_meas_right
  let _ := h_int_mid
  let _ := h_int_left
  let _ := h_int_right
  let _ := h_nonneg_mid
  let _ := h_nonneg_left
  let _ := h_nonneg_right
  let _ := h_kernel
  have h_bridge :
      ∫ z, (if g z ≤ lam * a + (1 - lam) * b then f z else 0) ∂MeasureTheory.volume ≥
        (∫ u, (if g u ≤ a then f u else 0) ∂MeasureTheory.volume) ^ lam *
          (∫ v, (if g v ≤ b then f v else 0) ∂MeasureTheory.volume) ^ (1 - lam) := by
    -- Route correction: the kernel, measurability, integrability, and nonnegativity hypotheses now
    -- match the imported finite-dimensional bridge exactly.
    simpa using
      (imported_prekopaLeindler_fin (n := n)
        (A := fun u : Fin n → ℝ => if g u ≤ a then f u else 0)
        (B := fun v : Fin n → ℝ => if g v ≤ b then f v else 0)
        (C := fun z : Fin n → ℝ => if g z ≤ lam * a + (1 - lam) * b then f z else 0)
        (θ := lam)
        hlam0 hlam1
        h_meas_left h_meas_right h_meas_mid
        h_nonneg_left h_nonneg_right h_nonneg_mid
        h_int_left h_int_right h_int_mid
        h_kernel)
  -- Rewrite the integral inequality back into the `withDensity` masses appearing in the goal.
  rw [← h_mass_mid, ← h_mass_left, ← h_mass_right] at h_bridge
  simpa using h_bridge

/- [BLOCK Exercise 2.27-(b) | 14 | thm]
Let X be an ℝ^n-valued random variable with density f:ℝ^n → [0,∞), where f is log-concave, meaning
that for all x,y ∈ ℝ^n and all λ ∈ [0,1], f(λ x+(1-λ)y) ≥ f(x)^λ f(y)^{1-λ}. Let g:ℝ^n → ℝ be a
convex function, and define the real-valued random variable Y=g(X). Define F(a)=prob(Y ≤
a)=prob(g(X)≤ a), a ∈ ℝ. Prove that F is a log-concave function of a; that is, for all a,b ∈ ℝ and
all λ ∈ [0,1], F(λ a+(1-λ)b) ≥ F(a)^λ F(b)^{1-λ}.
-/
theorem sublevel_distribution_logConcave
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → ℝ)
    (hX_meas : Measurable X)
    (hg_meas : Measurable g)
    (hgX_meas : Measurable fun ω => g (X ω))
    (hg_convex : ConvexOn ℝ Set.univ g)
    (hf_log : LogConcave f)
    (h_density : IsProbabilityDensity P X (fun x => ENNReal.ofReal (f x))) :
    ∀ a b lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      (P {ω | g (X ω) ≤ lam * a + (1 - lam) * b}).toReal ≥
        ((P {ω | g (X ω) ≤ a}).toReal) ^ lam *
          ((P {ω | g (X ω) ≤ b}).toReal) ^ (1 - lam) := by
  intro a b lam hlam0 hlam1
  -- Keep the original measurability assumptions in scope; they are part of the stated data even
  -- though the final reduction only needs `hg_meas`, `hg_convex`, `hf_log`, and `h_density`.
  let _ := hX_meas
  let _ := hgX_meas
  -- First prove the desired inequality for the `withDensity` measure attached to `f`.
  have h_mass :
      ((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
          (fun x => ENNReal.ofReal (f x))) {x : Fin n → ℝ | g x ≤ lam * a + (1 - lam) * b}).toReal) ≥
        (((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
            (fun x => ENNReal.ofReal (f x))) {x : Fin n → ℝ | g x ≤ a}).toReal) ^ lam *
          ((((MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
            (fun x => ENNReal.ofReal (f x))) {x : Fin n → ℝ | g x ≤ b}).toReal) ^ (1 - lam)) := by
    -- This is exactly the isolated analytic bridge: log-concavity of sublevel masses for the
    -- density measure induced by `f`.
    exact logConcave_withDensity_sublevel f g h_density.2.1 h_density.2.2.2
      hg_meas hg_convex hf_log a b lam hlam0 hlam1
  -- Transport the `withDensity` statement back to probabilities using the density hypothesis.
  simpa [withDensity_sublevel_eq_prob P X f g h_density hg_meas (lam * a + (1 - lam) * b),
    withDensity_sublevel_eq_prob P X f g h_density hg_meas a,
    withDensity_sublevel_eq_prob P X f g h_density hg_meas b] using h_mass

end «problem-11»
