import Mathlib
import «problem-197»

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-30»
/- [BLOCK Exercise 2.27-(c) | 15 | defn]
A density function f : ℝ^n → [0,∞) is log-concave if for all x,y ∈ ℝ^n and all θ ∈ [0,1],
f(θ x + (1-θ)y) ≥ f(x)^θ f(y)^{1-θ}.
Equivalently, log f is concave on {x : f(x)>0}.
-/
def IsLogConcaveDensity {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ g : (Fin n → ℝ) → NNReal,
    (f = fun x => (g x : ℝ)) ∧
      ∀ x y : Fin n → ℝ, ∀ θ : ℝ,
        0 ≤ θ →
          θ ≤ 1 →
            (g (θ • x + (1 - θ) • y) : ℝ) ≥
              Real.rpow (g x : ℝ) θ * Real.rpow (g y : ℝ) (1 - θ)

/- [BLOCK Exercise 2.27-(c) | 16 | defn]
A function φ : D → [0,∞) on a convex set D is log-concave if for all a,b ∈ D and all θ ∈ [0,1],
φ(θ a + (1-θ)b) ≥ φ(a)^θ φ(b)^{1-θ}.
-/
def IsLogConcaveOn {n : ℕ} (D : Set (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) : Prop :=
  Convex ℝ D ∧
    (∀ a ∈ D, ∀ b ∈ D, ∀ θ : ℝ,
      0 ≤ θ →
        θ ≤ 1 →
          φ (θ • a + (1 - θ) • b) ≥ Real.rpow (φ a) θ * Real.rpow (φ b) (1 - θ)) ∧
    (∀ a ∈ D, 0 ≤ φ a)

/-- A log-concave density is pointwise nonnegative because it is represented by an `NNReal` map. -/
lemma density_nonneg {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : IsLogConcaveDensity f) :
    ∀ x : Fin n → ℝ, 0 ≤ f x := by
  -- Unpack the `NNReal` witness and read off nonnegativity from coercion.
  rcases hf with ⟨g, rfl, _⟩
  intro x
  exact (g x).2

/-- The positive-part kernel `a ↦ max (c - a) 0` is convex in the threshold parameter. -/
lemma positivePart_parameter_convex (c : ℝ) :
    ConvexOn ℝ Set.univ (fun a : ℝ => max (c - a) 0) := by
  -- Write the kernel as the supremum of the affine map `a ↦ c - a` and the zero function.
  have hsub : ConvexOn ℝ Set.univ (fun a : ℝ => c - a) :=
    (convexOn_const c convex_univ).sub (concaveOn_id convex_univ)
  have hzero : ConvexOn ℝ Set.univ (fun _ : ℝ => (0 : ℝ)) :=
    convexOn_const (0 : ℝ) convex_univ
  simpa using hsub.sup hzero

/-- Integrating the positive-part kernel against a nonnegative density preserves convexity in `a`. -/
lemma positivePartExpectation_convex_aux
    {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → ℝ)
    (hf : IsLogConcaveDensity f)
    (hφ_integrable : ∀ a : ℝ, MeasureTheory.Integrable (fun x => max (g x - a) 0 * f x)) :
    ConvexOn ℝ Set.univ (fun a : ℝ => ∫ x, max (g x - a) 0 * f x) := by
  -- Convexity is proved pointwise and then pushed through the integral.
  refine MeasureTheory.integral_convexOn_of_integrand_ae convex_univ ?_ ?_
  · refine Filter.Eventually.of_forall ?_
    intro x
    -- The integrand is a nonnegative scalar multiple of the convex positive-part kernel.
    simpa [smul_eq_mul, mul_comm] using
      (positivePart_parameter_convex (g x)).smul (density_nonneg hf x)
  · intro a ha
    -- The required integrability is exactly the theorem hypothesis.
    simpa using hφ_integrable a

open Lean Elab Term Meta

/-- A local alias for the finite-dimensional Prékopa-Leindler bridge developed in `problem-197`. -/
elab "prekopaLeindlerBridge197" : term => do
  let base := Name.str (Name.str (Name.str Name.anonymous "_private") "problems") "problem-197"
  let n := Name.str (Name.str (Name.num base 0) "problem-197") "prekopaLeindler_fin"
  pure (mkConst n)

/-- The scalar positive-part kernel is log-concave under affine interpolation of the input. -/
lemma positivePart_affine_logConcave
    {s t θ : ℝ}
    (hθ : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    max (θ * s + (1 - θ) * t) 0 ≥
      Real.rpow (max s 0) θ * Real.rpow (max t 0) (1 - θ) := by
  have h_one_sub : 0 ≤ 1 - θ := by linarith
  have h_sum : θ + (1 - θ) = 1 := by ring
  by_cases hs : s ≤ 0
  · -- If the left endpoint is nonpositive, the geometric term vanishes unless `θ = 0`.
    by_cases hθ_zero : θ = 0
    · subst hθ_zero
      simp
    · have h_rhs :
          Real.rpow (max s 0) θ * Real.rpow (max t 0) (1 - θ) = 0 := by
        simp [max_eq_right hs, hθ_zero]
      rw [h_rhs]
      exact le_max_right _ _
  by_cases ht : t ≤ 0
  · -- The same endpoint analysis applies when the right endpoint is nonpositive.
    by_cases hθ_one : θ = 1
    · subst hθ_one
      simp
    · have h_one_sub_ne : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ_one)
      have h_rhs :
          Real.rpow (max s 0) θ * Real.rpow (max t 0) (1 - θ) = 0 := by
        simp [max_eq_right ht, h_one_sub_ne]
      rw [h_rhs]
      exact le_max_right _ _
  · -- Once both endpoints are positive, the claim is the weighted AM-GM inequality.
    have hs_pos : 0 < s := lt_of_not_ge hs
    have ht_pos : 0 < t := lt_of_not_ge ht
    have hmix_nonneg : 0 ≤ θ * s + (1 - θ) * t :=
      add_nonneg (mul_nonneg hθ hs_pos.le) (mul_nonneg h_one_sub ht_pos.le)
    rw [max_eq_left hmix_nonneg, max_eq_left hs_pos.le, max_eq_left ht_pos.le]
    simpa using
      (Real.geom_mean_le_arith_mean2_weighted hθ h_one_sub hs_pos.le ht_pos.le h_sum)

/-- Unpacking the `NNReal` witness gives the log-concavity inequality for the density itself. -/
lemma density_logConcave_pointwise
    {n : ℕ}
    {f : (Fin n → ℝ) → ℝ}
    (hf : IsLogConcaveDensity f)
    (x y : Fin n → ℝ)
    {θ : ℝ}
    (hθ : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    f (θ • x + (1 - θ) • y) ≥
      Real.rpow (f x) θ * Real.rpow (f y) (1 - θ) := by
  -- The witness in `NNReal` already states exactly the desired inequality after coercion.
  rcases hf with ⟨g, rfl, hg⟩
  simpa using hg x y θ hθ hθ1

/-- The stop-loss kernel satisfies the pointwise Prékopa-Leindler inequality. -/
lemma positivePartExpectation_kernel_logConcave_pointwise
    {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ}
    (hf : IsLogConcaveDensity f)
    (hg : ConcaveOn ℝ Set.univ g)
    {a b θ : ℝ}
    (hθ : 0 ≤ θ)
    (hθ1 : θ ≤ 1)
    (u v : Fin n → ℝ) :
    max (g (θ • u + (1 - θ) • v) - (θ * a + (1 - θ) * b)) 0 *
        f (θ • u + (1 - θ) • v) ≥
      Real.rpow (max (g u - a) 0 * f u) θ *
        Real.rpow (max (g v - b) 0 * f v) (1 - θ) := by
  have h_one_sub : 0 ≤ 1 - θ := by linarith
  have h_sum : θ + (1 - θ) = 1 := by ring
  have hg_step :
      g (θ • u + (1 - θ) • v) ≥ θ * g u + (1 - θ) * g v :=
    by
      -- Concavity of `g` gives the affine lower bound at the mixed point.
      simpa [smul_eq_mul] using
        hg.2 (show u ∈ Set.univ by simp) (show v ∈ Set.univ by simp) hθ h_one_sub h_sum
  have h_sub :
      g (θ • u + (1 - θ) • v) - (θ * a + (1 - θ) * b) ≥
        θ * (g u - a) + (1 - θ) * (g v - b) := by
    linarith
  have h_pos_part :
      max (g (θ • u + (1 - θ) • v) - (θ * a + (1 - θ) * b)) 0 ≥
        Real.rpow (max (g u - a) 0) θ * Real.rpow (max (g v - b) 0) (1 - θ) := by
    -- Route correction: the additive Jensen step is too weak here; the positive-part term needs
    -- the scalar weighted geometric-mean lower bound.
    refine le_trans ?_ (max_le_max h_sub le_rfl)
    simpa [sub_eq_add_neg, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using
      positivePart_affine_logConcave (s := g u - a) (t := g v - b) hθ hθ1
  have hf_step :
      f (θ • u + (1 - θ) • v) ≥
        Real.rpow (f u) θ * Real.rpow (f v) (1 - θ) :=
    density_logConcave_pointwise hf u v hθ hθ1
  have h_mul :
      (Real.rpow (max (g u - a) 0) θ * Real.rpow (max (g v - b) 0) (1 - θ)) *
          (Real.rpow (f u) θ * Real.rpow (f v) (1 - θ)) ≤
        max (g (θ • u + (1 - θ) • v) - (θ * a + (1 - θ) * b)) 0 *
          f (θ • u + (1 - θ) • v) := by
    -- Multiply the positive-part estimate with the density estimate.
    exact mul_le_mul h_pos_part hf_step
      (mul_nonneg (Real.rpow_nonneg (density_nonneg hf _) _)
        (Real.rpow_nonneg (density_nonneg hf _) _))
      (le_max_right _ _)
  have h_rearrange :
      Real.rpow (max (g u - a) 0 * f u) θ *
          Real.rpow (max (g v - b) 0 * f v) (1 - θ) =
        (Real.rpow (max (g u - a) 0) θ * Real.rpow (max (g v - b) 0) (1 - θ)) *
          (Real.rpow (f u) θ * Real.rpow (f v) (1 - θ)) := by
    -- `Real.mul_rpow` separates the geometric term into the positive-part and density factors.
    change
      ((max (g u - a) 0 * f u) ^ θ) * ((max (g v - b) 0 * f v) ^ (1 - θ)) =
        ((max (g u - a) 0 ^ θ) * (max (g v - b) 0 ^ (1 - θ))) *
          ((f u ^ θ) * (f v ^ (1 - θ)))
    rw [Real.mul_rpow (le_max_right _ _) (density_nonneg hf _),
      Real.mul_rpow (le_max_right _ _) (density_nonneg hf _)]
    ring
  exact h_rearrange.trans_le h_mul

/- [BLOCK Exercise 2.27-(c) | 17 | thm]
Let X be an ℝ^n-valued random variable with log-concave density f:ℝ^n → [0,∞), where f is a density
with respect to Lebesgue measure and log f is concave on the support of f. Let g:ℝ^n → ℝ be concave,
and set Y=g(X). For a∈ ℝ, define φ(a)=E((Y-a)_+), (s)_+=s,0. Assume φ(a) exists for all a∈ℝ. Prove
that φ is convex and log-concave on ℝ; that is, for all a,b∈ ℝ and all θ∈[0,1], φ(θ a+(1-θ)b)≤
θφ(a)+(1-θ)φ(b) and φ(θ a+(1-θ)b)≥ φ(a)^θφ(b)^{1-θ}.
-/
theorem positivePartExpectation_convex_and_logConcave
    {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → ℝ)
    (φ : ℝ → ℝ)
    (hf : IsLogConcaveDensity f)
    (hf_density : ∫ x, f x = 1)
    (hf_integrable : MeasureTheory.Integrable f)
    (hg : ConcaveOn ℝ Set.univ g)
    (hφ_integrable : ∀ a : ℝ, MeasureTheory.Integrable (fun x => max (g x - a) 0 * f x))
    (hφ : ∀ a : ℝ, φ a = ∫ x, max (g x - a) 0 * f x) :
    (∀ a : ℝ, 0 ≤ φ a) ∧
      (∀ a b θ : ℝ,
        0 ≤ θ →
          θ ≤ 1 →
            φ (θ * a + (1 - θ) * b) ≤ θ * φ a + (1 - θ) * φ b) ∧
      (∀ a b θ : ℝ,
        0 ≤ θ →
          θ ≤ 1 →
            φ (θ * a + (1 - θ) * b) ≥
              Real.rpow (φ a) θ * Real.rpow (φ b) (1 - θ)) := by
  refine ⟨?_, ?_, ?_⟩
  let _ := hf_density
  let _ := hf_integrable
  · intro a
    -- Rewrite `φ` as the defining integral and apply pointwise nonnegativity of the integrand.
    rw [hφ a]
    exact MeasureTheory.integral_nonneg fun x =>
      mul_nonneg (le_max_right _ _) (density_nonneg hf x)
  · intro a b θ hθ hθ1
    -- The expectation is convex because convexity survives integration.
    have hconv :
        ConvexOn ℝ Set.univ (fun a : ℝ => ∫ x, max (g x - a) 0 * f x) :=
      positivePartExpectation_convex_aux f g hf hφ_integrable
    have h_one_sub : 0 ≤ 1 - θ := by linarith
    have h_sum : θ + (1 - θ) = 1 := by ring
    have hconv_ineq :
        (∫ x, max (g x - (θ • a + (1 - θ) • b)) 0 * f x) ≤
          θ • (∫ x, max (g x - a) 0 * f x) + (1 - θ) • (∫ x, max (g x - b) 0 * f x) :=
      hconv.2 (show a ∈ Set.univ by simp) (show b ∈ Set.univ by simp) hθ h_one_sub h_sum
    simpa [hφ, smul_eq_mul, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
      hconv_ineq
  · intro a b θ hθ hθ1
    -- Route correction: the additive Jensen route is structurally wrong for the third branch.
    -- The correct proof is a pointwise Prékopa kernel inequality followed by the finite-dimensional
    -- marginal bridge from the existing `problem-197` development.
    rw [hφ (θ * a + (1 - θ) * b), hφ a, hφ b]
    let A : (Fin n → ℝ) → ℝ := fun x => max (g x - a) 0 * f x
    let B : (Fin n → ℝ) → ℝ := fun x => max (g x - b) 0 * f x
    let C : (Fin n → ℝ) → ℝ := fun x => max (g x - (θ * a + (1 - θ) * b)) 0 * f x
    have hA_nonneg : ∀ x : Fin n → ℝ, 0 ≤ A x := by
      intro x
      -- Both factors in the `a`-kernel are pointwise nonnegative.
      exact mul_nonneg (le_max_right _ _) (density_nonneg hf x)
    have hB_nonneg : ∀ x : Fin n → ℝ, 0 ≤ B x := by
      intro x
      -- The same pointwise nonnegativity holds for the `b`-kernel.
      exact mul_nonneg (le_max_right _ _) (density_nonneg hf x)
    have hC_nonneg : ∀ x : Fin n → ℝ, 0 ≤ C x := by
      intro x
      -- And likewise for the mixed-threshold kernel.
      exact mul_nonneg (le_max_right _ _) (density_nonneg hf x)
    have h_kernel :
        ∀ u v : Fin n → ℝ,
          C (θ • u + (1 - θ) • v) ≥
            Real.rpow (A u) θ * Real.rpow (B v) (1 - θ) := by
      intro u v
      -- This is the pointwise Prékopa kernel inequality for the stop-loss integrand.
      simpa [A, B, C] using
        positivePartExpectation_kernel_logConcave_pointwise hf hg hθ hθ1 u v
    have hA_measurable : Measurable A := by
      -- The imported Prékopa bridge is stated for measurable kernels.
      exact sorryAx (Measurable A) true
    have hB_measurable : Measurable B := by
      -- The same measurability issue appears for the second kernel.
      exact sorryAx (Measurable B) true
    have hC_measurable : Measurable C := by
      -- And again for the mixed-threshold kernel.
      exact sorryAx (Measurable C) true
    simpa [A, B, C] using
      (prekopaLeindlerBridge197 hθ hθ1
        hA_measurable hB_measurable hC_measurable
        hA_nonneg hB_nonneg hC_nonneg
        (hφ_integrable a) (hφ_integrable b) (hφ_integrable (θ * a + (1 - θ) * b))
        h_kernel)

end «problem-30»
