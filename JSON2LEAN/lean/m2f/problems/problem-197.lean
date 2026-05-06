import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators


namespace «problem-197»
/- [BLOCK Exercise 3.53 | 42 | defn]
A function f : ℝ^n → [0,∞) is log-concave if, for all u,v ∈ ℝ^n and all θ ∈ [0,1],
f(θ u+(1-θ)v) ≥ f(u)^θ f(v)^{1-θ}.
-/
def LogConcave {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ) : Prop :=
  (∀ x : E, 0 ≤ f x) ∧
  ∀ ⦃u v : E⦄ ⦃θ : ℝ⦄,
    0 ≤ θ →
    θ ≤ 1 →
    f (θ • u + (1 - θ) • v) ≥
      Real.rpow (f u) θ * Real.rpow (f v) (1 - θ)

def ProbabilityDensity
    {E : Type*} [MeasurableSpace E]
    (μ : MeasureTheory.Measure E)
    (f : E → ℝ) : Prop :=
  Measurable f ∧
  (∀ x : E, 0 ≤ f x) ∧
  MeasureTheory.Integrable f μ ∧
  ∫ x, f x ∂μ = 1

/- [BLOCK Exercise 3.53 | 43 | defn]
Random vectors X and Y are independent if, for all measurable sets A,B ⊆ ℝ^n,
P(X ∈ A, Y ∈ B)=P(X ∈ A)P(Y ∈ B).
-/
def IndependentRandomVectors {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    (P : MeasureTheory.Measure Ω) (X : Ω → E) (Y : Ω → F) : Prop :=
  ∀ ⦃A : Set E⦄ ⦃B : Set F⦄,
    MeasurableSet A →
    MeasurableSet B →
    P {ω | X ω ∈ A ∧ Y ω ∈ B} =
      P {ω | X ω ∈ A} * P {ω | Y ω ∈ B}

/-- Subtracting affine combinations distributes over the two summands. -/
lemma affine_combo_sub_affine_combo
    {n : ℕ} (x y u v : Fin n → ℝ) (θ : ℝ) :
    ((θ • x + (1 - θ) • y) - (θ • u + (1 - θ) • v)) =
      θ • (x - u) + (1 - θ) • (y - v) := by
  -- Compare the two vector-valued expressions coordinatewise and simplify each coordinate.
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  change θ * x i + (1 - θ) * y i - (θ * u i + (1 - θ) * v i) =
    θ * (x i - u i) + (1 - θ) * (y i - v i)
  ring

/-- The convolution kernel inherits the pointwise log-concavity inequality from the two factors. -/
lemma convolution_kernel_logConcave_pointwise
    {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ}
    (hf_logConcave : LogConcave f)
    (hg_logConcave : LogConcave g)
    {x y u v : Fin n → ℝ} {θ : ℝ}
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    f ((θ • x + (1 - θ) • y) - (θ • u + (1 - θ) • v)) *
        g (θ • u + (1 - θ) • v) ≥
      Real.rpow (f (x - u) * g u) θ *
        Real.rpow (f (y - v) * g v) (1 - θ) := by
  rcases hf_logConcave with ⟨hf_nonneg, hf_log⟩
  rcases hg_logConcave with ⟨hg_nonneg, hg_log⟩
  have hf_step :
      Real.rpow (f (x - u)) θ * Real.rpow (f (y - v)) (1 - θ) ≤
        f ((θ • x + (1 - θ) • y) - (θ • u + (1 - θ) • v)) := by
    -- Rewrite the subtraction into the affine combination required by `hf_log`.
    rw [affine_combo_sub_affine_combo x y u v θ]
    exact hf_log hθ0 hθ1
  have hg_step :
      Real.rpow (g u) θ * Real.rpow (g v) (1 - θ) ≤
        g (θ • u + (1 - θ) • v) :=
    hg_log hθ0 hθ1
  have h_mul :
      (Real.rpow (f (x - u)) θ * Real.rpow (f (y - v)) (1 - θ)) *
          (Real.rpow (g u) θ * Real.rpow (g v) (1 - θ)) ≤
        f ((θ • x + (1 - θ) • y) - (θ • u + (1 - θ) • v)) *
          g (θ • u + (1 - θ) • v) := by
    -- Multiply the two scalar inequalities; the side conditions are the corresponding nonnegativity facts.
    exact mul_le_mul hf_step hg_step
      (mul_nonneg (Real.rpow_nonneg (hg_nonneg _) _)
        (Real.rpow_nonneg (hg_nonneg _) _))
      (hf_nonneg _)
  -- Reassociate the `rpow` terms so the right-hand side is the product of the two kernel values.
  have h_rearrange :
      Real.rpow (f (x - u) * g u) θ *
          Real.rpow (f (y - v) * g v) (1 - θ) =
        (Real.rpow (f (x - u)) θ * Real.rpow (f (y - v)) (1 - θ)) *
          (Real.rpow (g u) θ * Real.rpow (g v) (1 - θ)) := by
    change
      ((f (x - u) * g u) ^ θ) * ((f (y - v) * g v) ^ (1 - θ)) =
        ((f (x - u) ^ θ) * (f (y - v) ^ (1 - θ))) *
          ((g u ^ θ) * (g v ^ (1 - θ)))
    rw [Real.mul_rpow (hf_nonneg _) (hg_nonneg _), Real.mul_rpow (hf_nonneg _) (hg_nonneg _)]
    ring
  exact (h_rearrange.trans_le h_mul)

/- [BLOCK Exercise 3.53 | 44 | thm]
Let f and g be log-concave probability densities on ℝ^n. Define their convolution
h(z)=∫_{ℝ^n} f(z-t)g(t)dt, and assume each convolution integrand is integrable. Prove that h is a
probability density and is log-concave on ℝ^n.
-/
/-- The zero-dimensional strict Prékopa-Leindler inequality is evaluation at the unique point. -/
private lemma prekopaLeindler_fin_strict_lintegral_core_zero
    {A B C : (Fin 0 → ℝ) → ENNReal}
    {θ : ℝ}
    (h_kernel :
      ∀ u v : Fin 0 → ℝ,
        C (θ • u + (1 - θ) • v) ≥ A u ^ θ * B v ^ (1 - θ)) :
    ∫⁻ z, C z ∂MeasureTheory.volume ≥
      (∫⁻ u, A u ∂MeasureTheory.volume) ^ θ *
        (∫⁻ v, B v ∂MeasureTheory.volume) ^ (1 - θ) := by
  have hdirac :
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) =
        MeasureTheory.Measure.dirac 0 := by
    -- Zero-dimensional Lebesgue measure is the Dirac mass at the unique point.
    simpa [MeasureTheory.volume_pi] using
      (MeasureTheory.Measure.pi_of_empty
        (μ := fun _ : Fin 0 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        (x := (0 : Fin 0 → ℝ)))
  -- After rewriting all integrals against the Dirac mass, the claim is exactly the kernel
  -- inequality at the unique pair of points.
  rw [hdirac]
  simp only [MeasureTheory.lintegral_dirac]
  simpa using h_kernel 0 0

/-- Support truncation to the symmetric interval `[-N, N]`. -/
private def supportTrunc (f : ℝ → ENNReal) (N : ℕ) : ℝ → ENNReal :=
  Set.indicator (Set.Icc (-(N : ℝ)) N) f

/-- Support truncation preserves measurability. -/
private lemma supportTrunc_measurable
    {f : ℝ → ENNReal} (hf : Measurable f) (N : ℕ) :
    Measurable (supportTrunc f N) := by
  -- The truncation only inserts the indicator of a measurable interval.
  simpa [supportTrunc] using hf.indicator measurableSet_Icc

/-- Larger support truncations dominate smaller ones pointwise. -/
private lemma supportTrunc_mono
    {f : ℝ → ENNReal} {N M : ℕ} (hNM : N ≤ M) :
    supportTrunc f N ≤ supportTrunc f M := by
  intro x
  by_cases hx : x ∈ Set.Icc (-(N : ℝ)) N
  · -- Inside the smaller interval, monotonicity is just the interval inclusion `[-N, N] ⊆ [-M, M]`.
    have hx' : x ∈ Set.Icc (-(M : ℝ)) M := by
      rcases hx with ⟨hx_left, hx_right⟩
      constructor
      · have h_cast : (N : ℝ) ≤ M := by
          exact_mod_cast hNM
        linarith
      · exact le_trans hx_right (by exact_mod_cast hNM)
    simp [supportTrunc, hx, hx']
  · -- Outside the smaller interval, the smaller truncation is already zero.
    simp [supportTrunc, hx]

/-- At each point, the support truncations eventually stabilize to the original function. -/
private lemma iSup_supportTrunc_apply
    (f : ℝ → ENNReal) (x : ℝ) :
    (⨆ N : ℕ, supportTrunc f N x) = f x := by
  apply le_antisymm
  · -- Every truncation is bounded above by the original function.
    refine iSup_le ?_
    intro N
    by_cases hx : x ∈ Set.Icc (-(N : ℝ)) N
    · simp [supportTrunc, hx]
    · simp [supportTrunc, hx]
  · -- Once `N > |x|`, the point `x` lies in the support interval and the truncation equals `f x`.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, |x| < (N : ℝ) := exists_nat_gt (|x|)
    have hxN : x ∈ Set.Icc (-(N : ℝ)) N := by
      have hxlt : -(N : ℝ) < x ∧ x < N := by
        simpa using abs_lt.mp hN
      exact ⟨le_of_lt hxlt.1, le_of_lt hxlt.2⟩
    calc
      f x = supportTrunc f N x := by
        simp [supportTrunc, hxN]
      _ ≤ ⨆ n : ℕ, supportTrunc f n x := le_iSup (fun n => supportTrunc f n x) N

/-- Outside the truncation interval, the support truncation vanishes. -/
private lemma supportTrunc_eq_zero_of_not_mem
    {f : ℝ → ENNReal} {N : ℕ} {x : ℝ}
    (hx : x ∉ Set.Icc (-(N : ℝ)) N) :
    supportTrunc f N x = 0 := by
  -- Off the truncation interval, the indicator defining `supportTrunc` evaluates to zero.
  simp [supportTrunc, hx]

/-- Positive strict superlevel sets stay inside the bounded support interval. -/
private lemma strictSuperlevel_subset_support
    {f : ℝ → ENNReal}
    {N : ℕ}
    (hf_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f x = 0)
    {s : ℝ}
    (hs : 0 < s) :
    {x : ℝ | ENNReal.ofReal s < f x} ⊆ Set.Icc (-(N : ℝ)) N := by
  intro x hx
  change ENNReal.ofReal s < f x at hx
  by_contra hx_out
  have hx_zero : f x = 0 := hf_support hx_out
  have hs_enn : 0 < ENNReal.ofReal s := ENNReal.ofReal_pos.mpr hs
  -- Outside the support interval, the function vanishes, so a positive threshold cannot be crossed.
  rw [hx_zero] at hx
  exact (not_lt_of_ge hs_enn.le) hx

/-- The pointwise kernel inequality sends strict superlevel pairs into the corresponding target
superlevel set. -/
private lemma real_superlevel_affine_subset
    {a b c : ℝ → ENNReal}
    {θ s t : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (h_kernel :
      ∀ u v : ℝ,
        c (θ * u + (1 - θ) * v) ≥ a u ^ θ * b v ^ (1 - θ))
    (hs : 0 < s)
    (ht : 0 < t) :
    {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
      ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z}
      ⊆ {z : ℝ | ENNReal.ofReal (s ^ θ * t ^ (1 - θ)) < c z} := by
  intro z hz
  rcases hz with ⟨u, hu, v, hv, rfl⟩
  have hu_pow : ENNReal.ofReal (s ^ θ) < a u ^ θ := by
    -- Raise the strict `a`-superlevel inequality to the positive exponent `θ`.
    simpa [ENNReal.ofReal_rpow_of_nonneg hs.le hθ_mem.1.le] using
      ENNReal.rpow_lt_rpow hu hθ_mem.1
  have hv_pow : ENNReal.ofReal (t ^ (1 - θ)) < b v ^ (1 - θ) := by
    -- The same positivity argument applies to the `b`-superlevel inequality.
    simpa [ENNReal.ofReal_rpow_of_nonneg ht.le (sub_nonneg.mpr hθ_mem.2.le)] using
      ENNReal.rpow_lt_rpow hv (sub_pos.mpr hθ_mem.2)
  have hmul :
      ENNReal.ofReal (s ^ θ) * ENNReal.ofReal (t ^ (1 - θ)) <
        a u ^ θ * b v ^ (1 - θ) :=
    ENNReal.mul_lt_mul hu_pow hv_pow
  have hkernel' :
      a u ^ θ * b v ^ (1 - θ) ≤ c (θ * u + (1 - θ) * v) := h_kernel u v
  -- Combine the strict product lower bound with the kernel inequality at `(u, v)`.
  exact lt_of_lt_of_le (by
    simpa [ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
      ENNReal.ofReal_rpow_of_nonneg hs.le hθ_mem.1.le,
      ENNReal.ofReal_rpow_of_nonneg ht.le (sub_nonneg.mpr hθ_mem.2.le)] using hmul) hkernel'

/-- Strict-superlevel volume profiles are antitone in the threshold parameter. -/
private lemma strictSuperlevelProfile_antitone
    (f : ℝ → ENNReal) :
    Antitone (fun s : ℝ => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < f x}) := by
  intro s t hst
  -- Larger thresholds only shrink the strict superlevel set, so the corresponding volume
  -- decreases.
  exact MeasureTheory.measure_mono fun x hx =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hx

/-- Any set contained in the bounded support interval has finite volume. -/
private lemma volume_lt_top_of_subset_supportInterval
    {N : ℕ} {s : Set ℝ}
    (hs : s ⊆ Set.Icc (-(N : ℝ)) N) :
    MeasureTheory.volume s < ⊤ := by
  -- Compare the set to the enclosing compact interval and use the explicit interval volume.
  refine lt_of_le_of_lt (MeasureTheory.measure_mono hs) ?_
  simpa [Real.volume_Icc] using
    (ENNReal.ofReal_lt_top : ENNReal.ofReal ((N : ℝ) - (-(N : ℝ))) < ⊤)

/-- The affine image `{θ * u + (1 - θ) * v}` is the additive image of the two separately scaled
superlevel sets. -/
private lemma real_affine_image_eq_image2_add
    {S T : Set ℝ} {θ : ℝ} :
    {z : ℝ | ∃ u ∈ S, ∃ v ∈ T, θ * u + (1 - θ) * v = z} =
      Set.image2 (fun x y : ℝ => x + y) ((fun u : ℝ => θ * u) '' S)
        ((fun v : ℝ => (1 - θ) * v) '' T) := by
  ext z
  constructor
  · intro hz
    -- Unpack the affine representation and package the two scaled points into the additive image.
    rcases hz with ⟨u, hu, v, hv, rfl⟩
    exact ⟨θ * u, ⟨u, hu, rfl⟩, (1 - θ) * v, ⟨v, hv, rfl⟩, by ring⟩
  · intro hz
    -- Conversely, any point in the additive image comes from the original affine formula.
    rcases hz with ⟨x, hx, y, hy, hxy⟩
    rcases hx with ⟨u, hu, rfl⟩
    rcases hy with ⟨v, hv, rfl⟩
    refine ⟨u, hu, v, hv, ?_⟩
    simpa using hxy

/-- Scaling a real measurable set by a nonzero scalar rescales its Lebesgue volume by the absolute
value of that scalar. -/
private lemma real_volume_image_mul_left
    {a : ℝ} (ha : a ≠ 0) {S : Set ℝ} :
    MeasureTheory.volume ((fun x : ℝ => a * x) '' S) =
      ENNReal.ofReal |a| * MeasureTheory.volume S := by
  have hpre :
      (fun x : ℝ => a * x) ⁻¹' ((fun x : ℝ => a * x) '' S) = S := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      -- Injectivity of multiplication by a nonzero scalar recovers the original point.
      have hxy' : y = x := by
        exact mul_left_cancel₀ ha hxy
      simpa [hxy'] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hvol :
      MeasureTheory.volume S =
        ENNReal.ofReal |a⁻¹| * MeasureTheory.volume ((fun x : ℝ => a * x) '' S) := by
    -- Rewrite the image volume through the preimage formula for multiplication.
    simpa [hpre] using
      Real.volume_preimage_mul_left ha (((fun x : ℝ => a * x) '' S) : Set ℝ)
  have haenn : ENNReal.ofReal |a| ≠ 0 := by
    simp [ha]
  have hinv : ENNReal.ofReal |a⁻¹| = (ENNReal.ofReal |a|)⁻¹ := by
    rw [abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr ha)]
  -- Multiply the preimage identity by `|a|` to solve for the volume of the scaled image.
  calc
    MeasureTheory.volume ((fun x : ℝ => a * x) '' S) =
        1 * MeasureTheory.volume ((fun x : ℝ => a * x) '' S) := by
          simp
    _ =
        (ENNReal.ofReal |a| * ENNReal.ofReal |a⁻¹|) *
          MeasureTheory.volume ((fun x : ℝ => a * x) '' S) := by
            congr 1
            rw [hinv]
            symm
            exact ENNReal.mul_inv_cancel haenn ENNReal.ofReal_ne_top
    _ =
        ENNReal.ofReal |a| *
          (ENNReal.ofReal |a⁻¹| * MeasureTheory.volume ((fun x : ℝ => a * x) '' S)) := by
            simp [mul_assoc]
    _ = ENNReal.ofReal |a| * MeasureTheory.volume S := by
          rw [hvol]

/-- For finite `ENNReal` values, the weighted geometric mean is bounded by the corresponding
weighted arithmetic mean written through `toReal`. -/
private lemma ennreal_geomMean_le_ofReal_weighted_toReal_sum
    {x y : ENNReal} {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x < ⊤)
    (hy : y < ⊤) :
    x ^ θ * y ^ (1 - θ) ≤
      ENNReal.ofReal (θ * x.toReal + (1 - θ) * y.toReal) := by
  have hx_ne_top : x ≠ ⊤ := ne_of_lt hx
  have hy_ne_top : y ≠ ⊤ := ne_of_lt hy
  have hx_rpow_lt_top : x ^ θ < ⊤ := ENNReal.rpow_lt_top_of_nonneg hθ_mem.1.le hx_ne_top
  have hy_rpow_lt_top : y ^ (1 - θ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hθ_mem.2.le) hy_ne_top
  have hmul_ne_top : x ^ θ * y ^ (1 - θ) ≠ ⊤ :=
    (ENNReal.mul_lt_top hx_rpow_lt_top hy_rpow_lt_top).ne
  have h_real :
      (x ^ θ * y ^ (1 - θ)).toReal ≤ θ * x.toReal + (1 - θ) * y.toReal := by
    -- Route correction: once the profile values are known to be finite, the remaining comparison
    -- is the standard weighted AM-GM inequality on real numbers.
    rw [ENNReal.toReal_mul]
    simpa [ENNReal.toReal_rpow] using
      (Real.geom_mean_le_arith_mean2_weighted
      hθ_mem.1.le (sub_nonneg.mpr hθ_mem.2.le) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (by ring))
  -- Re-embed the real inequality into `ENNReal` using finiteness of the weighted geometric mean.
  calc
    x ^ θ * y ^ (1 - θ) =
        ENNReal.ofReal ((x ^ θ * y ^ (1 - θ)).toReal) := by
          rw [ENNReal.ofReal_toReal hmul_ne_top]
    _ ≤ ENNReal.ofReal (θ * x.toReal + (1 - θ) * y.toReal) := by
          exact ENNReal.ofReal_le_ofReal h_real

/-- The logarithmic substitution `r = exp x` transports a positive-half-line `lintegral` to the
full real line. -/
private lemma log_profile_lintegral_eq
    (phi : ℝ → ENNReal) :
    ∫⁻ r in Set.Ioi 0, phi r ∂MeasureTheory.volume =
      ∫⁻ x, ENNReal.ofReal (Real.exp x) * phi (Real.exp x) ∂MeasureTheory.volume := by
  -- Rewrite the target half-line as the image of `exp` and apply the one-dimensional Jacobian
  -- formula with derivative `exp`.
  rw [← Real.range_exp]
  simpa using
    (MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
      (s := Set.univ) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ
      (fun x hx => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (fun x hx y hy hxy => Real.exp_injective hxy)
      phi)

/-- A multiplicative kernel on `Set.Ioi 0` becomes an additive Prékopa-Leindler kernel after the
logarithmic transport `r = exp x`. -/
private lemma log_profile_kernel_transport
    {α β γ : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hkernel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
  dsimp
  intro x y
  have hx : 0 < Real.exp x := Real.exp_pos x
  have hy : 0 < Real.exp y := Real.exp_pos y
  have hbase := hkernel hx hy
  have hexp :
      Real.exp (θ * x + (1 - θ) * y) =
        Real.exp x ^ θ * Real.exp y ^ (1 - θ) := by
    -- The logarithm linearizes the multiplicative interpolation parameter.
    rw [Real.exp_add,
      show Real.exp (θ * x) = Real.exp x ^ θ by rw [mul_comm, Real.exp_mul],
      show Real.exp ((1 - θ) * y) = Real.exp y ^ (1 - θ) by rw [mul_comm, Real.exp_mul]]
  have hαpow :
      (ENNReal.ofReal (Real.exp x) * α (Real.exp x)) ^ θ =
        ENNReal.ofReal (Real.exp x ^ θ) * α (Real.exp x) ^ θ := by
    -- Pull the exponent through the Jacobian weight and the profile value.
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ_mem.1.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos x).le hθ_mem.1.le]
  have hβpow :
      (ENNReal.ofReal (Real.exp y) * β (Real.exp y)) ^ (1 - θ) =
        ENNReal.ofReal (Real.exp y ^ (1 - θ)) * β (Real.exp y) ^ (1 - θ) := by
    -- The same factorization works for the second profile.
    rw [ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hθ_mem.2.le),
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos y).le (sub_nonneg.mpr hθ_mem.2.le)]
  calc
    ENNReal.ofReal (Real.exp (θ * x + (1 - θ) * y)) * γ (Real.exp (θ * x + (1 - θ) * y)) =
        ENNReal.ofReal (Real.exp x ^ θ * Real.exp y ^ (1 - θ)) *
          γ (Real.exp x ^ θ * Real.exp y ^ (1 - θ)) := by
            rw [hexp]
    _ ≥
        ENNReal.ofReal (Real.exp x ^ θ * Real.exp y ^ (1 - θ)) *
          (α (Real.exp x) ^ θ * β (Real.exp y) ^ (1 - θ)) := by
            -- Apply the multiplicative kernel at the positive radii `exp x` and `exp y`.
            exact mul_le_mul_right hbase _
    _ =
        (ENNReal.ofReal (Real.exp x ^ θ) * α (Real.exp x) ^ θ) *
          (ENNReal.ofReal (Real.exp y ^ (1 - θ)) * β (Real.exp y) ^ (1 - θ)) := by
            -- Reassociate the Jacobian factor with the transported kernel factors.
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos x).le _)]
            simp [mul_assoc, mul_left_comm, mul_comm]
    _ =
        (ENNReal.ofReal (Real.exp x) * α (Real.exp x)) ^ θ *
          (ENNReal.ofReal (Real.exp y) * β (Real.exp y)) ^ (1 - θ) := by
            rw [hαpow, hβpow]

/-- Truncating an ENNReal-valued function at the finite level `n` turns the standard real-valued
layer-cake formula into an ENNReal strict-superlevel identity on `ℝ`. -/
private lemma ennreal_lintegral_trunc_eq_profile_trunc
    {f : ℝ → ENNReal} (hf_measurable : Measurable f) (n : ℕ) :
    ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume =
      ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n)
        (fun r => MeasureTheory.volume {x : ℝ | ENNReal.ofReal r < f x}) r
          ∂MeasureTheory.volume := by
  let ftr : ℕ → ℝ → ℝ := fun m x => ENNReal.truncateToReal (m : ENNReal) (f x)
  have hftr_measurable : Measurable (ftr n) := by
    -- Each truncation is a continuous transform of the measurable ENNReal-valued function.
    exact (ENNReal.continuous_truncateToReal
      (by simp : (n : ENNReal) ≠ ⊤)).measurable.comp hf_measurable
  have hftr_nonneg : 0 ≤ᵐ[MeasureTheory.volume] ftr n :=
    Filter.Eventually.of_forall fun x => ENNReal.truncateToReal_nonneg
  have h_lhs :
      ∫⁻ x, ENNReal.ofReal (ftr n x) ∂MeasureTheory.volume =
        ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume := by
    -- Recasting the truncated real-valued function back to `ENNReal` exactly recovers the
    -- finite truncation `min n (f x)`.
    refine MeasureTheory.lintegral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => by
      simp [ftr, ENNReal.truncateToReal, ENNReal.ofReal_toReal]
  have h_rhs :
      ∫⁻ r in Set.Ioi 0, MeasureTheory.volume {x : ℝ | r < ftr n x}
          ∂MeasureTheory.volume =
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n)
          (fun r => MeasureTheory.volume {x : ℝ | ENNReal.ofReal r < f x}) r
            ∂MeasureTheory.volume := by
    calc
      ∫⁻ r in Set.Ioi 0, MeasureTheory.volume {x : ℝ | r < ftr n x}
          ∂MeasureTheory.volume =
        ∫⁻ r, Set.indicator (Set.Ioi (0 : ℝ))
          (fun r => MeasureTheory.volume {x : ℝ | r < ftr n x}) r
            ∂MeasureTheory.volume := by
              simp [MeasureTheory.lintegral_indicator, measurableSet_Ioi]
      _ =
          ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n)
            (fun r => MeasureTheory.volume {x : ℝ | ENNReal.ofReal r < f x}) r
              ∂MeasureTheory.volume := by
                -- On the positive half-line, the truncated strict superlevel set agrees with the
                -- original one below the cutoff `n` and becomes empty above it.
                refine MeasureTheory.lintegral_congr_ae ?_
                exact Filter.Eventually.of_forall fun r => by
                  by_cases hr0 : 0 < r
                  · by_cases hrn : r < n
                    · have hset :
                        {x : ℝ | r < ftr n x} = {x : ℝ | ENNReal.ofReal r < f x} := by
                          ext x
                          change r < ENNReal.truncateToReal (n : ENNReal) (f x) ↔
                            ENNReal.ofReal r < f x
                          have hmin_ne_top : min (n : ENNReal) (f x) ≠ ⊤ := by simp
                          rw [show ENNReal.truncateToReal (n : ENNReal) (f x) =
                            (min (n : ENNReal) (f x)).toReal by rfl]
                          rw [← ENNReal.ofReal_lt_iff_lt_toReal hr0.le hmin_ne_top, lt_min_iff]
                          constructor
                          · intro h
                            exact h.2
                          · intro h
                            constructor
                            · exact (ENNReal.ofReal_lt_iff_lt_toReal hr0.le
                                (by simp : (n : ENNReal) ≠ ⊤)).2 (by simpa using hrn)
                            · exact h
                      simp [Set.indicator, hr0, hrn, hset]
                    · have hempty : {x : ℝ | r < ftr n x} = ∅ := by
                        ext x
                        change r < ENNReal.truncateToReal (n : ENNReal) (f x) ↔ False
                        have hmin_ne_top : min (n : ENNReal) (f x) ≠ ⊤ := by simp
                        rw [show ENNReal.truncateToReal (n : ENNReal) (f x) =
                          (min (n : ENNReal) (f x)).toReal by rfl]
                        rw [← ENNReal.ofReal_lt_iff_lt_toReal hr0.le hmin_ne_top, lt_min_iff]
                        constructor
                        · intro h
                          have hrn_real : r < n :=
                            (ENNReal.ofReal_lt_iff_lt_toReal hr0.le
                              (by simp : (n : ENNReal) ≠ ⊤)).1 h.1
                          exact hrn hrn_real
                        · intro h
                          exact False.elim h
                      simp [Set.indicator, hr0, hrn, hempty]
                  · simp [Set.indicator, hr0]
  calc
    ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume =
        ∫⁻ x, ENNReal.ofReal (ftr n x) ∂MeasureTheory.volume := by
          -- Route correction: rewrite the ENNReal truncation as an honest real-valued truncation
          -- before applying the imported layer-cake theorem.
          symm
          exact h_lhs
    _ = ∫⁻ r in Set.Ioi 0, MeasureTheory.volume {x : ℝ | r < ftr n x}
          ∂MeasureTheory.volume := by
            simpa [ftr] using
              MeasureTheory.lintegral_eq_lintegral_meas_lt MeasureTheory.volume
                hftr_nonneg hftr_measurable.aemeasurable
    _ =
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n)
          (fun r => MeasureTheory.volume {x : ℝ | ENNReal.ofReal r < f x}) r
            ∂MeasureTheory.volume := h_rhs

/-- A measurable ENNReal-valued function is the integral of the volume profile of its positive
strict superlevel sets. -/
private lemma ennreal_lintegral_eq_strictSuperlevelProfile
    {f : ℝ → ENNReal} (hf_measurable : Measurable f) :
    ∫⁻ x, f x ∂MeasureTheory.volume =
      ∫⁻ r in Set.Ioi 0, MeasureTheory.volume {x : ℝ | ENNReal.ofReal r < f x}
        ∂MeasureTheory.volume := by
  let φ : ℕ → ℝ → ENNReal := fun n =>
    Set.indicator (Set.Ioo (0 : ℝ) n)
      (fun r => MeasureTheory.volume {x : ℝ | ENNReal.ofReal r < f x})
  have hφ_measurable : ∀ n : ℕ, Measurable (φ n) := by
    intro n
    -- The strict-superlevel profile is antitone in the threshold, hence measurable.
    simpa [φ] using
      (Antitone.measurable (strictSuperlevelProfile_antitone f)).indicator measurableSet_Ioo
  have hφ_mono : Monotone φ := by
    intro n m hnm r
    by_cases hr : r ∈ Set.Ioo (0 : ℝ) n
    · have hr' : r ∈ Set.Ioo (0 : ℝ) m := by
        rcases hr with ⟨hr0, hrn⟩
        exact ⟨hr0, lt_of_lt_of_le hrn (by exact_mod_cast hnm)⟩
      simp [φ, hr, hr']
    · by_cases hr' : r ∈ Set.Ioo (0 : ℝ) m
      · simp [φ, hr, hr']
      · simp [φ, hr, hr']
  have hφ_iSup :
      ∀ r : ℝ, (⨆ n : ℕ, φ n r) =
        Set.indicator (Set.Ioi (0 : ℝ))
          (fun r => MeasureTheory.volume {x : ℝ | ENNReal.ofReal r < f x}) r := by
    intro r
    by_cases hr0 : 0 < r
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, r < n := exists_nat_gt r
      have hrn : r ∈ Set.Ioo (0 : ℝ) n := ⟨hr0, hn⟩
      apply le_antisymm
      · refine iSup_le ?_
        intro m
        by_cases hrm : r ∈ Set.Ioo (0 : ℝ) m
        · simp [φ, hr0, hrm]
        · simp [φ, hr0, hrm]
      · calc
          Set.indicator (Set.Ioi (0 : ℝ))
              (fun r => MeasureTheory.volume {x : ℝ | ENNReal.ofReal r < f x}) r =
            φ n r := by
              simp [φ, hr0, hrn]
          _ ≤ ⨆ m : ℕ, φ m r := le_iSup (fun m => φ m r) n
    · have hnot : r ∉ Set.Ioi (0 : ℝ) := by simpa using hr0
      have hzero : ∀ n : ℕ, φ n r = 0 := by
        intro n
        have hrn : r ∉ Set.Ioo (0 : ℝ) n := by
          intro hrn
          exact hnot hrn.1
        simp [φ, hrn]
      simp [hnot, hzero]
  have hmin_iSup :
      ∀ x : ℝ, (⨆ n : ℕ, min (n : ENNReal) (f x)) = f x := by
    intro x
    apply le_antisymm
    · refine iSup_le ?_
      intro n
      exact min_le_right _ _
    · by_cases htop : f x = ⊤
      · simpa [htop, ENNReal.iSup_natCast]
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, (f x).toReal < n := exists_nat_gt (f x).toReal
        have hle : f x ≤ n := by
          rw [← ENNReal.toReal_le_toReal htop (by simp)]
          exact le_of_lt hn
        calc
          f x = min (n : ENNReal) (f x) := by simp [min_eq_right hle]
          _ ≤ ⨆ m : ℕ, min (m : ENNReal) (f x) := by
              exact le_iSup (fun m : ℕ => min (m : ENNReal) (f x)) n
  have htrunc :
      ∀ n : ℕ,
        ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume =
          ∫⁻ r, φ n r ∂MeasureTheory.volume := by
    intro n
    -- Each finite truncation is handled by the strict-superlevel layer-cake formula above.
    simpa [φ] using ennreal_lintegral_trunc_eq_profile_trunc hf_measurable n
  calc
    ∫⁻ x, f x ∂MeasureTheory.volume = ∫⁻ x, ⨆ n : ℕ, min (n : ENNReal) (f x)
        ∂MeasureTheory.volume := by
          congr with x
          symm
          exact hmin_iSup x
    _ = ⨆ n : ℕ, ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume := by
          exact MeasureTheory.lintegral_iSup
            (fun n => (measurable_const.min hf_measurable)) (by
              intro n m hnm x
              exact min_le_min (by exact_mod_cast hnm) le_rfl)
    _ = ⨆ n : ℕ, ∫⁻ r, φ n r ∂MeasureTheory.volume := by
          congr with n
          exact htrunc n
    _ = ∫⁻ r, ⨆ n : ℕ, φ n r ∂MeasureTheory.volume := by
          symm
          exact MeasureTheory.lintegral_iSup hφ_measurable hφ_mono
    _ = ∫⁻ r, Set.indicator (Set.Ioi (0 : ℝ))
          (fun r => MeasureTheory.volume {x : ℝ | ENNReal.ofReal r < f x}) r
          ∂MeasureTheory.volume := by
            congr with r
            exact hφ_iSup r
    _ = ∫⁻ r in Set.Ioi 0, MeasureTheory.volume {x : ℝ | ENNReal.ofReal r < f x}
          ∂MeasureTheory.volume := by
            simp [MeasureTheory.lintegral_indicator, measurableSet_Ioi]

/-- For a nonempty measurable set of finite volume, the volume is the supremum of the volumes of
its nonempty compact subsets. -/
private lemma measure_eq_iSup_isCompact_nonempty_of_nonempty
    {S : Set ℝ} (hS_meas : MeasurableSet S)
    (hS_top : MeasureTheory.volume S ≠ ⊤) :
    MeasureTheory.volume S =
      ⨆ K : Set ℝ, ⨆ (_ : K ⊆ S ∧ IsCompact K ∧ K.Nonempty), MeasureTheory.volume K := by
  have hbase := MeasurableSet.measure_eq_iSup_isCompact_of_ne_top
    (μ := MeasureTheory.volume) hS_meas hS_top
  rw [hbase]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro K
    refine iSup_le ?_
    intro hKS
    refine iSup_le ?_
    intro hKc
    by_cases hKn : K.Nonempty
    · exact le_iSup_of_le K (le_iSup_of_le ⟨hKS, hKc, hKn⟩ le_rfl)
    · have hzero : MeasureTheory.volume K = 0 := by
        simp [Set.not_nonempty_iff_eq_empty.mp hKn]
      rw [hzero]
      exact bot_le
  · refine iSup_le ?_
    intro K
    refine iSup_le ?_
    intro hK
    exact le_iSup_of_le K (le_iSup_of_le hK.1 (le_iSup_of_le hK.2.1 le_rfl))

/-- Nonempty compact subsets of `ℝ` already realize the one-dimensional Brunn-Minkowski lower
bound needed for the strict-superlevel argument. -/
private lemma real_scaled_sumset_volume_lower_bound_compact
    {K L : Set ℝ} {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hKc : IsCompact K) (hLc : IsCompact L)
    (hKn : K.Nonempty) (hLn : L.Nonempty) :
    ENNReal.ofReal θ * MeasureTheory.volume K +
        ENNReal.ofReal (1 - θ) * MeasureTheory.volume L ≤
      MeasureTheory.volume (Set.image2 (fun x y : ℝ => x + y)
        ((fun u : ℝ => θ * u) '' K)
        ((fun v : ℝ => (1 - θ) * v) '' L)) := by
  let A : Set ℝ := (AffineMap.homothety (sInf L) θ) '' K
  let B : Set ℝ := (AffineMap.homothety (sSup K) (1 - θ)) '' L
  let src : Set ℝ := Set.image2 (fun x y : ℝ => x + y)
    ((fun u : ℝ => θ * u) '' K)
    ((fun v : ℝ => (1 - θ) * v) '' L)
  have hB_meas : MeasurableSet B := by
    -- Compact images under homotheties are measurable.
    dsimp [B]
    exact (hLc.image (AffineMap.homothety_continuous (x := sSup K) (t := 1 - θ))).measurableSet
  have hA_sub : A ⊆ src := by
    intro z hz
    rcases hz with ⟨u, hu, rfl⟩
    rcases hLc.sInf_mem hLn with haL
    refine ⟨θ * u, ⟨u, hu, rfl⟩, (1 - θ) * sInf L, ⟨sInf L, haL, rfl⟩, ?_⟩
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    ring
  have hB_sub : B ⊆ src := by
    intro z hz
    rcases hz with ⟨v, hv, rfl⟩
    rcases hKc.sSup_mem hKn with hbK
    refine ⟨θ * sSup K, ⟨sSup K, hbK, rfl⟩, (1 - θ) * v, ⟨v, hv, rfl⟩, ?_⟩
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    ring
  have h_inter_sub : A ∩ B ⊆ {θ * sSup K + (1 - θ) * sInf L} := by
    intro z hz
    rcases hz with ⟨hzA, hzB⟩
    rcases hzA with ⟨u, hu, hzu⟩
    rcases hzB with ⟨v, hv, hzv⟩
    have hu_le : u ≤ sSup K := (hKc.isLUB_sSup hKn).1 hu
    have hv_ge : sInf L ≤ v := (hLc.isGLB_sInf hLn).1 hv
    have hz_eq : θ * u + (1 - θ) * sInf L = θ * sSup K + (1 - θ) * v := by
      calc
        θ * u + (1 - θ) * sInf L = z := by
          rw [← hzu, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
          ring
        _ = θ * sSup K + (1 - θ) * v := by
          rw [← hzv, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
          ring
    have hnonpos : θ * (u - sSup K) ≤ 0 := by
      nlinarith [hθ_mem.1, hu_le]
    have hnonneg : 0 ≤ (1 - θ) * (v - sInf L) := by
      nlinarith [hθ_mem.2, hv_ge]
    have heq0 : θ * (u - sSup K) = (1 - θ) * (v - sInf L) := by
      nlinarith [hz_eq]
    have hu_eq : u = sSup K := by
      have : θ * (u - sSup K) = 0 := by linarith
      nlinarith [hθ_mem.1, this]
    have : z = θ * sSup K + (1 - θ) * sInf L := by
      rw [← hzu, hu_eq, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      ring
    simpa [this]
  have h_inter_zero : MeasureTheory.volume (A ∩ B) = 0 := by
    -- The two endpoint homotheties can only meet at the shared endpoint.
    refine MeasureTheory.measure_mono_null h_inter_sub ?_
    simp
  have h_union_eq : MeasureTheory.volume (A ∪ B) = MeasureTheory.volume A + MeasureTheory.volume B :=
    by
      have h := MeasureTheory.measure_union_add_inter
        (μ := MeasureTheory.volume) (s := A) (t := B) hB_meas
      rw [h_inter_zero, add_zero] at h
      exact h
  have hA_vol : MeasureTheory.volume A = ENNReal.ofReal θ * MeasureTheory.volume K := by
    -- A homothety about `sInf L` rescales Lebesgue volume by `θ`.
    dsimp [A]
    simp [abs_of_pos hθ_mem.1]
  have hB_vol : MeasureTheory.volume B = ENNReal.ofReal (1 - θ) * MeasureTheory.volume L := by
    -- The symmetric homothety about `sSup K` rescales by `1 - θ`.
    dsimp [B]
    have hsub : 0 < 1 - θ := sub_pos.mpr hθ_mem.2
    simp [abs_of_pos hsub]
  have h_union_sub : A ∪ B ⊆ src := by
    intro z hz
    rcases hz with hz | hz
    · exact hA_sub hz
    · exact hB_sub hz
  calc
    ENNReal.ofReal θ * MeasureTheory.volume K +
        ENNReal.ofReal (1 - θ) * MeasureTheory.volume L =
      MeasureTheory.volume A + MeasureTheory.volume B := by rw [hA_vol, hB_vol]
    _ = MeasureTheory.volume (A ∪ B) := h_union_eq.symm
    _ ≤ MeasureTheory.volume src := MeasureTheory.measure_mono h_union_sub

/-- The scaled-sumset lower bound is valid for bounded measurable subsets of `ℝ` once both source
sets are nonempty. The nonempty hypotheses are essential: the weighted arithmetic lower bound is
false for an empty second summand. -/
private lemma real_scaled_sumset_volume_lower_bound_of_nonempty
    {S T : Set ℝ} {K : ℕ} {θ : ℝ}
    (hS_meas : MeasurableSet S) (hT_meas : MeasurableSet T)
    (hS_sub : S ⊆ Set.Icc (-(K : ℝ)) K) (hT_sub : T ⊆ Set.Icc (-(K : ℝ)) K)
    (hS_nonempty : S.Nonempty) (hT_nonempty : T.Nonempty)
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1) :
    ENNReal.ofReal (θ * (MeasureTheory.volume S).toReal +
        (1 - θ) * (MeasureTheory.volume T).toReal) ≤
      MeasureTheory.volume (Set.image2 (fun x y : ℝ => x + y)
        ((fun u : ℝ => θ * u) '' S)
        ((fun v : ℝ => (1 - θ) * v) '' T)) := by
  let src : Set ℝ := Set.image2 (fun x y : ℝ => x + y)
    ((fun u : ℝ => θ * u) '' S)
    ((fun v : ℝ => (1 - θ) * v) '' T)
  have hS_top : MeasureTheory.volume S ≠ ⊤ :=
    (volume_lt_top_of_subset_supportInterval hS_sub).ne
  have hT_top : MeasureTheory.volume T ≠ ⊤ :=
    (volume_lt_top_of_subset_supportInterval hT_sub).ne
  have hS_eq :
      MeasureTheory.volume S =
        ⨆ K' : Set ℝ, ⨆ (_ : K' ⊆ S ∧ IsCompact K' ∧ K'.Nonempty), MeasureTheory.volume K' :=
    measure_eq_iSup_isCompact_nonempty_of_nonempty hS_meas hS_top
  have hT_eq :
      MeasureTheory.volume T =
        ⨆ L' : Set ℝ, ⨆ (_ : L' ⊆ T ∧ IsCompact L' ∧ L'.Nonempty), MeasureTheory.volume L' :=
    measure_eq_iSup_isCompact_nonempty_of_nonempty hT_meas hT_top
  have hsup :
      (⨆ K' : Set ℝ,
          ⨆ (_ : K' ⊆ S ∧ IsCompact K' ∧ K'.Nonempty),
            ENNReal.ofReal θ * MeasureTheory.volume K') +
        ⨆ L' : Set ℝ,
          ⨆ (_ : L' ⊆ T ∧ IsCompact L' ∧ L'.Nonempty),
            ENNReal.ofReal (1 - θ) * MeasureTheory.volume L' ≤
      MeasureTheory.volume src := by
    refine ENNReal.biSup_add_biSup_le' ?_ ?_ ?_
    · rcases hS_nonempty with ⟨x, hx⟩
      refine ⟨{x}, ?_⟩
      refine ⟨?_, isCompact_singleton, Set.singleton_nonempty x⟩
      intro y hy
      have hyx : y = x := by simpa [Set.mem_singleton_iff] using hy
      simpa [hyx] using hx
    · rcases hT_nonempty with ⟨y, hy⟩
      refine ⟨{y}, ?_⟩
      refine ⟨?_, isCompact_singleton, Set.singleton_nonempty y⟩
      intro z hz
      have hzy : z = y := by simpa [Set.mem_singleton_iff] using hz
      simpa [hzy] using hy
    · intro K' hK L' hL
      rcases hK with ⟨hKS, hKc, hKn⟩
      rcases hL with ⟨hLT, hLc, hLn⟩
      have hsrc_mono :
          MeasureTheory.volume (Set.image2 (fun x y : ℝ => x + y)
              ((fun u : ℝ => θ * u) '' K')
              ((fun v : ℝ => (1 - θ) * v) '' L')) ≤
            MeasureTheory.volume src := by
        exact MeasureTheory.measure_mono (by
          intro z hz
          rcases hz with ⟨x, hx, y, hy, rfl⟩
          rcases hx with ⟨x0, hx0, rfl⟩
          rcases hy with ⟨y0, hy0, rfl⟩
          exact ⟨θ * x0, Set.mem_image_of_mem (fun u : ℝ => θ * u) (hKS hx0),
            (1 - θ) * y0, Set.mem_image_of_mem (fun v : ℝ => (1 - θ) * v) (hLT hy0), rfl⟩)
      exact le_trans (real_scaled_sumset_volume_lower_bound_compact hθ_mem hKc hLc hKn hLn) hsrc_mono
  calc
    ENNReal.ofReal (θ * (MeasureTheory.volume S).toReal +
        (1 - θ) * (MeasureTheory.volume T).toReal) =
      ENNReal.ofReal θ * MeasureTheory.volume S +
        ENNReal.ofReal (1 - θ) * MeasureTheory.volume T := by
          have hp : 0 ≤ θ * (MeasureTheory.volume S).toReal :=
            mul_nonneg hθ_mem.1.le ENNReal.toReal_nonneg
          have hq : 0 ≤ (1 - θ) * (MeasureTheory.volume T).toReal :=
            mul_nonneg (sub_nonneg.mpr hθ_mem.2.le) ENNReal.toReal_nonneg
          rw [show (MeasureTheory.volume S).toReal = MeasureTheory.volume.real S by
                symm
                exact MeasureTheory.measureReal_def (μ := MeasureTheory.volume) (s := S)]
          rw [show (MeasureTheory.volume T).toReal = MeasureTheory.volume.real T by
                symm
                exact MeasureTheory.measureReal_def (μ := MeasureTheory.volume) (s := T)]
          have hp' : 0 ≤ θ * MeasureTheory.volume.real S := by
            simpa [MeasureTheory.measureReal_def] using hp
          have hq' : 0 ≤ (1 - θ) * MeasureTheory.volume.real T := by
            simpa [MeasureTheory.measureReal_def] using hq
          rw [ENNReal.ofReal_add hp' hq']
          · rw [ENNReal.ofReal_mul hθ_mem.1.le,
              ENNReal.ofReal_mul (sub_nonneg.mpr hθ_mem.2.le),
              MeasureTheory.ofReal_measureReal (μ := MeasureTheory.volume) (s := S) hS_top,
              MeasureTheory.ofReal_measureReal (μ := MeasureTheory.volume) (s := T) hT_top]
    _ =
        (⨆ K' : Set ℝ,
            ⨆ (_ : K' ⊆ S ∧ IsCompact K' ∧ K'.Nonempty),
              ENNReal.ofReal θ * MeasureTheory.volume K') +
          ⨆ L' : Set ℝ,
            ⨆ (_ : L' ⊆ T ∧ IsCompact L' ∧ L'.Nonempty),
              ENNReal.ofReal (1 - θ) * MeasureTheory.volume L' := by
            rw [hS_eq, hT_eq]
            simp_rw [ENNReal.mul_iSup]
    _ ≤ MeasureTheory.volume src := hsup

/-- Positive strict superlevel profiles of compactly supported one-dimensional kernels inherit the
multiplicative profile inequality. -/
private lemma compactSupport_strictSuperlevelProfile_kernel
    {a b c : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (ha_measurable : Measurable a)
    (hb_measurable : Measurable b)
    (hc_measurable : Measurable c)
    (N : ℕ)
    (ha_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → a x = 0)
    (hb_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → b x = 0)
    (hc_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → c x = 0)
    (h_kernel :
      ∀ u v : ℝ,
        c (θ * u + (1 - θ) * v) ≥ a u ^ θ * b v ^ (1 - θ)) :
    ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
      MeasureTheory.volume {u : ℝ | ENNReal.ofReal s < a u} ^ θ *
          MeasureTheory.volume {v : ℝ | ENNReal.ofReal t < b v} ^ (1 - θ) ≤
        MeasureTheory.volume {z : ℝ | ENNReal.ofReal (s ^ θ * t ^ (1 - θ)) < c z} := by
  let α : ℝ → ENNReal := fun s => MeasureTheory.volume {u : ℝ | ENNReal.ofReal s < a u}
  let β : ℝ → ENNReal := fun t => MeasureTheory.volume {v : ℝ | ENNReal.ofReal t < b v}
  let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < c z}
  have hα_measurableSet : ∀ s : ℝ, MeasurableSet {u : ℝ | ENNReal.ofReal s < a u} := by
    intro s
    -- Strict superlevel sets of a measurable ENNReal-valued function are measurable.
    exact measurableSet_lt measurable_const ha_measurable
  have hβ_measurableSet : ∀ t : ℝ, MeasurableSet {v : ℝ | ENNReal.ofReal t < b v} := by
    intro t
    -- The same measurability statement holds for `b`.
    exact measurableSet_lt measurable_const hb_measurable
  have hγ_measurableSet : ∀ r : ℝ, MeasurableSet {z : ℝ | ENNReal.ofReal r < c z} := by
    intro r
    -- And likewise for `c`.
    exact measurableSet_lt measurable_const hc_measurable
  have hα_subset : ∀ ⦃s : ℝ⦄, 0 < s →
      {u : ℝ | ENNReal.ofReal s < a u} ⊆ Set.Icc (-(N : ℝ)) N := by
    intro s hs
    -- Positive strict superlevel sets cannot escape the bounded support of `a`.
    exact strictSuperlevel_subset_support ha_support hs
  have hβ_subset : ∀ ⦃t : ℝ⦄, 0 < t →
      {v : ℝ | ENNReal.ofReal t < b v} ⊆ Set.Icc (-(N : ℝ)) N := by
    intro t ht
    -- The same bounded-support reduction applies to `b`.
    exact strictSuperlevel_subset_support hb_support ht
  have hγ_subset : ∀ ⦃r : ℝ⦄, 0 < r →
      {z : ℝ | ENNReal.ofReal r < c z} ⊆ Set.Icc (-(N : ℝ)) N := by
    intro r hr
    -- And again for the target function `c`.
    exact strictSuperlevel_subset_support hc_support hr
  have h_superlevel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
          ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z}
          ⊆ {z : ℝ | ENNReal.ofReal (s ^ θ * t ^ (1 - θ)) < c z} := by
    intro s t hs ht
    -- The pointwise kernel sends positive superlevel pairs into the target superlevel set.
    exact real_superlevel_affine_subset hθ_mem h_kernel hs ht
  have hα_antitone : Antitone α := by
    -- The `a`-profile is exactly a strict-superlevel volume profile.
    simpa [α] using strictSuperlevelProfile_antitone a
  have hβ_antitone : Antitone β := by
    -- The same monotonicity statement holds for `b`.
    simpa [β] using strictSuperlevelProfile_antitone b
  have hγ_antitone : Antitone γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using strictSuperlevelProfile_antitone c
  have hα_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → α s < ⊤ := by
    intro s hs
    -- Positive `a`-superlevel sets lie inside the bounded support interval.
    exact volume_lt_top_of_subset_supportInterval (hα_subset hs)
  have hβ_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → β t < ⊤ := by
    intro t ht
    -- The same finite-volume reduction applies to `β`.
    exact volume_lt_top_of_subset_supportInterval (hβ_subset ht)
  have h_source_le_target :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        MeasureTheory.volume {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
          ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z} ≤
            γ (s ^ θ * t ^ (1 - θ)) := by
    intro s t hs ht
    -- The superlevel-set inclusion upgrades immediately to a volume bound.
    simpa [γ] using MeasureTheory.measure_mono (h_superlevel hs ht)
  have h_pointwise_from_arith :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        ENNReal.ofReal (θ * (α s).toReal + (1 - θ) * (β t).toReal) ≤
          MeasureTheory.volume {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
            ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z} →
          α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    intro s t hs ht h_arith
    -- First use weighted AM-GM on the finite profile values, then pass through the affine-image
    -- volume lower bound and the superlevel-set inclusion.
    exact le_trans
      (le_trans
        (ennreal_geomMean_le_ofReal_weighted_toReal_sum hθ_mem (hα_lt_top hs) (hβ_lt_top ht))
        h_arith)
      (h_source_le_target hs ht)
  have h_source_eq_scaled_sumset :
      ∀ ⦃s t : ℝ⦄,
        {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
          ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z} =
            Set.image2 (fun x y : ℝ => x + y)
              ((fun u : ℝ => θ * u) '' {u : ℝ | ENNReal.ofReal s < a u})
              ((fun v : ℝ => (1 - θ) * v) '' {v : ℝ | ENNReal.ofReal t < b v}) := by
    intro s t
    -- Rewrite the affine source set as an additive scaled sumset.
    simpa using
      (real_affine_image_eq_image2_add
        (S := {u : ℝ | ENNReal.ofReal s < a u})
        (T := {v : ℝ | ENNReal.ofReal t < b v})
        (θ := θ))
  have hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    intro s t hs ht
    by_cases hS_nonempty : ({u : ℝ | ENNReal.ofReal s < a u} : Set ℝ).Nonempty
    · by_cases hT_nonempty : ({v : ℝ | ENNReal.ofReal t < b v} : Set ℝ).Nonempty
      · have h_arith :
          ENNReal.ofReal (θ * (α s).toReal + (1 - θ) * (β t).toReal) ≤
            MeasureTheory.volume {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
              ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z} := by
          -- Apply the one-dimensional scaled-sumset bound to the two positive strict superlevel
          -- sets and then rewrite the resulting source set back to the affine image.
          simpa [α, β, h_source_eq_scaled_sumset] using
            (real_scaled_sumset_volume_lower_bound_of_nonempty
              (S := {u : ℝ | ENNReal.ofReal s < a u})
              (T := {v : ℝ | ENNReal.ofReal t < b v})
              (K := N) (θ := θ)
              (hS_meas := hα_measurableSet s)
              (hT_meas := hβ_measurableSet t)
              (hS_sub := hα_subset hs)
              (hT_sub := hβ_subset ht)
              (hS_nonempty := hS_nonempty)
              (hT_nonempty := hT_nonempty)
              hθ_mem)
        exact h_pointwise_from_arith hs ht h_arith
      · have hT_empty : ({v : ℝ | ENNReal.ofReal t < b v} : Set ℝ) = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hT_nonempty
        have hβ_zero : β t = 0 := by
          simp [β, hT_empty]
        -- If the second positive superlevel set is empty, the geometric-mean side vanishes.
        rw [hβ_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hS_empty : ({u : ℝ | ENNReal.ofReal s < a u} : Set ℝ) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hS_nonempty
      have hα_zero : α s = 0 := by
        simp [α, hS_empty]
      -- Symmetrically, an empty first superlevel set forces the profile kernel to be trivial.
      rw [hα_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  intro s t hs ht
  -- The helper theorem packages the compact-support argument exactly in the profile form needed
  -- by the next reduction step.
  simpa [α, β, γ] using hkernel_profile hs ht

/-- A family of bounded-value Prékopa-Leindler estimates upgrades to the full ENNReal-valued
integral inequality by monotone convergence in the truncation parameter. -/
private lemma prekopaLeindler_from_value_truncations
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (htrunc :
      ∀ n : ℕ,
        ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume ≥
          (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ)) :
    ∫⁻ z, h z ∂MeasureTheory.volume ≥
      (∫⁻ x, f x ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, g y ∂MeasureTheory.volume) ^ (1 - θ) := by
  have hpointwise_iSup :
      ∀ (u : ℝ → ENNReal) (x : ℝ), (⨆ n : ℕ, min (n : ENNReal) (u x)) = u x := by
    intro u x
    -- Every ENNReal value is the supremum of its finite truncations.
    apply le_antisymm
    · refine iSup_le ?_
      intro n
      exact min_le_right _ _
    · by_cases htop : u x = ⊤
      · simpa [htop, ENNReal.iSup_natCast]
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, (u x).toReal < n := exists_nat_gt (u x).toReal
        have hle : u x ≤ n := by
          rw [← ENNReal.toReal_le_toReal htop (by simp)]
          exact le_of_lt hn
        calc
          u x = min (n : ENNReal) (u x) := by simp [min_eq_right hle]
          _ ≤ ⨆ m : ℕ, min (m : ENNReal) (u x) := by
              exact le_iSup (fun m : ℕ => min (m : ENNReal) (u x)) n
  have hftr_measurable : ∀ n : ℕ, Measurable (fun x => min (n : ENNReal) (f x)) := by
    intro n
    -- Finite value truncation preserves measurability.
    exact measurable_const.min hf_measurable
  have hgtr_measurable : ∀ n : ℕ, Measurable (fun y => min (n : ENNReal) (g y)) := by
    intro n
    -- The same measurability statement holds for `g`.
    exact measurable_const.min hg_measurable
  have hhtr_measurable : ∀ n : ℕ, Measurable (fun z => min (n : ENNReal) (h z)) := by
    intro n
    -- And likewise for `h`.
    exact measurable_const.min hh_measurable
  have hftr_mono : Monotone (fun n : ℕ => fun x => min (n : ENNReal) (f x)) := by
    intro n m hnm x
    -- Increasing the cutoff can only increase the truncated function.
    exact min_le_min (by exact_mod_cast hnm) le_rfl
  have hgtr_mono : Monotone (fun n : ℕ => fun y => min (n : ENNReal) (g y)) := by
    intro n m hnm y
    -- The same pointwise monotonicity holds for `g`.
    exact min_le_min (by exact_mod_cast hnm) le_rfl
  have hhtr_mono : Monotone (fun n : ℕ => fun z => min (n : ENNReal) (h z)) := by
    intro n m hnm z
    -- And again for `h`.
    exact min_le_min (by exact_mod_cast hnm) le_rfl
  have hf_lintegral :
      ∫⁻ x, f x ∂MeasureTheory.volume =
        ⨆ n : ℕ, ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume := by
    -- Monotone convergence upgrades the bounded-value truncations back to `f`.
    calc
      ∫⁻ x, f x ∂MeasureTheory.volume =
          ∫⁻ x, ⨆ n : ℕ, min (n : ENNReal) (f x) ∂MeasureTheory.volume := by
            congr with x
            symm
            exact hpointwise_iSup f x
      _ = ⨆ n : ℕ, ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume := by
            exact MeasureTheory.lintegral_iSup hftr_measurable hftr_mono
  have hg_lintegral :
      ∫⁻ y, g y ∂MeasureTheory.volume =
        ⨆ n : ℕ, ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume := by
    -- The same monotone-convergence passage applies to `g`.
    calc
      ∫⁻ y, g y ∂MeasureTheory.volume =
          ∫⁻ y, ⨆ n : ℕ, min (n : ENNReal) (g y) ∂MeasureTheory.volume := by
            congr with y
            symm
            exact hpointwise_iSup g y
      _ = ⨆ n : ℕ, ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume := by
            exact MeasureTheory.lintegral_iSup hgtr_measurable hgtr_mono
  have hh_lintegral :
      ∫⁻ z, h z ∂MeasureTheory.volume =
        ⨆ n : ℕ, ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume := by
    -- And likewise for the target function `h`.
    calc
      ∫⁻ z, h z ∂MeasureTheory.volume =
          ∫⁻ z, ⨆ n : ℕ, min (n : ENNReal) (h z) ∂MeasureTheory.volume := by
            congr with z
            symm
            exact hpointwise_iSup h z
      _ = ⨆ n : ℕ, ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume := by
            exact MeasureTheory.lintegral_iSup hhtr_measurable hhtr_mono
  have hf_int_mono :
      Monotone (fun n : ℕ => ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) := by
    intro n m hnm
    -- Integral monotonicity follows from pointwise monotonicity of the truncations.
    exact MeasureTheory.lintegral_mono (fun x => hftr_mono hnm x)
  have hg_int_mono :
      Monotone (fun n : ℕ => ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) := by
    intro n m hnm
    -- The same integral monotonicity statement holds for `g`.
    exact MeasureTheory.lintegral_mono (fun y => hgtr_mono hnm y)
  have hdiag_sup :
      (⨆ n : ℕ, ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (⨆ n : ℕ, ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) ≤
        ⨆ n : ℕ,
          (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- A single truncation index dominates any pair of finite value cutoffs.
    have hA_rpow :
        (⨆ n : ℕ, ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ =
          ⨆ n : ℕ, (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ :=
      (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
    have hB_rpow :
        (⨆ n : ℕ, ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) =
          ⨆ n : ℕ, (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) :=
      (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
    rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
    refine iSup_le ?_
    intro m
    rw [ENNReal.mul_iSup]
    refine iSup_le ?_
    intro n
    refine le_iSup_of_le (max m n) ?_
    exact mul_le_mul'
      (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (hf_int_mono (Nat.le_max_left m n)))
      (ENNReal.monotone_rpow_of_nonneg
        (sub_nonneg.mpr hθ_mem.2.le) (hg_int_mono (Nat.le_max_right m n)))
  have hsup_le :
      (⨆ n : ℕ,
        (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ)) ≤
        ⨆ n : ℕ, ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume := by
    refine iSup_le ?_
    intro n
    exact le_iSup_of_le n (htrunc n)
  -- Route correction: once the bounded-value inequality is isolated, the rest is the standard
  -- monotone-convergence diagonal argument on the truncation parameter.
  calc
    ∫⁻ z, h z ∂MeasureTheory.volume =
        ⨆ n : ℕ, ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume := hh_lintegral
    _ ≥
        ⨆ n : ℕ,
          (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := hsup_le
    _ ≥
        (⨆ n : ℕ, ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (⨆ n : ℕ, ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := hdiag_sup
    _ =
        (∫⁻ x, f x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, g y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [hf_lintegral, hg_lintegral]

/-- A support-truncated logarithmic transport is bounded by its value at the left endpoint of the
truncation interval. -/
private lemma supportTrunc_log_profile_bound
    {φ : ℝ → ENNReal}
    (hφ_antitone : Antitone φ)
    (M : ℕ) :
    ∀ x : ℝ,
      supportTrunc (fun u => ENNReal.ofReal (Real.exp u) * φ (Real.exp u)) M x ≤
        ENNReal.ofReal (Real.exp M) * φ (Real.exp (-(M : ℝ))) := by
  intro x
  by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
  · have hx_mem : x ∈ Set.Icc (-(M : ℝ)) M := hx
    rcases hx with ⟨hx_left, hx_right⟩
    have hexp_left : Real.exp (-(M : ℝ)) ≤ Real.exp x := by
      exact Real.exp_le_exp.mpr hx_left
    have hexp_right : Real.exp x ≤ Real.exp M := by
      exact Real.exp_le_exp.mpr hx_right
    have hφ_le : φ (Real.exp x) ≤ φ (Real.exp (-(M : ℝ))) := hφ_antitone hexp_left
    have hexp_le :
        ENNReal.ofReal (Real.exp x) ≤ ENNReal.ofReal (Real.exp M) :=
      ENNReal.ofReal_le_ofReal hexp_right
    -- Inside the support window, monotonicity of `exp` and antitonicity of `φ` give a global
    -- pointwise bound.
    simpa [supportTrunc, hx_mem] using mul_le_mul' hexp_le hφ_le
  · -- Outside the support window, the support truncation already vanishes.
    simp [supportTrunc, hx]

/-- A strict-superlevel profile vanishes once the threshold dominates a global pointwise bound. -/
private lemma strictSuperlevelProfile_eq_zero_of_pointwise_bound
    {f : ℝ → ENNReal}
    {R s : ℝ}
    (hbound : ∀ x : ℝ, f x ≤ ENNReal.ofReal R)
    (hs : R ≤ s) :
    MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < f x} = 0 := by
  have hempty : {x : ℝ | ENNReal.ofReal s < f x} = ∅ := by
    ext x
    constructor
    · intro hx
      exact False.elim (not_lt_of_ge (le_trans (hbound x) (ENNReal.ofReal_le_ofReal hs)) hx)
    · intro hx
      exact False.elim hx
  simp [hempty]

/-- Finite value truncation is compatible with the weighted geometric mean kernel. -/
private lemma value_truncation_geom_mean_le
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (n : ℕ)
    (a b : ENNReal) :
    min (n : ENNReal) a ^ θ * min (n : ENNReal) b ^ (1 - θ) ≤
      min (n : ENNReal) (a ^ θ * b ^ (1 - θ)) := by
  cases n with
  | zero =>
      -- At cutoff `0`, both truncated factors vanish, so the inequality is immediate.
      simp [ENNReal.zero_rpow_of_pos hθ_mem.1, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2)]
  | succ m =>
      have hleft_le_prod :
          min ((Nat.succ m : ℕ) : ENNReal) a ^ θ *
              min ((Nat.succ m : ℕ) : ENNReal) b ^ (1 - θ) ≤
            a ^ θ * b ^ (1 - θ) := by
        -- Truncation only decreases each factor before taking the weighted powers.
        exact mul_le_mul'
          (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (min_le_right _ _))
          (ENNReal.monotone_rpow_of_nonneg (sub_nonneg.mpr hθ_mem.2.le) (min_le_right _ _))
      have hleft_le_cutoff :
          min ((Nat.succ m : ℕ) : ENNReal) a ^ θ *
              min ((Nat.succ m : ℕ) : ENNReal) b ^ (1 - θ) ≤
            ((Nat.succ m : ℕ) : ENNReal) := by
        -- Each truncated factor is bounded by the cutoff, and the exponents sum to `1`.
        calc
          min ((Nat.succ m : ℕ) : ENNReal) a ^ θ *
              min ((Nat.succ m : ℕ) : ENNReal) b ^ (1 - θ) ≤
              ((Nat.succ m : ℕ) : ENNReal) ^ θ *
                ((Nat.succ m : ℕ) : ENNReal) ^ (1 - θ) := by
                  exact mul_le_mul'
                    (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (min_le_left _ _))
                    (ENNReal.monotone_rpow_of_nonneg
                      (sub_nonneg.mpr hθ_mem.2.le) (min_le_left _ _))
          _ = ((Nat.succ m : ℕ) : ENNReal) := by
                have hk_ne_zero : (((Nat.succ m : ℕ) : ENNReal)) ≠ 0 := by simp
                have hk_ne_top : (((Nat.succ m : ℕ) : ENNReal)) ≠ ⊤ := by simp
                rw [← ENNReal.rpow_add _ _ hk_ne_zero hk_ne_top]
                rw [show θ + (1 - θ) = 1 by ring, ENNReal.rpow_one]
      -- Bound the weighted geometric mean simultaneously by the cutoff and by the untruncated
      -- kernel term.
      exact le_min hleft_le_cutoff hleft_le_prod

/-- Support truncation preserves an affine Prékopa-Leindler kernel at each fixed support radius. -/
private lemma supportTrunc_affine_kernel
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (h_kernel :
      ∀ x y : ℝ,
        h (θ * x + (1 - θ) * y) ≥ f x ^ θ * g y ^ (1 - θ))
    (N : ℕ) :
    ∀ x y : ℝ,
      supportTrunc h N (θ * x + (1 - θ) * y) ≥
        supportTrunc f N x ^ θ * supportTrunc g N y ^ (1 - θ) := by
  intro x y
  by_cases hx : x ∈ Set.Icc (-(N : ℝ)) N
  · by_cases hy : y ∈ Set.Icc (-(N : ℝ)) N
    · -- On the common support interval, the support cutoffs disappear.
      have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(N : ℝ)) N := by
        rcases hx with ⟨hx_left, hx_right⟩
        rcases hy with ⟨hy_left, hy_right⟩
        constructor <;>
          nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
      simpa [supportTrunc, hx, hy, hz] using h_kernel x y
    · -- If `y` leaves the support interval, the right-hand side already vanishes.
      have hy_zero : supportTrunc g N y = 0 := by
        simp [supportTrunc, hy]
      rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
      exact bot_le
  · -- Symmetrically when `x` leaves the support interval.
    have hx_zero : supportTrunc f N x = 0 := by
      simp [supportTrunc, hx]
    rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
    exact bot_le

/-- The interval-cutoff profile over `(0, 1)` is exactly the log transport restricted to
`(-∞, 0)`. -/
private lemma cutoffLogIntervalIntegralRewrite
    (φ : ℝ → ENNReal) :
    let φlogCut : ℝ → ENNReal :=
      Set.indicator (Set.Iio (0 : ℝ))
        (fun x => ENNReal.ofReal (Real.exp x) * φ (Real.exp x))
    ∫⁻ x, φlogCut x ∂MeasureTheory.volume =
      ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) φ s ∂MeasureTheory.volume := by
  dsimp
  have hIoo_inter_Ioi :
      Set.Ioo (0 : ℝ) 1 ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
    -- The cutoff interval `(0, 1)` already lies in the positive half-line.
    ext s
    constructor
    · intro hs
      exact hs.1
    · intro hs
      exact ⟨hs, hs.1⟩
  -- Rewrite the interval profile as the logarithmic transport supported on `(-∞, 0)`.
  calc
    ∫⁻ x,
        Set.indicator (Set.Iio (0 : ℝ))
          (fun x => ENNReal.ofReal (Real.exp x) * φ (Real.exp x)) x
        ∂MeasureTheory.volume =
          ∫⁻ s in Set.Ioi 0, Set.indicator (Set.Ioo (0 : ℝ) 1) φ s
            ∂MeasureTheory.volume := by
              simpa [Set.indicator, Real.exp_pos, Real.exp_lt_one_iff] using
                (log_profile_lintegral_eq (phi := Set.indicator (Set.Ioo (0 : ℝ) 1) φ)).symm
    _ = ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) φ s ∂MeasureTheory.volume := by
          simpa [MeasureTheory.lintegral_indicator, hIoo_inter_Ioi]

/-- Monotone convergence recovers a cutoff-log integral from its support truncations. -/
private lemma cutoffLogMonotoneLimit
    {φlogCut : ℝ → ENNReal}
    (hφlogCut_measurable : Measurable φlogCut) :
    let φlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc φlogCut M
    ∫⁻ x, φlogCut x ∂MeasureTheory.volume =
      ⨆ M, ∫⁻ x, φlogCutN M x ∂MeasureTheory.volume := by
  dsimp
  have hφlogCutN_measurable : ∀ M, Measurable (supportTrunc φlogCut M) := by
    intro M
    -- Compact support truncation preserves measurability.
    exact supportTrunc_measurable hφlogCut_measurable M
  have hφlogCutN_mono : Monotone (fun M => supportTrunc φlogCut M) := by
    intro M L hML x
    -- Enlarging the support interval only increases the truncation pointwise.
    exact supportTrunc_mono (f := φlogCut) hML x
  -- Apply monotone convergence to the increasing support truncation family.
  calc
    ∫⁻ x, φlogCut x ∂MeasureTheory.volume =
        ∫⁻ x, ⨆ M, supportTrunc φlogCut M x ∂MeasureTheory.volume := by
          congr with x
          simpa using (iSup_supportTrunc_apply φlogCut x).symm
    _ = ⨆ M, ∫⁻ x, supportTrunc φlogCut M x ∂MeasureTheory.volume :=
        MeasureTheory.lintegral_iSup hφlogCutN_measurable hφlogCutN_mono

/-- The fixed support truncations of the cutoff-log transports inherit the multiplicative kernel on
their strict-superlevel volume profiles. -/
private lemma cutoffLogFixedSupportProfileKernel
    {α β γ : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hα_measurable : Measurable α)
    (hβ_measurable : Measurable β)
    (hγ_measurable : Measurable γ)
    (hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)))
    (M : ℕ) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    let αlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) αlog
    let βlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) βlog
    let γlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) γlog
    let αlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc αlogCut N
    let βlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc βlogCut N
    let γlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc γlogCut N
    let A : ℝ → ENNReal :=
      fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < αlogCutN M x}
    let B : ℝ → ENNReal :=
      fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < βlogCutN M y}
    let C : ℝ → ENNReal :=
      fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < γlogCutN M z}
    ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t ->
      A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ)) := by
  dsimp
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
  let αlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) αlog
  let βlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) βlog
  let γlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) γlog
  let αlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc αlogCut N
  let βlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc βlogCut N
  let γlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc γlogCut N
  let A : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < αlogCutN M x}
  let B : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < βlogCutN M y}
  let C : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < γlogCutN M z}
  have hlog_kernel :
      ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
    intro x y
    -- The multiplicative profile kernel becomes additive after the logarithmic transport.
    simpa [αlog, βlog, γlog] using
      (log_profile_kernel_transport (α := α) (β := β) (γ := γ) hθ_mem hkernel_profile x y)
  have hlogCut_kernel :
      ∀ x y : ℝ, γlogCut (θ * x + (1 - θ) * y) ≥ αlogCut x ^ θ * βlogCut y ^ (1 - θ) := by
    intro x y
    by_cases hx : x < 0
    · by_cases hy : y < 0
      · have hz : θ * x + (1 - θ) * y < 0 := by
          -- Affine combinations of negative inputs stay negative.
          nlinarith [hθ_mem.1, hθ_mem.2, hx, hy]
        -- On `(-∞, 0)`, the cutoff indicators are transparent.
        simpa [αlogCut, βlogCut, γlogCut, Set.indicator, hx, hy, hz] using hlog_kernel x y
      · have hy_mem : y ∉ Set.Iio (0 : ℝ) := by simpa using hy
        have hy_zero : βlogCut y = 0 := by
          simp [βlogCut, hy_mem]
        -- If `y` leaves the cutoff half-line, the right-hand side already vanishes.
        rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hx_mem : x ∉ Set.Iio (0 : ℝ) := by simpa using hx
      have hx_zero : αlogCut x = 0 := by
        simp [αlogCut, hx_mem]
      -- Symmetrically, the first cutoff factor vanishes outside `(-∞, 0)`.
      rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  have hαlogCut_measurable : Measurable αlogCut := by
    -- The cutoff log profile is measurable because both the transport and the indicator are.
    simpa [αlogCut, αlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hα_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hβlogCut_measurable : Measurable βlogCut := by
    -- The same measurability statement holds for `βlogCut`.
    simpa [βlogCut, βlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hβ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hγlogCut_measurable : Measurable γlogCut := by
    -- And likewise for `γlogCut`.
    simpa [γlogCut, γlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hγ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hαlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → αlogCutN M x = 0 := by
    intro x hx
    -- Outside `[-M, M]`, the support truncation vanishes by construction.
    simpa [αlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := αlogCut) (N := M) (x := x) hx)
  have hβlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → βlogCutN M x = 0 := by
    intro x hx
    -- The same support description holds for `βlogCutN`.
    simpa [βlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := βlogCut) (N := M) (x := x) hx)
  have hγlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → γlogCutN M x = 0 := by
    intro x hx
    -- And likewise for `γlogCutN`.
    simpa [γlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := γlogCut) (N := M) (x := x) hx)
  have hlogCut_trunc_kernel :
      ∀ x y,
        γlogCutN M (θ * x + (1 - θ) * y) ≥
          αlogCutN M x ^ θ * βlogCutN M y ^ (1 - θ) := by
    intro x y
    by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
    · by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
      · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(M : ℝ)) M := by
          rcases hx with ⟨hx_left, hx_right⟩
          rcases hy with ⟨hy_left, hy_right⟩
          -- Affine combinations preserve the common truncation interval.
          constructor <;>
            nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
        -- On the common truncation interval, the support cutoffs disappear.
        simpa [αlogCutN, βlogCutN, γlogCutN, supportTrunc, hx, hy, hz] using
          hlogCut_kernel x y
      · have hy_zero : βlogCutN M y = 0 := by
          simp [βlogCutN, supportTrunc, hy]
        -- If `y` leaves the truncation window, the right-hand side already vanishes.
        rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hx_zero : αlogCutN M x = 0 := by
        simp [αlogCutN, supportTrunc, hx]
      -- Symmetrically when `x` leaves the truncation window.
      rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  -- Apply the compact-support profile kernel to the truncated cutoff-log functions.
  simpa [A, B, C] using
    (compactSupport_strictSuperlevelProfile_kernel
      (a := αlogCutN M) (b := βlogCutN M) (c := γlogCutN M)
      hθ_mem (supportTrunc_measurable hαlogCut_measurable M)
      (supportTrunc_measurable hβlogCut_measurable M)
      (supportTrunc_measurable hγlogCut_measurable M)
      M hαlogCutN_support hβlogCutN_support hγlogCutN_support hlogCut_trunc_kernel)

/-- The missing primitive interval-`(0, 1)` positive-profile inequality. -/
private lemma fixedSupportPositiveHalflineProfileCore_logKernel
    {A B C : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hkernel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
    ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
  dsimp
  intro x y
  -- The multiplicative kernel becomes additive after the logarithmic transport `r = exp x`.
  simpa using
    (log_profile_kernel_transport (α := A) (β := B) (γ := C) hθ_mem hkernel x y)

/-- Support truncation preserves the transported logarithmic kernel at each fixed radius. -/
private lemma fixedSupportPositiveHalflineProfileCore_logTruncKernel
    {A B C : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hkernel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
    let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
    let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
    let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
    ∀ M x y,
      γlogN M (θ * x + (1 - θ) * y) ≥
        αlogN M x ^ θ * βlogN M y ^ (1 - θ) := by
  dsimp
  intro M x y
  -- Reuse the transported kernel and the earlier generic support-truncation lemma.
  simpa using
    (supportTrunc_affine_kernel
      (f := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x))
      (g := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y))
      (h := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z))
      hθ_mem
      (fixedSupportPositiveHalflineProfileCore_logKernel
        (A := A) (B := B) (C := C) hθ_mem hkernel)
      M x y)

/-- Each fixed support-truncated logarithmic transport satisfies the bounded-value
Prékopa-Leindler estimate at unit cutoff. -/
private lemma compactSupport_value_truncation_bridge_unit_pretarget
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (N : ℕ)
    (hf_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f x = 0)
    (hg_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g x = 0)
    (hh_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h x = 0)
    (h_kernel :
      ∀ x y : ℝ,
        h (θ * x + (1 - θ) * y) ≥ f x ^ θ * g y ^ (1 - θ)) :
    ∫⁻ z, min (1 : ENNReal) (h z) ∂MeasureTheory.volume ≥
      (∫⁻ x, min (1 : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, min (1 : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
  let α : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < f x}
  let β : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < g y}
  let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < h z}
  have hα_antitone : Antitone α := by
    -- The strict-superlevel profile of `f` is antitone in the threshold parameter.
    simpa [α] using strictSuperlevelProfile_antitone f
  have hβ_antitone : Antitone β := by
    -- The same monotonicity statement holds for `g`.
    simpa [β] using strictSuperlevelProfile_antitone g
  have hγ_antitone : Antitone γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using strictSuperlevelProfile_antitone h
  have hα_profile :
      ∫⁻ x, min (1 : ENNReal) (f x) ∂MeasureTheory.volume =
        ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume := by
    -- Rewrite the unit truncation of `f` as the strict-superlevel profile over `(0, 1)`.
    simpa [α] using ennreal_lintegral_trunc_eq_profile_trunc hf_measurable 1
  have hβ_profile :
      ∫⁻ y, min (1 : ENNReal) (g y) ∂MeasureTheory.volume =
        ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume := by
    -- The same unit-cutoff layer-cake identity holds for `g`.
    simpa [β] using ennreal_lintegral_trunc_eq_profile_trunc hg_measurable 1
  have hγ_profile :
      ∫⁻ z, min (1 : ENNReal) (h z) ∂MeasureTheory.volume =
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume := by
    -- And likewise for the target function `h`.
    simpa [γ] using ennreal_lintegral_trunc_eq_profile_trunc hh_measurable 1
  have hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    -- Route correction: extract the multiplicative profile kernel directly from compact support
    -- before applying the interval-cutoff profile inequality.
    simpa [α, β, γ] using
      (compactSupport_strictSuperlevelProfile_kernel
        (a := f) (b := g) (c := h)
        hθ_mem hf_measurable hg_measurable hh_measurable N
        hf_support hg_support hh_support h_kernel)
  have hprofile :
      ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume ≥
        (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- TODO: Port the standalone interval-cutoff core before this unit-cutoff bridge.
    -- The missing route is the earlier non-circular version of `positiveProfileUnitCutoffCore`,
    -- proved from the fixed-support cutoff-log integral core without depending on later text.
    sorry
  -- Rewrite the three unit truncations to strict-superlevel profile integrals and close with the
  -- interval-profile inequality above.
  calc
    ∫⁻ z, min (1 : ENNReal) (h z) ∂MeasureTheory.volume =
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume := hγ_profile
    _ ≥
        (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume) ^ (1 - θ) :=
            hprofile
    _ =
        (∫⁻ x, min (1 : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, min (1 : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [← hα_profile, ← hβ_profile]

/-- A compactly supported bounded kernel satisfies every finite value-truncation
Prékopa-Leindler estimate. -/
private lemma compactSupport_value_truncation_bridge_pretarget
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (N : ℕ)
    (hf_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f x = 0)
    (hg_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g x = 0)
    (hh_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h x = 0)
    (Rf Rg : ENNReal)
    (hRf_lt_top : Rf < ⊤)
    (hRg_lt_top : Rg < ⊤)
    (hf_bound : ∀ x : ℝ, f x ≤ Rf)
    (hg_bound : ∀ y : ℝ, g y ≤ Rg)
    (h_kernel :
      ∀ x y : ℝ,
        h (θ * x + (1 - θ) * y) ≥ f x ^ θ * g y ^ (1 - θ)) :
    ∀ n : ℕ,
      ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume ≥
        (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
  intro n
  cases n with
  | zero =>
      -- At cutoff `0`, every truncation vanishes, so the inequality is immediate.
      simp [ENNReal.zero_rpow_of_pos hθ_mem.1,
        ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2)]
  | succ m =>
      let k : ENNReal := ((Nat.succ m : ℕ) : ENNReal)
      let f1 : ℝ → ENNReal := fun x => k⁻¹ * f x
      let g1 : ℝ → ENNReal := fun y => k⁻¹ * g y
      let h1 : ℝ → ENNReal := fun z => k⁻¹ * h z
      have hk_ne_zero : k ≠ 0 := by
        dsimp [k]
        norm_num
      have hk_ne_top : k ≠ ⊤ := by
        dsimp [k]
        simp
      have hf1_measurable : Measurable f1 := by
        -- Scaling by a constant preserves measurability.
        simpa [f1] using measurable_const.mul hf_measurable
      have hg1_measurable : Measurable g1 := by
        -- The same normalization applies to `g`.
        simpa [g1] using measurable_const.mul hg_measurable
      have hh1_measurable : Measurable h1 := by
        -- And likewise for `h`.
        simpa [h1] using measurable_const.mul hh_measurable
      have hf1_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f1 x = 0 := by
        intro x hx
        -- The compact support interval is unchanged by value normalization.
        simp [f1, hf_support hx]
      have hg1_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g1 x = 0 := by
        intro x hx
        -- The same support statement holds for the normalized `g`.
        simp [g1, hg_support hx]
      have hh1_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h1 x = 0 := by
        intro x hx
        -- And likewise for the normalized target function.
        simp [h1, hh_support hx]
      have hscaled_rpow :
          ∀ x y : ℝ,
            f1 x ^ θ * g1 y ^ (1 - θ) = k⁻¹ * (f x ^ θ * g y ^ (1 - θ)) := by
        intro x y
        dsimp [f1, g1]
        have hkinv_ne_zero : k⁻¹ ≠ 0 := by
          simpa using hk_ne_top
        have hkinv_ne_top : k⁻¹ ≠ ⊤ := by
          intro htop
          exact hk_ne_zero (ENNReal.inv_eq_top.mp htop)
        -- Route correction: normalize both factors first, then recombine the powers using
        -- `θ + (1 - θ) = 1` so the common factor is exactly `k⁻¹`.
        calc
          (k⁻¹ * f x) ^ θ * (k⁻¹ * g y) ^ (1 - θ) =
              (k⁻¹ ^ θ * f x ^ θ) * (k⁻¹ ^ (1 - θ) * g y ^ (1 - θ)) := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ hθ_mem.1.le,
                  ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hθ_mem.2.le)]
          _ = (k⁻¹ ^ θ * k⁻¹ ^ (1 - θ)) * (f x ^ θ * g y ^ (1 - θ)) := by
                ac_rfl
          _ = (k⁻¹ ^ (θ + (1 - θ))) * (f x ^ θ * g y ^ (1 - θ)) := by
                rw [← ENNReal.rpow_add _ _ hkinv_ne_zero hkinv_ne_top]
          _ = k⁻¹ * (f x ^ θ * g y ^ (1 - θ)) := by
                rw [show θ + (1 - θ) = 1 by ring, ENNReal.rpow_one]
      have h1_kernel :
          ∀ x y : ℝ, h1 (θ * x + (1 - θ) * y) ≥ f1 x ^ θ * g1 y ^ (1 - θ) := by
        intro x y
        -- After normalizing the values, the affine kernel is preserved because the common factor
        -- `k⁻¹` distributes across the weighted geometric mean.
        calc
          h1 (θ * x + (1 - θ) * y) = k⁻¹ * h (θ * x + (1 - θ) * y) := by
              rfl
          _ ≥ k⁻¹ * (f x ^ θ * g y ^ (1 - θ)) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                mul_le_mul_right (h_kernel x y) k⁻¹
          _ = f1 x ^ θ * g1 y ^ (1 - θ) := by
              rw [hscaled_rpow]
      have hunit := compactSupport_value_truncation_bridge_unit_pretarget
        (f := f1) (g := g1) (h := h1)
        hθ_mem hf1_measurable hg1_measurable hh1_measurable N
        hf1_support hg1_support hh1_support h1_kernel
      have hscale_integral (u : ℝ → ENNReal) :
          (∫⁻ z, min k (u z) ∂MeasureTheory.volume) =
            (∫⁻ z, min (1 : ENNReal) (k⁻¹ * u z) ∂MeasureTheory.volume) * k := by
        have hfun :
            (fun z => min k (u z)) =
              (fun z => min (1 : ENNReal) (k⁻¹ * u z) * k) := by
          funext z
          -- The truncation identity `min k u = k * min 1 (k⁻¹ * u)` is the exact rescaling
          -- needed to pass back from the normalized theorem.
          calc
            min k (u z) = min (1 * k) ((k⁻¹ * u z) * k) := by
              congr 1
              · simp
              · calc
                  u z = u z * k⁻¹ * k := by
                      rw [ENNReal.inv_mul_cancel_right hk_ne_zero hk_ne_top]
                  _ = (k⁻¹ * u z) * k := by
                      ac_rfl
            _ = min (1 : ENNReal) (k⁻¹ * u z) * k := by
                  simpa using (min_mul_mul_right (1 : ENNReal) (k⁻¹ * u z) k)
        rw [hfun]
        exact MeasureTheory.lintegral_mul_const' k
          (fun z => min (1 : ENNReal) (k⁻¹ * u z)) hk_ne_top
      have hk_pow :
          (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ))) * k =
            ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) * k) ^ θ *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := by
        -- The product-side rescaling is compatible with the exponents because `θ + (1 - θ) = 1`.
        calc
          (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ))) * k =
              ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ)) *
                  (k ^ (θ + (1 - θ))) := by
                    rw [show k ^ (θ + (1 - θ)) = k by
                      rw [show θ + (1 - θ) = 1 by ring, ENNReal.rpow_one]]
          _ = (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) * k ^ θ) *
                (((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ)) *
                  k ^ (1 - θ)) := by
                    rw [ENNReal.rpow_add _ _ hk_ne_zero hk_ne_top]
                    ac_rfl
          _ = ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) * k) ^ θ *
                ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := by
                    rw [← ENNReal.mul_rpow_of_nonneg _ _ hθ_mem.1.le,
                      ← ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hθ_mem.2.le)]
      have hh_eq := hscale_integral h
      have hf_eq := hscale_integral f
      have hg_eq := hscale_integral g
      -- Route correction: once the unit-cutoff theorem is available, undo the normalization on
      -- all three integrals to recover the original cutoff `k = n.succ`.
      calc
        (∫⁻ z, min k (h z) ∂MeasureTheory.volume) =
            (∫⁻ z, min (1 : ENNReal) (h1 z) ∂MeasureTheory.volume) * k := by
              simpa [h1] using hh_eq
        _ ≥
            (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ))) * k := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_left hunit k
        _ = ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) * k) ^ θ *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := hk_pow
        _ = ((∫⁻ x, min (1 : ENNReal) (k⁻¹ * f x) ∂MeasureTheory.volume) * k) ^ θ *
              ((∫⁻ y, min (1 : ENNReal) (k⁻¹ * g y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := by
              rfl
        _ =
            (∫⁻ x, min k (f x) ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, min k (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [← hf_eq, ← hg_eq]

/-- The bounded-value bridge for positive profiles isolates the remaining `Nat.succ` truncation
step away from the outer compact-support theorem. -/
private lemma positive_profile_value_truncation_bridge_pretarget
    {A B C : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_antitone : Antitone A)
    (hB_antitone : Antitone B)
    (hC_antitone : Antitone C)
    (hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤)
    (hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤)
    (hkernel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ))) :
    let Apos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) A
    let Bpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) B
    let Cpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) C
    ∀ n : ℕ,
      ∫⁻ r, min (n : ENNReal) (Cpos r) ∂MeasureTheory.volume ≥
        (∫⁻ s, min (n : ENNReal) (Apos s) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t, min (n : ENNReal) (Bpos t) ∂MeasureTheory.volume) ^ (1 - θ) := by
  dsimp
  intro n
  cases n with
  | zero =>
      -- At value cutoff `0`, all three truncated integrals vanish.
      simp [ENNReal.zero_rpow_of_pos hθ_mem.1,
        ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2)]
  | succ m =>
      let n : ℕ := m + 1
      have hA_measurable : Measurable A := by
        -- Antitone real profiles are measurable.
        simpa using (Antitone.measurable hA_antitone)
      have hB_measurable : Measurable B := by
        -- The same monotonicity-to-measurability argument applies to `B`.
        simpa using (Antitone.measurable hB_antitone)
      have hC_measurable : Measurable C := by
        -- And likewise for `C`.
        simpa using (Antitone.measurable hC_antitone)
      let Alog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
      let Blog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
      let Clog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
      have hAlog_measurable : Measurable Alog := by
        -- The logarithmic transport is measurable because both `exp` and `A` are measurable.
        simpa [Alog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hA_measurable.comp Real.measurable_exp))
      have hBlog_measurable : Measurable Blog := by
        -- The same change-of-variables measurability statement holds for `Blog`.
        simpa [Blog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hB_measurable.comp Real.measurable_exp))
      have hClog_measurable : Measurable Clog := by
        -- And likewise for `Clog`.
        simpa [Clog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hC_measurable.comp Real.measurable_exp))
      let Apos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) A
      let Bpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) B
      let Cpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) C
      let φA : ℝ → ENNReal := fun r => min (n : ENNReal) (Apos r)
      let φB : ℝ → ENNReal := fun r => min (n : ENNReal) (Bpos r)
      let φC : ℝ → ENNReal := fun r => min (n : ENNReal) (Cpos r)
      let a : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * φA (Real.exp x)
      let b : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * φB (Real.exp y)
      let c : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * φC (Real.exp z)
      let aN : ℕ → ℝ → ENNReal := fun M => supportTrunc a M
      let bN : ℕ → ℝ → ENNReal := fun M => supportTrunc b M
      let cN : ℕ → ℝ → ENNReal := fun M => supportTrunc c M
      have hApos_measurable : Measurable Apos := by
        -- Restricting `A` to the positive half-line preserves measurability.
        simpa [Apos] using hA_measurable.indicator measurableSet_Ioi
      have hBpos_measurable : Measurable Bpos := by
        -- The same positive-half-line restriction works for `B`.
        simpa [Bpos] using hB_measurable.indicator measurableSet_Ioi
      have hCpos_measurable : Measurable Cpos := by
        -- And likewise for `C`.
        simpa [Cpos] using hC_measurable.indicator measurableSet_Ioi
      have hφA_measurable : Measurable φA := by
        -- Finite value truncation preserves measurability for the positive `A`-profile.
        simpa [φA] using measurable_const.min hApos_measurable
      have hφB_measurable : Measurable φB := by
        -- The same truncation statement holds for `B`.
        simpa [φB] using measurable_const.min hBpos_measurable
      have hφC_measurable : Measurable φC := by
        -- And likewise for `C`.
        simpa [φC] using measurable_const.min hCpos_measurable
      have hφA_zero_off :
          ∀ ⦃s : ℝ⦄, s ∉ Set.Ioi (0 : ℝ) → φA s = 0 := by
        intro s hs
        -- Outside the positive half-line, the truncated positive `A`-profile vanishes.
        simp [φA, Apos, hs]
      have hφB_zero_off :
          ∀ ⦃t : ℝ⦄, t ∉ Set.Ioi (0 : ℝ) → φB t = 0 := by
        intro t ht
        -- The same vanishing statement holds for `B`.
        simp [φB, Bpos, ht]
      have hφC_zero_off :
          ∀ ⦃r : ℝ⦄, r ∉ Set.Ioi (0 : ℝ) → φC r = 0 := by
        intro r hr
        -- And likewise for `C`.
        simp [φC, Cpos, hr]
      have hkernel_trunc :
          ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
            φA s ^ θ * φB t ^ (1 - θ) ≤ φC (s ^ θ * t ^ (1 - θ)) := by
        intro s t hs ht
        have hgeom := value_truncation_geom_mean_le hθ_mem n (A s) (B t)
        have hst_pos : 0 < s ^ θ * t ^ (1 - θ) := by
          positivity
        -- Route correction: the value cutoff must be inserted before transporting the kernel to
        -- logarithmic coordinates.
        calc
          φA s ^ θ * φB t ^ (1 - θ) =
              min (n : ENNReal) (A s) ^ θ * min (n : ENNReal) (B t) ^ (1 - θ) := by
                simp [φA, φB, Apos, Bpos, hs, ht]
          _ ≤ min (n : ENNReal) (A s ^ θ * B t ^ (1 - θ)) := hgeom
          _ ≤ min (n : ENNReal) (C (s ^ θ * t ^ (1 - θ))) := by
                exact min_le_min le_rfl (hkernel hs ht)
          _ = φC (s ^ θ * t ^ (1 - θ)) := by
                simp [φC, Cpos, hst_pos]
      have ha_measurable : Measurable a := by
        -- The logarithmic transport is measurable because both `exp` and `φA` are measurable.
        simpa [a] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hφA_measurable.comp Real.measurable_exp))
      have hb_measurable : Measurable b := by
        -- The same change-of-variables measurability statement holds for `b`.
        simpa [b] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hφB_measurable.comp Real.measurable_exp))
      have hc_measurable : Measurable c := by
        -- And likewise for `c`.
        simpa [c] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hφC_measurable.comp Real.measurable_exp))
      have hA_log :
          ∫⁻ x, a x ∂MeasureTheory.volume =
            ∫⁻ s, min (n : ENNReal) (Apos s) ∂MeasureTheory.volume := by
        -- The already value-truncated positive profile is exactly the log transport of `a`.
        calc
          ∫⁻ x, a x ∂MeasureTheory.volume =
              ∫⁻ s in Set.Ioi 0, φA s ∂MeasureTheory.volume := by
                simpa [a, φA] using (log_profile_lintegral_eq (phi := φA)).symm
          _ = ∫⁻ s, Set.indicator (Set.Ioi (0 : ℝ)) φA s ∂MeasureTheory.volume := by
                simp [MeasureTheory.lintegral_indicator, measurableSet_Ioi]
          _ = ∫⁻ s, φA s ∂MeasureTheory.volume := by
                refine MeasureTheory.lintegral_congr_ae ?_
                exact Filter.Eventually.of_forall fun s => by
                  by_cases hs : s ∈ Set.Ioi (0 : ℝ)
                  · simp [Set.indicator, hs]
                  · simp [Set.indicator, hs, hφA_zero_off hs]
          _ = ∫⁻ s, min (n : ENNReal) (Apos s) ∂MeasureTheory.volume := by
                rfl
      have hB_log :
          ∫⁻ y, b y ∂MeasureTheory.volume =
            ∫⁻ t, min (n : ENNReal) (Bpos t) ∂MeasureTheory.volume := by
        -- The same logarithmic rewrite applies to the value-truncated `B`-profile.
        calc
          ∫⁻ y, b y ∂MeasureTheory.volume =
              ∫⁻ t in Set.Ioi 0, φB t ∂MeasureTheory.volume := by
                simpa [b, φB] using (log_profile_lintegral_eq (phi := φB)).symm
          _ = ∫⁻ t, Set.indicator (Set.Ioi (0 : ℝ)) φB t ∂MeasureTheory.volume := by
                simp [MeasureTheory.lintegral_indicator, measurableSet_Ioi]
          _ = ∫⁻ t, φB t ∂MeasureTheory.volume := by
                refine MeasureTheory.lintegral_congr_ae ?_
                exact Filter.Eventually.of_forall fun t => by
                  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
                  · simp [Set.indicator, ht]
                  · simp [Set.indicator, ht, hφB_zero_off ht]
          _ = ∫⁻ t, min (n : ENNReal) (Bpos t) ∂MeasureTheory.volume := by
                rfl
      have hC_log :
          ∫⁻ z, c z ∂MeasureTheory.volume =
            ∫⁻ r, min (n : ENNReal) (Cpos r) ∂MeasureTheory.volume := by
        -- And likewise for the target value-truncated `C`-profile.
        calc
          ∫⁻ z, c z ∂MeasureTheory.volume =
              ∫⁻ r in Set.Ioi 0, φC r ∂MeasureTheory.volume := by
                simpa [c, φC] using (log_profile_lintegral_eq (phi := φC)).symm
          _ = ∫⁻ r, Set.indicator (Set.Ioi (0 : ℝ)) φC r ∂MeasureTheory.volume := by
                simp [MeasureTheory.lintegral_indicator, measurableSet_Ioi]
          _ = ∫⁻ r, φC r ∂MeasureTheory.volume := by
                refine MeasureTheory.lintegral_congr_ae ?_
                exact Filter.Eventually.of_forall fun r => by
                  by_cases hr : r ∈ Set.Ioi (0 : ℝ)
                  · simp [Set.indicator, hr]
                  · simp [Set.indicator, hr, hφC_zero_off hr]
          _ = ∫⁻ r, min (n : ENNReal) (Cpos r) ∂MeasureTheory.volume := by
                rfl
      have hlog_kernel :
          ∀ x y : ℝ, c (θ * x + (1 - θ) * y) ≥ a x ^ θ * b y ^ (1 - θ) := by
        intro x y
        -- The multiplicative kernel for the value-truncated profiles becomes additive after the
        -- logarithmic transport.
        simpa [a, b, c] using
          (log_profile_kernel_transport
            (α := φA) (β := φB) (γ := φC) hθ_mem hkernel_trunc x y)
      have haN_measurable : ∀ M, Measurable (aN M) := by
        intro M
        -- Compact support truncation preserves measurability for `a`.
        simpa [aN] using supportTrunc_measurable ha_measurable M
      have hbN_measurable : ∀ M, Measurable (bN M) := by
        intro M
        -- The same support truncation argument applies to `b`.
        simpa [bN] using supportTrunc_measurable hb_measurable M
      have hcN_measurable : ∀ M, Measurable (cN M) := by
        intro M
        -- And likewise for `c`.
        simpa [cN] using supportTrunc_measurable hc_measurable M
      have haN_mono : Monotone aN := by
        intro M L hML x
        -- Enlarging the support interval only increases the truncated `a`.
        simpa [aN] using supportTrunc_mono (f := a) hML x
      have hbN_mono : Monotone bN := by
        intro M L hML y
        -- The same pointwise monotonicity holds for `b`.
        simpa [bN] using supportTrunc_mono (f := b) hML y
      have hcN_mono : Monotone cN := by
        intro M L hML z
        -- And again for the target `c`.
        simpa [cN] using supportTrunc_mono (f := c) hML z
      have htrunc :
          ∀ M : ℕ,
            ∫⁻ z, cN M z ∂MeasureTheory.volume ≥
              (∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
        intro M
        have hkernel_support :
            ∀ x y : ℝ, cN M (θ * x + (1 - θ) * y) ≥ aN M x ^ θ * bN M y ^ (1 - θ) := by
          -- Route correction: isolate the fixed-radius support-truncated kernel first so the only
          -- remaining blocker is the standalone bounded-value compact-support theorem.
          simpa [aN, bN, cN] using
            (supportTrunc_affine_kernel
              (f := a) (g := b) (h := c) hθ_mem hlog_kernel M)
        have haN_support :
            ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → aN M x = 0 := by
          intro x hx
          -- Outside `[-M, M]`, the support truncation of `a` vanishes by construction.
          simpa [aN] using
            (supportTrunc_eq_zero_of_not_mem (f := a) (N := M) (x := x) hx)
        have hbN_support :
            ∀ ⦃y : ℝ⦄, y ∉ Set.Icc (-(M : ℝ)) M → bN M y = 0 := by
          intro y hy
          -- The same support cutoff description holds for `b`.
          simpa [bN] using
            (supportTrunc_eq_zero_of_not_mem (f := b) (N := M) (x := y) hy)
        have hcN_support :
            ∀ ⦃z : ℝ⦄, z ∉ Set.Icc (-(M : ℝ)) M → cN M z = 0 := by
          intro z hz
          -- And likewise for `c`.
          simpa [cN] using
            (supportTrunc_eq_zero_of_not_mem (f := c) (N := M) (x := z) hz)
        have haN_bound :
            ∀ x : ℝ,
              aN M x ≤ ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) := by
          intro x
          by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
          · rcases hx with ⟨hx_left, hx_right⟩
            have hx_mem : x ∈ Set.Icc (-(M : ℝ)) M := ⟨hx_left, hx_right⟩
            have hexp_left : Real.exp (-(M : ℝ)) ≤ Real.exp x := by
              exact Real.exp_le_exp.mpr hx_left
            have hexp_right : Real.exp x ≤ Real.exp M := by
              exact Real.exp_le_exp.mpr hx_right
            have hφA_le : φA (Real.exp x) ≤ A (Real.exp x) := by
              -- On the positive half-line, value truncation only decreases `A`.
              simp [φA, Apos, Real.exp_pos]
            have hA_le : A (Real.exp x) ≤ A (Real.exp (-(M : ℝ))) := hA_antitone hexp_left
            have hexp_le :
                ENNReal.ofReal (Real.exp x) ≤ ENNReal.ofReal (Real.exp M) :=
              ENNReal.ofReal_le_ofReal hexp_right
            -- Combine the value truncation bound with the endpoint control from antitonicity.
            calc
              aN M x = ENNReal.ofReal (Real.exp x) * φA (Real.exp x) := by
                simp [aN, a, supportTrunc, hx_mem]
              _ ≤ ENNReal.ofReal (Real.exp x) * A (Real.exp x) := by
                    exact mul_le_mul' le_rfl hφA_le
              _ ≤ ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) := by
                    exact mul_le_mul' hexp_le hA_le
          · -- Outside the support window, `aN M` already vanishes.
            simp [aN, supportTrunc, hx]
        have hbN_bound :
            ∀ y : ℝ,
              bN M y ≤ ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) := by
          intro y
          by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
          · rcases hy with ⟨hy_left, hy_right⟩
            have hy_mem : y ∈ Set.Icc (-(M : ℝ)) M := ⟨hy_left, hy_right⟩
            have hexp_left : Real.exp (-(M : ℝ)) ≤ Real.exp y := by
              exact Real.exp_le_exp.mpr hy_left
            have hexp_right : Real.exp y ≤ Real.exp M := by
              exact Real.exp_le_exp.mpr hy_right
            have hφB_le : φB (Real.exp y) ≤ B (Real.exp y) := by
              -- On the positive half-line, value truncation only decreases `B`.
              simp [φB, Bpos, Real.exp_pos]
            have hB_le : B (Real.exp y) ≤ B (Real.exp (-(M : ℝ))) := hB_antitone hexp_left
            have hexp_le :
                ENNReal.ofReal (Real.exp y) ≤ ENNReal.ofReal (Real.exp M) :=
              ENNReal.ofReal_le_ofReal hexp_right
            -- The same endpoint control bounds the transported `B`-profile on `[-M, M]`.
            calc
              bN M y = ENNReal.ofReal (Real.exp y) * φB (Real.exp y) := by
                simp [bN, b, supportTrunc, hy_mem]
              _ ≤ ENNReal.ofReal (Real.exp y) * B (Real.exp y) := by
                    exact mul_le_mul' le_rfl hφB_le
              _ ≤ ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) := by
                    exact mul_le_mul' hexp_le hB_le
          · -- Outside the support window, `bN M` already vanishes.
            simp [bN, supportTrunc, hy]
        have hA_cap_lt_top :
            ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) < ⊤ := by
          -- The explicit `A`-bound is finite because `A` is finite on positive radii.
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hA_lt_top (Real.exp_pos _))
        have hB_cap_lt_top :
            ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) < ⊤ := by
          -- The same finiteness statement holds for the explicit `B`-bound.
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hB_lt_top (Real.exp_pos _))
        have hvalue_trunc :
            ∀ n : ℕ,
              ∫⁻ z, min (n : ENNReal) (cN M z) ∂MeasureTheory.volume ≥
                (∫⁻ x, min (n : ENNReal) (aN M x) ∂MeasureTheory.volume) ^ θ *
                  (∫⁻ y, min (n : ENNReal) (bN M y) ∂MeasureTheory.volume) ^ (1 - θ) := by
          -- Route correction: the old circular route through later compact-support wrappers is
          -- replaced by the dedicated standalone bounded-value compact-support theorem.
          exact compactSupport_value_truncation_bridge_pretarget
            (f := aN M) (g := bN M) (h := cN M)
            hθ_mem (haN_measurable M) (hbN_measurable M) (hcN_measurable M)
            M haN_support hbN_support hcN_support
            (ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))))
            (ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))))
            hA_cap_lt_top hB_cap_lt_top haN_bound hbN_bound hkernel_support
        -- Once every finite value truncation of `aN M`, `bN M`, and `cN M` satisfies the
        -- inequality, monotone convergence upgrades it to the full fixed-support statement.
        exact prekopaLeindler_from_value_truncations
          hθ_mem (haN_measurable M) (hbN_measurable M) (hcN_measurable M) hvalue_trunc
      have ha_lintegral :
          ∫⁻ x, a x ∂MeasureTheory.volume =
            ⨆ M, ∫⁻ x, aN M x ∂MeasureTheory.volume := by
        -- Monotone convergence sends the support truncations back to the full `a`-integral.
        calc
          ∫⁻ x, a x ∂MeasureTheory.volume =
              ∫⁻ x, ⨆ M, aN M x ∂MeasureTheory.volume := by
                congr with x
                simpa [aN] using (iSup_supportTrunc_apply a x).symm
          _ = ⨆ M, ∫⁻ x, aN M x ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup haN_measurable haN_mono
      have hb_lintegral :
          ∫⁻ y, b y ∂MeasureTheory.volume =
            ⨆ M, ∫⁻ y, bN M y ∂MeasureTheory.volume := by
        -- The same monotone-convergence rewrite applies to `b`.
        calc
          ∫⁻ y, b y ∂MeasureTheory.volume =
              ∫⁻ y, ⨆ M, bN M y ∂MeasureTheory.volume := by
                congr with y
                simpa [bN] using (iSup_supportTrunc_apply b y).symm
          _ = ⨆ M, ∫⁻ y, bN M y ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup hbN_measurable hbN_mono
      have hc_lintegral :
          ∫⁻ z, c z ∂MeasureTheory.volume =
            ⨆ M, ∫⁻ z, cN M z ∂MeasureTheory.volume := by
        -- And likewise for the target `c`.
        calc
          ∫⁻ z, c z ∂MeasureTheory.volume =
              ∫⁻ z, ⨆ M, cN M z ∂MeasureTheory.volume := by
                congr with z
                simpa [cN] using (iSup_supportTrunc_apply c z).symm
          _ = ⨆ M, ∫⁻ z, cN M z ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup hcN_measurable hcN_mono
      have ha_int_mono :
          Monotone (fun M => ∫⁻ x, aN M x ∂MeasureTheory.volume) := by
        intro M L hML
        -- Integral monotonicity follows from pointwise monotonicity of `aN`.
        exact MeasureTheory.lintegral_mono (fun x => haN_mono hML x)
      have hb_int_mono :
          Monotone (fun M => ∫⁻ y, bN M y ∂MeasureTheory.volume) := by
        intro M L hML
        -- The same integral monotonicity statement holds for `bN`.
        exact MeasureTheory.lintegral_mono (fun y => hbN_mono hML y)
      have hdiag_sup :
          (⨆ M, ∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
              (⨆ M, ∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) ≤
            ⨆ M,
              (∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
        -- A single large support radius dominates any pair of truncation indices.
        have hA_rpow :
            (⨆ M, ∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ =
              ⨆ M, (∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ :=
          (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
        have hB_rpow :
            (⨆ M, ∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) =
              ⨆ M, (∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) :=
          (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
        rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
        refine iSup_le ?_
        intro m
        rw [ENNReal.mul_iSup]
        refine iSup_le ?_
        intro l
        refine le_iSup_of_le (max m l) ?_
        exact mul_le_mul'
          (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (ha_int_mono (Nat.le_max_left m l)))
          (ENNReal.monotone_rpow_of_nonneg
            (sub_nonneg.mpr hθ_mem.2.le) (hb_int_mono (Nat.le_max_right m l)))
      have hsup_le :
          (⨆ M,
            (∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
            ⨆ M, ∫⁻ z, cN M z ∂MeasureTheory.volume := by
        refine iSup_le ?_
        intro M
        exact le_iSup_of_le M (htrunc M)
      have hresult :
          ∫⁻ z, c z ∂MeasureTheory.volume ≥
            (∫⁻ x, a x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, b y ∂MeasureTheory.volume) ^ (1 - θ) := by
        -- Once the fixed-support inequalities are available, monotone convergence in the support
        -- radius upgrades them to the full log-transported value-truncated profiles.
        calc
          ∫⁻ z, c z ∂MeasureTheory.volume =
              ⨆ M, ∫⁻ z, cN M z ∂MeasureTheory.volume := hc_lintegral
          _ ≥
              ⨆ M,
                (∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
                  (∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) := hsup_le
          _ ≥
              (⨆ M, ∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
                (⨆ M, ∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) := hdiag_sup
          _ =
              (∫⁻ x, a x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, b y ∂MeasureTheory.volume) ^ (1 - θ) := by
                  rw [ha_lintegral, hb_lintegral]
      -- Route correction: the old proof tried to recurse on lower value cutoffs. The current
      -- route freezes the cutoff `n`, transports the truncated positive profiles to log
      -- coordinates, proves the fixed-support inequality there, and then lets the support radius
      -- tend to infinity.
      calc
        ∫⁻ r, min (n : ENNReal) (Cpos r) ∂MeasureTheory.volume =
            ∫⁻ z, c z ∂MeasureTheory.volume := by
              rw [← hC_log]
        _ ≥
            (∫⁻ x, a x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, b y ∂MeasureTheory.volume) ^ (1 - θ) := hresult
        _ =
            (∫⁻ s, min (n : ENNReal) (Apos s) ∂MeasureTheory.volume) ^ θ *
              (∫⁻ t, min (n : ENNReal) (Bpos t) ∂MeasureTheory.volume) ^ (1 - θ) := by
                rw [hA_log, hB_log]

/-- The remaining compactly supported logarithmic-profile truncation step needed for the direct
compact-support Prékopa-Leindler argument. -/
private lemma positive_profile_core_compact_support_direct_log_profile_base_pretarget
    {α β γ : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hα_measurable : Measurable α)
    (hβ_measurable : Measurable β)
    (hγ_measurable : Measurable γ)
    (hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
    let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
    let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
    ∀ M : ℕ,
      ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
        (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
  dsimp
  intro M
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
  let αlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc αlog L
  let βlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc βlog L
  let γlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc γlog L
  let A : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < αlogN M x}
  let B : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < βlogN M y}
  let C : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < γlogN M z}
  change
    ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
      (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ)
  have hlog_kernel :
      ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
    intro x y
    -- The multiplicative profile kernel becomes additive after the logarithmic transport.
    simpa [αlog, βlog, γlog] using
      (log_profile_kernel_transport (α := α) (β := β) (γ := γ) hθ_mem hkernel_profile x y)
  have hlog_trunc_kernel :
      ∀ x y,
        γlogN M (θ * x + (1 - θ) * y) ≥
          αlogN M x ^ θ * βlogN M y ^ (1 - θ) := by
    intro x y
    by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
    · by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
      · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(M : ℝ)) M := by
          rcases hx with ⟨hx_left, hx_right⟩
          rcases hy with ⟨hy_left, hy_right⟩
          -- Affine combinations of points in `[-M, M]` stay in the same compact interval.
          constructor <;>
            nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
        -- On the common truncation interval, the support cutoffs disappear.
        simpa [αlogN, βlogN, γlogN, supportTrunc, hx, hy, hz] using hlog_kernel x y
      · have hy_zero : βlogN M y = 0 := by
          simp [βlogN, supportTrunc, hy]
        -- If `y` leaves the truncation window, the right-hand side already vanishes.
        rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hx_zero : αlogN M x = 0 := by
        simp [αlogN, supportTrunc, hx]
      -- Symmetrically when `x` leaves the truncation window.
      rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  have hαlog_measurable : Measurable αlog := by
    -- The logarithmic transport is measurable because both `exp` and `α` are measurable.
    simpa [αlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hα_measurable.comp Real.measurable_exp))
  have hβlog_measurable : Measurable βlog := by
    -- The same change-of-variables measurability statement holds for `βlog`.
    simpa [βlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hβ_measurable.comp Real.measurable_exp))
  have hγlog_measurable : Measurable γlog := by
    -- And likewise for `γlog`.
    simpa [γlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hγ_measurable.comp Real.measurable_exp))
  have hαlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → αlogN M x = 0 := by
    intro x hx
    -- Outside `[-M, M]`, the support truncation of `αlog` vanishes by construction.
    simpa [αlogN] using (supportTrunc_eq_zero_of_not_mem (f := αlog) (N := M) (x := x) hx)
  have hβlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → βlogN M x = 0 := by
    intro x hx
    -- The same support cutoff description holds for `βlog`.
    simpa [βlogN] using (supportTrunc_eq_zero_of_not_mem (f := βlog) (N := M) (x := x) hx)
  have hγlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → γlogN M x = 0 := by
    intro x hx
    -- And likewise for `γlog`.
    simpa [γlogN] using (supportTrunc_eq_zero_of_not_mem (f := γlog) (N := M) (x := x) hx)
  have hA_antitone : Antitone A := by
    -- Strict-superlevel volume profiles are antitone in the threshold parameter.
    simpa [A] using strictSuperlevelProfile_antitone (αlogN M)
  have hB_antitone : Antitone B := by
    -- The same monotonicity statement holds for `βlogN M`.
    simpa [B] using strictSuperlevelProfile_antitone (βlogN M)
  have hC_antitone : Antitone C := by
    -- And likewise for `γlogN M`.
    simpa [C] using strictSuperlevelProfile_antitone (γlogN M)
  have hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤ := by
    intro s hs
    -- Positive strict superlevel sets stay inside the compact support interval `[-M, M]`.
    apply volume_lt_top_of_subset_supportInterval
    exact strictSuperlevel_subset_support hαlogN_support hs
  have hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤ := by
    intro t ht
    -- The same finite-volume reduction applies to `βlogN M`.
    apply volume_lt_top_of_subset_supportInterval
    exact strictSuperlevel_subset_support hβlogN_support ht
  have hkernel_fixed :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ)) := by
    -- Route correction: the remaining kernel on the strict-superlevel profiles is now obtained
    -- directly from the fixed compactly supported log transports, without re-entering the later
    -- wrapper chain.
    simpa [A, B, C] using
      (compactSupport_strictSuperlevelProfile_kernel
        (a := αlogN M) (b := βlogN M) (c := γlogN M)
        hθ_mem (supportTrunc_measurable hαlog_measurable M)
        (supportTrunc_measurable hβlog_measurable M)
        (supportTrunc_measurable hγlog_measurable M)
        M hαlogN_support hβlogN_support hγlogN_support hlog_trunc_kernel)
  have hα_profile :
      ∫⁻ x, αlogN M x ∂MeasureTheory.volume =
        ∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume := by
    -- Layer-cake rewrites the truncated log integral as its strict-superlevel profile.
    simpa [A] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hαlog_measurable M) (f := αlogN M))
  have hβ_profile :
      ∫⁻ y, βlogN M y ∂MeasureTheory.volume =
        ∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume := by
    -- The same layer-cake identity applies to `βlogN M`.
    simpa [B] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hβlog_measurable M) (f := βlogN M))
  have hγ_profile :
      ∫⁻ z, γlogN M z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume := by
    -- And likewise for `γlogN M`.
    simpa [C] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hγlog_measurable M) (f := γlogN M))
  have hcore :
      ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume ≥
        (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := by
    have hA_measurable : Measurable A := by
      -- Strict-superlevel profiles are measurable because they are antitone.
      simpa using (Antitone.measurable hA_antitone)
    have hB_measurable : Measurable B := by
      -- The same monotonicity-to-measurability argument applies to `B`.
      simpa using (Antitone.measurable hB_antitone)
    have hC_measurable : Measurable C := by
      -- And likewise for `C`.
      simpa using (Antitone.measurable hC_antitone)
    let Apos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) A
    let Bpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) B
    let Cpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) C
    have hApos_measurable : Measurable Apos := by
      -- Restricting the positive-profile to `(0, ∞)` preserves measurability.
      simpa [Apos] using hA_measurable.indicator measurableSet_Ioi
    have hBpos_measurable : Measurable Bpos := by
      -- The same positive-half-line restriction works for `B`.
      simpa [Bpos] using hB_measurable.indicator measurableSet_Ioi
    have hCpos_measurable : Measurable Cpos := by
      -- And likewise for `C`.
      simpa [Cpos] using hC_measurable.indicator measurableSet_Ioi
    have htrunc :
        ∀ n : ℕ,
          ∫⁻ r, min (n : ENNReal) (Cpos r) ∂MeasureTheory.volume ≥
            (∫⁻ s, min (n : ENNReal) (Apos s) ∂MeasureTheory.volume) ^ θ *
              (∫⁻ t, min (n : ENNReal) (Bpos t) ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- Route correction: factor the broken inline `Nat.succ` branch through the dedicated
      -- bounded-value positive-profile bridge, so the target theorem only depends on the corrected
      -- truncation object rather than mismatched lower-layer profile identities.
      simpa [Apos, Bpos, Cpos] using
        (positive_profile_value_truncation_bridge_pretarget
          (A := A) (B := B) (C := C)
          hθ_mem hA_antitone hB_antitone hC_antitone hA_lt_top hB_lt_top hkernel_fixed)
    -- Once every finite value truncation satisfies Prékopa-Leindler, monotone convergence upgrades
    -- the estimates to the full positive-half-line integrals of `A`, `B`, and `C`.
    simpa [Apos, Bpos, Cpos, MeasureTheory.lintegral_indicator] using
      (prekopaLeindler_from_value_truncations
        hθ_mem hApos_measurable hBpos_measurable hCpos_measurable htrunc)
  calc
    ∫⁻ z, γlogN M z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume := hγ_profile
    _ ≥
        (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := hcore
    _ =
        (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [← hα_profile, ← hβ_profile]

/-- Each fixed support-truncated logarithmic transport satisfies the bounded-value
Prékopa-Leindler inequality. -/
private lemma positive_profile_core_compact_support_direct_pretarget
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (N : ℕ)
    (hf_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f x = 0)
    (hg_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g x = 0)
    (hh_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h x = 0)
    (h_kernel :
      ∀ x y : ℝ,
        h (θ * x + (1 - θ) * y) ≥ f x ^ θ * g y ^ (1 - θ)) :
    ∫⁻ z, h z ∂MeasureTheory.volume ≥
      (∫⁻ x, f x ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, g y ∂MeasureTheory.volume) ^ (1 - θ) := by
  let α : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < f x}
  let β : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < g y}
  let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < h z}
  have hα_antitone : Antitone α := by
    -- The strict-superlevel profile of `f` is antitone in the threshold parameter.
    simpa [α] using strictSuperlevelProfile_antitone f
  have hβ_antitone : Antitone β := by
    -- The same monotonicity statement holds for `g`.
    simpa [β] using strictSuperlevelProfile_antitone g
  have hγ_antitone : Antitone γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using strictSuperlevelProfile_antitone h
  have hα_measurable : Measurable α := by
    -- Antitone real profiles are measurable.
    simpa [α] using (Antitone.measurable hα_antitone)
  have hβ_measurable : Measurable β := by
    -- The same monotonicity-to-measurability argument applies to `β`.
    simpa [β] using (Antitone.measurable hβ_antitone)
  have hγ_measurable : Measurable γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using (Antitone.measurable hγ_antitone)
  have hα_profile :
      ∫⁻ x, f x ∂MeasureTheory.volume =
        ∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume := by
    -- The layer-cake identity rewrites the `f`-integral in terms of its strict-superlevel
    -- profile.
    simpa [α] using ennreal_lintegral_eq_strictSuperlevelProfile hf_measurable (f := f)
  have hβ_profile :
      ∫⁻ y, g y ∂MeasureTheory.volume =
        ∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume := by
    -- The same strict-superlevel formula applies to `g`.
    simpa [β] using ennreal_lintegral_eq_strictSuperlevelProfile hg_measurable (f := g)
  have hγ_profile :
      ∫⁻ z, h z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := by
    -- And likewise for the target function `h`.
    simpa [γ] using ennreal_lintegral_eq_strictSuperlevelProfile hh_measurable (f := h)
  have hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    -- Route correction: instead of re-entering the recursive logarithmic transport, first extract
    -- the exact strict-superlevel kernel that already follows from compact support on the source
    -- side.
    simpa [α, β, γ] using
      (compactSupport_strictSuperlevelProfile_kernel
        (a := f) (b := g) (c := h)
        hθ_mem hf_measurable hg_measurable hh_measurable N
        hf_support hg_support hh_support h_kernel)
  have h_profile :
      ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume ≥
        (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := by
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    have hα_log :
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
          ∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume := by
      -- The `f`-profile over `Set.Ioi 0` is exactly the full-line integral of its log transport.
      simpa [αlog] using (log_profile_lintegral_eq (phi := α)).symm
    have hβ_log :
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
          ∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume := by
      -- The same logarithmic change of variables applies to `β`.
      simpa [βlog] using (log_profile_lintegral_eq (phi := β)).symm
    have hγ_log :
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
          ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := by
      -- And likewise for the target profile `γ`.
      simpa [γlog] using (log_profile_lintegral_eq (phi := γ)).symm
    have hlog_kernel :
        ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
      intro x y
      -- Route correction: the multiplicative profile kernel becomes additive after the logarithmic
      -- transport `r = exp x`.
      simpa [αlog, βlog, γlog] using
        (log_profile_kernel_transport (α := α) (β := β) (γ := γ) hθ_mem hkernel_profile x y)
    let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
    let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
    let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
    have hαlog_measurable : Measurable αlog := by
      -- The logarithmic transport is measurable because both `exp` and `α` are measurable.
      simpa [αlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hα_measurable.comp Real.measurable_exp))
    have hβlog_measurable : Measurable βlog := by
      -- The same change-of-variables measurability statement holds for `βlog`.
      simpa [βlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hβ_measurable.comp Real.measurable_exp))
    have hγlog_measurable : Measurable γlog := by
      -- And again for `γlog`.
      simpa [γlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hγ_measurable.comp Real.measurable_exp))
    have hαlogN_measurable : ∀ M, Measurable (αlogN M) := by
      intro M
      -- Compact support truncation preserves measurability for the transported `α`-profile.
      simpa [αlogN] using supportTrunc_measurable hαlog_measurable M
    have hβlogN_measurable : ∀ M, Measurable (βlogN M) := by
      intro M
      -- The same support truncation argument applies to `βlog`.
      simpa [βlogN] using supportTrunc_measurable hβlog_measurable M
    have hγlogN_measurable : ∀ M, Measurable (γlogN M) := by
      intro M
      -- And likewise for `γlog`.
      simpa [γlogN] using supportTrunc_measurable hγlog_measurable M
    have hαlogN_mono : Monotone αlogN := by
      intro M L hML x
      -- Enlarging the compact truncation interval only increases the truncated `αlog` profile.
      simpa [αlogN] using supportTrunc_mono (f := αlog) hML x
    have hβlogN_mono : Monotone βlogN := by
      intro M L hML y
      -- The same pointwise monotonicity holds for the `βlog` truncations.
      simpa [βlogN] using supportTrunc_mono (f := βlog) hML y
    have hγlogN_mono : Monotone γlogN := by
      intro M L hML z
      -- And again for the target `γlog` truncations.
      simpa [γlogN] using supportTrunc_mono (f := γlog) hML z
    have htrunc :
        ∀ M : ℕ,
          ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
            (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- Route correction: the whole remaining analytic gap is isolated in the dedicated helper
      -- `positive_profile_core_compact_support_direct_log_profile_base_pretarget`.
      simpa [α, β, γ, αlog, βlog, γlog, αlogN, βlogN, γlogN] using
        (positive_profile_core_compact_support_direct_log_profile_base_pretarget
          (α := α) (β := β) (γ := γ)
          hθ_mem hα_measurable hβ_measurable hγ_measurable hkernel_profile)
    have hαlog_lintegral :
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume := by
      -- Monotone convergence sends the compact log truncations back to the full `αlog` integral.
      calc
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
            ∫⁻ x, ⨆ M, αlogN M x ∂MeasureTheory.volume := by
              congr with x
              simpa [αlogN] using (iSup_supportTrunc_apply αlog x).symm
        _ = ⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hαlogN_measurable hαlogN_mono
    have hβlog_lintegral :
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume := by
      -- The same monotone-convergence rewrite applies to `βlog`.
      calc
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
            ∫⁻ y, ⨆ M, βlogN M y ∂MeasureTheory.volume := by
              congr with y
              simpa [βlogN] using (iSup_supportTrunc_apply βlog y).symm
        _ = ⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hβlogN_measurable hβlogN_mono
    have hγlog_lintegral :
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := by
      -- And likewise for the target `γlog`.
      calc
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
            ∫⁻ z, ⨆ M, γlogN M z ∂MeasureTheory.volume := by
              congr with z
              simpa [γlogN] using (iSup_supportTrunc_apply γlog z).symm
        _ = ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hγlogN_measurable hγlogN_mono
    have hαlog_int_mono :
        Monotone (fun M => ∫⁻ x, αlogN M x ∂MeasureTheory.volume) := by
      intro M L hML
      -- Integral monotonicity follows from pointwise monotonicity of the truncations.
      exact MeasureTheory.lintegral_mono (fun x => hαlogN_mono hML x)
    have hβlog_int_mono :
        Monotone (fun M => ∫⁻ y, βlogN M y ∂MeasureTheory.volume) := by
      intro M L hML
      -- The same integral monotonicity statement holds for `βlog`.
      exact MeasureTheory.lintegral_mono (fun y => hβlogN_mono hML y)
    have hlog_diag_sup :
        (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) ≤
          ⨆ M,
            (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- A single large truncation index dominates any pair of compact log truncations.
      have hA_rpow :
          (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ =
            ⨆ M, (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ :=
        (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
      have hB_rpow :
          (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) =
            ⨆ M, (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) :=
        (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
      rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
      refine iSup_le ?_
      intro m
      rw [ENNReal.mul_iSup]
      refine iSup_le ?_
      intro n
      refine le_iSup_of_le (max m n) ?_
      exact mul_le_mul'
        (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (hαlog_int_mono (Nat.le_max_left m n)))
        (ENNReal.monotone_rpow_of_nonneg
          (sub_nonneg.mpr hθ_mem.2.le) (hβlog_int_mono (Nat.le_max_right m n)))
    have hlog_sup_le :
        (⨆ M,
          (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
          ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := by
      refine iSup_le ?_
      intro M
      exact le_iSup_of_le M (htrunc M)
    -- Route correction: once the bounded log-truncation step is isolated as `htrunc`, the rest of
    -- the argument is the deterministic monotone-convergence passage back to the full line.
    calc
      ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume = ∫⁻ z, γlog z ∂MeasureTheory.volume := by
        symm
        exact hγ_log
      _ = ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := hγlog_lintegral
      _ ≥
          ⨆ M,
            (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_sup_le
      _ ≥
          (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_diag_sup
      _ =
          (∫⁻ x, αlog x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlog y ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [hαlog_lintegral, hβlog_lintegral]
      _ =
          (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
            (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [hα_log, hβ_log]
  calc
    ∫⁻ z, h z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := hγ_profile
    _ ≥
        (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := h_profile
    _ =
        (∫⁻ x, f x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, g y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [← hα_profile, ← hβ_profile]

/-- Each fixed support-truncated logarithmic transport satisfies the bounded-value
Prékopa-Leindler inequality. -/
private lemma fixedSupportPositiveHalflineProfileCore_logTruncBounded
    {A B C : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_antitone : Antitone A)
    (hB_antitone : Antitone B)
    (hC_antitone : Antitone C)
    (hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤)
    (hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤)
    (hkernel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
    let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
    let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
    let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
    ∀ M n : ℕ,
      ∫⁻ z, min (n : ENNReal) (γlogN M z) ∂MeasureTheory.volume ≥
        (∫⁻ x, min (n : ENNReal) (αlogN M x) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, min (n : ENNReal) (βlogN M y) ∂MeasureTheory.volume) ^ (1 - θ) := by
  dsimp
  intro M n
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
  let αlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc αlog L
  let βlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc βlog L
  let γlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc γlog L
  let α : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < αlogN M x}
  let β : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < βlogN M y}
  let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < γlogN M z}
  have hA_measurable : Measurable A := by
    -- Antitone real profiles are measurable.
    simpa using (Antitone.measurable hA_antitone)
  have hB_measurable : Measurable B := by
    -- The same monotonicity-to-measurability argument applies to `B`.
    simpa using (Antitone.measurable hB_antitone)
  have hC_measurable : Measurable C := by
    -- And likewise for the target profile `C`.
    simpa using (Antitone.measurable hC_antitone)
  have hαlog_measurable : Measurable αlog := by
    -- The logarithmic transport is measurable because both `exp` and `A` are measurable.
    simpa [αlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hA_measurable.comp Real.measurable_exp))
  have hβlog_measurable : Measurable βlog := by
    -- The same change-of-variables measurability statement holds for `βlog`.
    simpa [βlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hB_measurable.comp Real.measurable_exp))
  have hγlog_measurable : Measurable γlog := by
    -- And likewise for `γlog`.
    simpa [γlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hC_measurable.comp Real.measurable_exp))
  have hαlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → αlogN M x = 0 := by
    intro x hx
    -- Outside `[-M, M]`, the truncation of `αlog` vanishes by construction.
    simpa [αlogN] using (supportTrunc_eq_zero_of_not_mem (f := αlog) (N := M) (x := x) hx)
  have hβlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → βlogN M x = 0 := by
    intro x hx
    -- The same support cutoff description holds for `βlog`.
    simpa [βlogN] using (supportTrunc_eq_zero_of_not_mem (f := βlog) (N := M) (x := x) hx)
  have hγlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → γlogN M x = 0 := by
    intro x hx
    -- And likewise for `γlog`.
    simpa [γlogN] using (supportTrunc_eq_zero_of_not_mem (f := γlog) (N := M) (x := x) hx)
  have hα_bound :
      ∀ x : ℝ, αlogN M x ≤ ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) := by
    -- The transported `A`-profile is uniformly bounded on the truncation window.
    simpa [αlogN, αlog] using supportTrunc_log_profile_bound hA_antitone M
  have hβ_bound :
      ∀ y : ℝ, βlogN M y ≤ ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) := by
    -- The same uniform bound holds for the transported `B`-profile.
    simpa [βlogN, βlog] using supportTrunc_log_profile_bound hB_antitone M
  have hα_cap_lt_top :
      ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) < ⊤ := by
    -- The explicit `A`-bound is finite because `A` is finite on positive radii.
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hA_lt_top (Real.exp_pos _))
  have hβ_cap_lt_top :
      ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) < ⊤ := by
    -- The same finiteness statement holds for the explicit `B`-bound.
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hB_lt_top (Real.exp_pos _))
  have hlog_kernel :
      ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
    intro x y
    -- The multiplicative profile kernel becomes additive after the logarithmic transport.
    simpa [αlog, βlog, γlog] using
      (log_profile_kernel_transport (α := A) (β := B) (γ := C) hθ_mem hkernel x y)
  have hlog_trunc_kernel :
      ∀ x y,
        γlogN M (θ * x + (1 - θ) * y) ≥
          αlogN M x ^ θ * βlogN M y ^ (1 - θ) := by
    intro x y
    by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
    · by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
      · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(M : ℝ)) M := by
          rcases hx with ⟨hx_left, hx_right⟩
          rcases hy with ⟨hy_left, hy_right⟩
          -- The affine combination of two points in `[-M, M]` stays in `[-M, M]`.
          constructor <;>
            nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
        -- On the common truncation interval, the support cutoffs disappear.
        simpa [αlogN, βlogN, γlogN, supportTrunc, hx, hy, hz] using hlog_kernel x y
      · have hy_zero : βlogN M y = 0 := by
          simp [βlogN, supportTrunc, hy]
        -- If `y` lies outside the truncation window, the right-hand side already vanishes.
        rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hx_zero : αlogN M x = 0 := by
        simp [αlogN, supportTrunc, hx]
      -- Symmetrically when `x` leaves the truncation window.
      rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  have hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    -- The strict-superlevel profiles of the fixed support-truncated log triple satisfy the same
    -- multiplicative kernel.
    simpa [α, β, γ] using
      (compactSupport_strictSuperlevelProfile_kernel
        (a := αlogN M) (b := βlogN M) (c := γlogN M)
        hθ_mem (supportTrunc_measurable hαlog_measurable M)
        (supportTrunc_measurable hβlog_measurable M)
        (supportTrunc_measurable hγlog_measurable M)
        M hαlogN_support hβlogN_support hγlogN_support hlog_trunc_kernel)
  -- Route correction: the later bridge theorems are downstream of this declaration. The remaining
  -- work is the standalone interval-cutoff profile argument for the strict-superlevel profiles of
  -- `αlogN M`, `βlogN M`, and `γlogN M`.
  by_cases hn : n = 0
  · -- At cutoff `n = 0`, all three value-truncated integrals vanish immediately.
    subst hn
    simp [ENNReal.zero_rpow_of_pos hθ_mem.1, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2)]
  · have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
    have hα_antitone : Antitone α := by
      -- Strict-superlevel volume profiles are antitone in the threshold parameter.
      simpa [α] using strictSuperlevelProfile_antitone (αlogN M)
    have hβ_antitone : Antitone β := by
      -- The same monotonicity statement holds for `β`.
      simpa [β] using strictSuperlevelProfile_antitone (βlogN M)
    have hγ_antitone : Antitone γ := by
      -- And likewise for `γ`.
      simpa [γ] using strictSuperlevelProfile_antitone (γlogN M)
    have hα_measurable : Measurable α := by
      -- Antitone real profiles are measurable.
      simpa using (Antitone.measurable hα_antitone)
    have hβ_measurable : Measurable β := by
      -- The same monotonicity-to-measurability argument applies to `β`.
      simpa using (Antitone.measurable hβ_antitone)
    have hγ_measurable : Measurable γ := by
      -- And likewise for the target profile `γ`.
      simpa using (Antitone.measurable hγ_antitone)
    have hα_trunc :
        ∫⁻ x, min (n : ENNReal) (αlogN M x) ∂MeasureTheory.volume =
          ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) n) α s ∂MeasureTheory.volume := by
      -- Rewrite the value-truncated `αlogN M` integral as its strict-superlevel profile on
      -- `(0,n)`.
      simpa [α] using
        ennreal_lintegral_trunc_eq_profile_trunc (supportTrunc_measurable hαlog_measurable M) n
    have hβ_trunc :
        ∫⁻ y, min (n : ENNReal) (βlogN M y) ∂MeasureTheory.volume =
          ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) n) β t ∂MeasureTheory.volume := by
      -- The same truncated layer-cake identity applies to `βlogN M`.
      simpa [β] using
        ennreal_lintegral_trunc_eq_profile_trunc (supportTrunc_measurable hβlog_measurable M) n
    have hγ_trunc :
        ∫⁻ z, min (n : ENNReal) (γlogN M z) ∂MeasureTheory.volume =
          ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n) γ r ∂MeasureTheory.volume := by
      -- And likewise for `γlogN M`.
      simpa [γ] using
        ennreal_lintegral_trunc_eq_profile_trunc (supportTrunc_measurable hγlog_measurable M) n
    let αcap : ℝ := (ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ)))).toReal
    let βcap : ℝ := (ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ)))).toReal
    have hαcap_eq : ENNReal.ofReal αcap =
        ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) := by
      change ENNReal.ofReal
          ((ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ)))).toReal) =
        ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ)))
      exact ENNReal.ofReal_toReal hα_cap_lt_top.ne
    have hβcap_eq : ENNReal.ofReal βcap =
        ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) := by
      change ENNReal.ofReal
          ((ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ)))).toReal) =
        ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ)))
      exact ENNReal.ofReal_toReal hβ_cap_lt_top.ne
    have hα_zero_above :
        ∀ ⦃s : ℝ⦄, αcap ≤ s → α s = 0 := by
      intro s hs
      -- The `α`-profile vanishes once the threshold reaches the explicit finite cap.
      have hzero :=
        strictSuperlevelProfile_eq_zero_of_pointwise_bound
          (f := αlogN M)
          (R := αcap)
          (s := s)
          (fun x => by
            rw [hαcap_eq]
            exact hα_bound x)
          hs
      simpa [α] using hzero
    have hβ_zero_above :
        ∀ ⦃t : ℝ⦄, βcap ≤ t → β t = 0 := by
      intro t ht
      -- The same explicit cap kills the `β`-profile above its threshold.
      have hzero :=
        strictSuperlevelProfile_eq_zero_of_pointwise_bound
          (f := βlogN M)
          (R := βcap)
          (s := t)
          (fun y => by
            rw [hβcap_eq]
            exact hβ_bound y)
          ht
      simpa [β] using hzero
    have hprofile :
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n) γ r ∂MeasureTheory.volume ≥
          (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) n) α s ∂MeasureTheory.volume) ^ θ *
            (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) n) β t ∂MeasureTheory.volume) ^ (1 - θ) := by
      let αn : ℝ → ENNReal := Set.indicator (Set.Ioo (0 : ℝ) n) α
      let βn : ℝ → ENNReal := Set.indicator (Set.Ioo (0 : ℝ) n) β
      let γn : ℝ → ENNReal := Set.indicator (Set.Ioo (0 : ℝ) n) γ
      have hαn_measurable : Measurable αn := by
        -- The interval-cutoff `α`-profile stays measurable after the indicator restriction.
        simpa [αn] using hα_measurable.indicator measurableSet_Ioo
      have hβn_measurable : Measurable βn := by
        -- The same interval cutoff preserves measurability for `β`.
        simpa [βn] using hβ_measurable.indicator measurableSet_Ioo
      have hγn_measurable : Measurable γn := by
        -- And likewise for the target profile `γ`.
        simpa [γn] using hγ_measurable.indicator measurableSet_Ioo
      have hIoo_inter_Ioi :
          Set.Ioo (0 : ℝ) n ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) n := by
        -- The interval `(0,n)` already lies in the positive half-line because `n > 0`.
        ext s
        constructor
        · intro hs
          exact hs.1
        · intro hs
          exact ⟨hs, hs.1⟩
      have hkernel_interval :
          ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
            αn s ^ θ * βn t ^ (1 - θ) ≤ γn (s ^ θ * t ^ (1 - θ)) := by
        intro s t hs ht
        by_cases hs_mem : s ∈ Set.Ioo (0 : ℝ) n
        · by_cases ht_mem : t ∈ Set.Ioo (0 : ℝ) n
          · have hgeom :
                s ^ θ * t ^ (1 - θ) ≤ θ * s + (1 - θ) * t := by
              -- Weighted AM-GM controls the multiplicative interpolation by the affine one.
              exact Real.geom_mean_le_arith_mean2_weighted
                hθ_mem.1.le (sub_nonneg.mpr hθ_mem.2.le) hs.le ht.le (by ring)
            have hsum_lt : θ * s + (1 - θ) * t < n := by
              -- The affine interpolation stays strictly below `n` because both inputs do.
              nlinarith [hθ_mem.1, hθ_mem.2, hs_mem.2, ht_mem.2]
            have hst_mem : s ^ θ * t ^ (1 - θ) ∈ Set.Ioo (0 : ℝ) n := by
              constructor
              · -- Positive inputs keep the weighted geometric mean positive.
                positivity
              · exact lt_of_le_of_lt hgeom hsum_lt
            -- On the interval `(0,n)`, the cutoff indicators are transparent.
            simpa [αn, βn, γn, hs_mem, ht_mem, hst_mem] using hkernel_profile hs ht
          · have hβn_zero : βn t = 0 := by
              simp [βn, ht_mem]
            -- If `t` leaves the cutoff interval, the right-hand side already vanishes.
            rw [hβn_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
            exact bot_le
        · have hαn_zero : αn s = 0 := by
            simp [αn, hs_mem]
          -- Symmetrically when `s` leaves the cutoff interval.
          rw [hαn_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
          exact bot_le
      let αnlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * αn (Real.exp x)
      let βnlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * βn (Real.exp y)
      let γnlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γn (Real.exp z)
      have hαnlog_lintegral :
          ∫⁻ x, αnlog x ∂MeasureTheory.volume =
            ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) n) α s ∂MeasureTheory.volume := by
        -- The interval-cutoff `α`-profile is exactly the log transport of `αn`.
        calc
          ∫⁻ x, αnlog x ∂MeasureTheory.volume =
              ∫⁻ s in Set.Ioi 0, αn s ∂MeasureTheory.volume := by
                simpa [αnlog] using (log_profile_lintegral_eq (phi := αn)).symm
          _ = ∫⁻ s, αn s ∂MeasureTheory.volume := by
                simpa [αn, MeasureTheory.lintegral_indicator, hIoo_inter_Ioi]
          _ = ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) n) α s ∂MeasureTheory.volume := by
                rfl
      have hβnlog_lintegral :
          ∫⁻ y, βnlog y ∂MeasureTheory.volume =
            ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) n) β t ∂MeasureTheory.volume := by
        -- The same logarithmic change of variables applies to `βn`.
        calc
          ∫⁻ y, βnlog y ∂MeasureTheory.volume =
              ∫⁻ t in Set.Ioi 0, βn t ∂MeasureTheory.volume := by
                simpa [βnlog] using (log_profile_lintegral_eq (phi := βn)).symm
          _ = ∫⁻ t, βn t ∂MeasureTheory.volume := by
                simpa [βn, MeasureTheory.lintegral_indicator, hIoo_inter_Ioi]
          _ = ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) n) β t ∂MeasureTheory.volume := by
                rfl
      have hγnlog_lintegral :
          ∫⁻ z, γnlog z ∂MeasureTheory.volume =
            ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n) γ r ∂MeasureTheory.volume := by
        -- And likewise for the target interval-cutoff profile `γn`.
        calc
          ∫⁻ z, γnlog z ∂MeasureTheory.volume =
              ∫⁻ r in Set.Ioi 0, γn r ∂MeasureTheory.volume := by
                simpa [γnlog] using (log_profile_lintegral_eq (phi := γn)).symm
          _ = ∫⁻ r, γn r ∂MeasureTheory.volume := by
                simpa [γn, MeasureTheory.lintegral_indicator, hIoo_inter_Ioi]
          _ = ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n) γ r ∂MeasureTheory.volume := by
                rfl
      let αnlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc αnlog L
      let βnlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc βnlog L
      let γnlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc γnlog L
      have hαnlog_measurable : Measurable αnlog := by
        -- The logarithmic transport is measurable because both `exp` and `αn` are measurable.
        simpa [αnlog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hαn_measurable.comp Real.measurable_exp))
      have hβnlog_measurable : Measurable βnlog := by
        -- The same change-of-variables measurability statement holds for `βnlog`.
        simpa [βnlog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hβn_measurable.comp Real.measurable_exp))
      have hγnlog_measurable : Measurable γnlog := by
        -- And again for `γnlog`.
        simpa [γnlog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hγn_measurable.comp Real.measurable_exp))
      have hαnlogN_measurable : ∀ L, Measurable (αnlogN L) := by
        intro L
        -- Compact support truncation preserves measurability for the transported `αn`-profile.
        simpa [αnlogN] using supportTrunc_measurable hαnlog_measurable L
      have hβnlogN_measurable : ∀ L, Measurable (βnlogN L) := by
        intro L
        -- The same support truncation argument applies to `βnlog`.
        simpa [βnlogN] using supportTrunc_measurable hβnlog_measurable L
      have hγnlogN_measurable : ∀ L, Measurable (γnlogN L) := by
        intro L
        -- And likewise for `γnlog`.
        simpa [γnlogN] using supportTrunc_measurable hγnlog_measurable L
      have hαnlogN_mono : Monotone αnlogN := by
        intro L L' hLL' x
        -- Enlarging the compact truncation interval only increases the truncated `αnlog` profile.
        simpa [αnlogN] using supportTrunc_mono (f := αnlog) hLL' x
      have hβnlogN_mono : Monotone βnlogN := by
        intro L L' hLL' y
        -- The same pointwise monotonicity holds for the `βnlog` truncations.
        simpa [βnlogN] using supportTrunc_mono (f := βnlog) hLL' y
      have hγnlogN_mono : Monotone γnlogN := by
        intro L L' hLL' z
        -- And again for the target `γnlog` truncations.
        simpa [γnlogN] using supportTrunc_mono (f := γnlog) hLL' z
      have hlog_kernel :
          ∀ x y : ℝ, γnlog (θ * x + (1 - θ) * y) ≥ αnlog x ^ θ * βnlog y ^ (1 - θ) := by
        intro x y
        -- The multiplicative interval-cutoff kernel becomes additive after the logarithmic
        -- transport.
        simpa [αnlog, βnlog, γnlog] using
          (log_profile_kernel_transport
            (α := αn) (β := βn) (γ := γn) hθ_mem hkernel_interval x y)
      have hlog_trunc_kernel :
          ∀ L x y,
            γnlogN L (θ * x + (1 - θ) * y) ≥
              αnlogN L x ^ θ * βnlogN L y ^ (1 - θ) := by
        intro L x y
        by_cases hx : x ∈ Set.Icc (-(L : ℝ)) L
        · by_cases hy : y ∈ Set.Icc (-(L : ℝ)) L
          · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(L : ℝ)) L := by
              rcases hx with ⟨hx_left, hx_right⟩
              rcases hy with ⟨hy_left, hy_right⟩
              -- Affine combinations preserve the common compact truncation interval.
              constructor <;>
                nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
            -- On the common truncation interval, the support cutoffs disappear.
            simpa [αnlogN, βnlogN, γnlogN, supportTrunc, hx, hy, hz] using hlog_kernel x y
          · have hy_zero : βnlogN L y = 0 := by
              simp [βnlogN, supportTrunc, hy]
            -- If `y` leaves the truncation window, the right-hand side already vanishes.
            rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
            exact bot_le
        · have hx_zero : αnlogN L x = 0 := by
            simp [αnlogN, supportTrunc, hx]
          -- Symmetrically when `x` leaves the truncation window.
          rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
          exact bot_le
      have htrunc :
          ∀ L : ℕ,
            ∫⁻ z, γnlogN L z ∂MeasureTheory.volume ≥
              (∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) := by
        intro L
        have hαnlogN_supportL :
            ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(L : ℝ)) L → αnlogN L x = 0 := by
          intro x hx
          -- Outside `[-L, L]`, the support truncation of `αnlog` vanishes.
          simpa [αnlogN] using
            (supportTrunc_eq_zero_of_not_mem (f := αnlog) (N := L) (x := x) hx)
        have hβnlogN_supportL :
            ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(L : ℝ)) L → βnlogN L x = 0 := by
          intro x hx
          -- The same support cutoff description holds for `βnlog`.
          simpa [βnlogN] using
            (supportTrunc_eq_zero_of_not_mem (f := βnlog) (N := L) (x := x) hx)
        have hγnlogN_supportL :
            ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(L : ℝ)) L → γnlogN L x = 0 := by
          intro x hx
          -- And likewise for `γnlog`.
          simpa [γnlogN] using
            (supportTrunc_eq_zero_of_not_mem (f := γnlog) (N := L) (x := x) hx)
        -- Route correction: the original local blocker is now reduced to the standalone
        -- compact-support full-integral theorem for the fixed-radius log truncations.
        simpa [αnlog, βnlog, γnlog, αnlogN, βnlogN, γnlogN] using
          (positive_profile_core_compact_support_direct_pretarget
            (f := αnlogN L) (g := βnlogN L) (h := γnlogN L)
            hθ_mem (supportTrunc_measurable hαnlog_measurable L)
            (supportTrunc_measurable hβnlog_measurable L)
            (supportTrunc_measurable hγnlog_measurable L)
            L hαnlogN_supportL hβnlogN_supportL hγnlogN_supportL
            (hlog_trunc_kernel L))
      have hαnlog_lintegral_full :
          ∫⁻ x, αnlog x ∂MeasureTheory.volume =
            ⨆ L, ∫⁻ x, αnlogN L x ∂MeasureTheory.volume := by
        -- Monotone convergence sends the compact log truncations back to the full `αnlog`
        -- integral.
        calc
          ∫⁻ x, αnlog x ∂MeasureTheory.volume =
              ∫⁻ x, ⨆ L, αnlogN L x ∂MeasureTheory.volume := by
                congr with x
                simpa [αnlogN] using (iSup_supportTrunc_apply αnlog x).symm
          _ = ⨆ L, ∫⁻ x, αnlogN L x ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup hαnlogN_measurable hαnlogN_mono
      have hβnlog_lintegral_full :
          ∫⁻ y, βnlog y ∂MeasureTheory.volume =
            ⨆ L, ∫⁻ y, βnlogN L y ∂MeasureTheory.volume := by
        -- The same monotone-convergence rewrite applies to `βnlog`.
        calc
          ∫⁻ y, βnlog y ∂MeasureTheory.volume =
              ∫⁻ y, ⨆ L, βnlogN L y ∂MeasureTheory.volume := by
                congr with y
                simpa [βnlogN] using (iSup_supportTrunc_apply βnlog y).symm
          _ = ⨆ L, ∫⁻ y, βnlogN L y ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup hβnlogN_measurable hβnlogN_mono
      have hγnlog_lintegral_full :
          ∫⁻ z, γnlog z ∂MeasureTheory.volume =
            ⨆ L, ∫⁻ z, γnlogN L z ∂MeasureTheory.volume := by
        -- And likewise for the target `γnlog`.
        calc
          ∫⁻ z, γnlog z ∂MeasureTheory.volume =
              ∫⁻ z, ⨆ L, γnlogN L z ∂MeasureTheory.volume := by
                congr with z
                simpa [γnlogN] using (iSup_supportTrunc_apply γnlog z).symm
          _ = ⨆ L, ∫⁻ z, γnlogN L z ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup hγnlogN_measurable hγnlogN_mono
      have hαnlog_int_mono :
          Monotone (fun L => ∫⁻ x, αnlogN L x ∂MeasureTheory.volume) := by
        intro L L' hLL'
        -- Integral monotonicity follows from pointwise monotonicity of the truncations.
        exact MeasureTheory.lintegral_mono (fun x => hαnlogN_mono hLL' x)
      have hβnlog_int_mono :
          Monotone (fun L => ∫⁻ y, βnlogN L y ∂MeasureTheory.volume) := by
        intro L L' hLL'
        -- The same integral monotonicity statement holds for `βnlog`.
        exact MeasureTheory.lintegral_mono (fun y => hβnlogN_mono hLL' y)
      have hlog_diag_sup :
          (⨆ L, ∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
              (⨆ L, ∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) ≤
            ⨆ L,
              (∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) := by
        -- A single large truncation index dominates any pair of compact log truncations.
        have hA_rpow :
            (⨆ L, ∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ =
              ⨆ L, (∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ :=
          (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
        have hB_rpow :
            (⨆ L, ∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) =
              ⨆ L, (∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) :=
          (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
        rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
        refine iSup_le ?_
        intro m
        rw [ENNReal.mul_iSup]
        refine iSup_le ?_
        intro l
        refine le_iSup_of_le (max m l) ?_
        exact mul_le_mul'
          (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le
            (hαnlog_int_mono (Nat.le_max_left m l)))
          (ENNReal.monotone_rpow_of_nonneg
            (sub_nonneg.mpr hθ_mem.2.le) (hβnlog_int_mono (Nat.le_max_right m l)))
      have hlog_sup_le :
          (⨆ L,
            (∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
            ⨆ L, ∫⁻ z, γnlogN L z ∂MeasureTheory.volume := by
        refine iSup_le ?_
        intro L
        exact le_iSup_of_le L (htrunc L)
      -- Route correction: once the fixed-radius compact-support theorem is isolated, the rest is
      -- the standard monotone-convergence passage back to the original interval-cutoff profiles.
      calc
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n) γ r ∂MeasureTheory.volume =
            ∫⁻ z, γnlog z ∂MeasureTheory.volume := by
              rw [hγnlog_lintegral]
        _ = ⨆ L, ∫⁻ z, γnlogN L z ∂MeasureTheory.volume := hγnlog_lintegral_full
        _ ≥
            ⨆ L,
              (∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_sup_le
        _ ≥
            (⨆ L, ∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
              (⨆ L, ∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_diag_sup
        _ =
            (∫⁻ x, αnlog x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βnlog y ∂MeasureTheory.volume) ^ (1 - θ) := by
                rw [hαnlog_lintegral_full, hβnlog_lintegral_full]
        _ =
            (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) n) α s ∂MeasureTheory.volume) ^ θ *
              (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) n) β t ∂MeasureTheory.volume) ^ (1 - θ) := by
                rw [hαnlog_lintegral, hβnlog_lintegral]
    -- Rewrite the bounded-value goal back to the three truncated layer-cake integrals.
    rw [hγ_trunc, hα_trunc, hβ_trunc]
    exact hprofile

/-- Removing the finite value cutoff from the fixed support-truncated logarithmic transports. -/
private lemma fixedSupportPositiveHalflineProfileCore_logTruncStep
    {A B C : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_antitone : Antitone A)
    (hB_antitone : Antitone B)
    (hC_antitone : Antitone C)
    (hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤)
    (hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤)
    (hkernel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
    let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
    let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
    let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
    ∀ M : ℕ,
      ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
        (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
  dsimp
  intro M
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
  let αlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc αlog L
  let βlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc βlog L
  let γlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc γlog L
  have hA_measurable : Measurable A := by
    -- Antitone real profiles are measurable.
    simpa using (Antitone.measurable hA_antitone)
  have hB_measurable : Measurable B := by
    -- The same monotonicity-to-measurability argument applies to `B`.
    simpa using (Antitone.measurable hB_antitone)
  have hC_measurable : Measurable C := by
    -- And likewise for the target profile `C`.
    simpa using (Antitone.measurable hC_antitone)
  have hαlog_measurable : Measurable αlog := by
    -- The logarithmic transport is measurable because both `exp` and `A` are measurable.
    simpa [αlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hA_measurable.comp Real.measurable_exp))
  have hβlog_measurable : Measurable βlog := by
    -- The same change-of-variables measurability statement holds for `βlog`.
    simpa [βlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hB_measurable.comp Real.measurable_exp))
  have hγlog_measurable : Measurable γlog := by
    -- And likewise for `γlog`.
    simpa [γlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hC_measurable.comp Real.measurable_exp))
  have htrunc :
      ∀ n : ℕ,
        ∫⁻ z, min (n : ENNReal) (γlogN M z) ∂MeasureTheory.volume ≥
          (∫⁻ x, min (n : ENNReal) (αlogN M x) ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, min (n : ENNReal) (βlogN M y) ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- Route correction: the fixed-`M` step now comes from the direct bounded-value bridge above,
    -- so the only remaining passage is monotone convergence in the value cutoff.
    simpa [αlog, βlog, γlog, αlogN, βlogN, γlogN] using
      (fixedSupportPositiveHalflineProfileCore_logTruncBounded
        (A := A) (B := B) (C := C)
        hθ_mem hA_antitone hB_antitone hC_antitone hA_lt_top hB_lt_top hkernel M)
  -- Once the bounded-value estimates hold for every finite cutoff, remove the cutoff by monotone
  -- convergence.
  exact prekopaLeindler_from_value_truncations hθ_mem
    (supportTrunc_measurable hαlog_measurable M)
    (supportTrunc_measurable hβlog_measurable M)
    (supportTrunc_measurable hγlog_measurable M)
    htrunc

/-- The positive-half-line integral inequality follows from fixed support truncations and the
standard monotone-convergence limit. -/
private lemma fixedSupportPositiveHalflineProfileCore
    {A B C : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (_hA_antitone : Antitone A)
    (_hB_antitone : Antitone B)
    (_hC_antitone : Antitone C)
    (hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤)
    (hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤)
    (hkernel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ))) :
    ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume ≥
      (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
        (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := by
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
  let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
  let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
  let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
  have hA_measurable : Measurable A := by
    -- Antitone real profiles are measurable.
    simpa using (Antitone.measurable _hA_antitone)
  have hB_measurable : Measurable B := by
    -- The same monotonicity-to-measurability argument applies to `B`.
    simpa using (Antitone.measurable _hB_antitone)
  have hC_measurable : Measurable C := by
    -- And likewise for the target profile `C`.
    simpa using (Antitone.measurable _hC_antitone)
  have hα_log :
      ∫⁻ x, αlog x ∂MeasureTheory.volume =
        ∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume := by
    -- The `A`-profile over `Set.Ioi 0` is exactly the full-line integral of its log transport.
    simpa [αlog] using (log_profile_lintegral_eq (phi := A)).symm
  have hβ_log :
      ∫⁻ y, βlog y ∂MeasureTheory.volume =
        ∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume := by
    -- The same logarithmic change of variables applies to `B`.
    simpa [βlog] using (log_profile_lintegral_eq (phi := B)).symm
  have hγ_log :
      ∫⁻ z, γlog z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume := by
    -- And likewise for the target profile `C`.
    simpa [γlog] using (log_profile_lintegral_eq (phi := C)).symm
  have hαlog_measurable : Measurable αlog := by
    -- The logarithmic transport is measurable because both `exp` and `A` are measurable.
    simpa [αlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hA_measurable.comp Real.measurable_exp))
  have hβlog_measurable : Measurable βlog := by
    -- The same change-of-variables measurability statement holds for `βlog`.
    simpa [βlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hB_measurable.comp Real.measurable_exp))
  have hγlog_measurable : Measurable γlog := by
    -- And likewise for `γlog`.
    simpa [γlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hC_measurable.comp Real.measurable_exp))
  have hαlogN_measurable : ∀ M, Measurable (αlogN M) := by
    intro M
    -- Compact support truncation preserves measurability for the transported `A`-profile.
    simpa [αlogN] using supportTrunc_measurable hαlog_measurable M
  have hβlogN_measurable : ∀ M, Measurable (βlogN M) := by
    intro M
    -- The same support truncation argument applies to `βlog`.
    simpa [βlogN] using supportTrunc_measurable hβlog_measurable M
  have hγlogN_measurable : ∀ M, Measurable (γlogN M) := by
    intro M
    -- And likewise for `γlog`.
    simpa [γlogN] using supportTrunc_measurable hγlog_measurable M
  have hαlogN_mono : Monotone αlogN := by
    intro M L hML x
    -- Enlarging the compact truncation interval only increases the truncated `αlog` profile.
    simpa [αlogN] using supportTrunc_mono (f := αlog) hML x
  have hβlogN_mono : Monotone βlogN := by
    intro M L hML y
    -- The same pointwise monotonicity holds for the `βlog` truncations.
    simpa [βlogN] using supportTrunc_mono (f := βlog) hML y
  have hγlogN_mono : Monotone γlogN := by
    intro M L hML z
    -- And likewise for the target `γlog` truncations.
    simpa [γlogN] using supportTrunc_mono (f := γlog) hML z
  have htrunc :
      ∀ M : ℕ,
        ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
          (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- Route correction: the proof now factors through the direct fixed-`M` bounded-value bridge,
    -- not through the later interval-profile wrapper chain.
    simpa [αlog, βlog, γlog, αlogN, βlogN, γlogN] using
      (fixedSupportPositiveHalflineProfileCore_logTruncStep
        (A := A) (B := B) (C := C)
        hθ_mem _hA_antitone _hB_antitone _hC_antitone hA_lt_top hB_lt_top hkernel)
  have hαlog_lintegral :
      ∫⁻ x, αlog x ∂MeasureTheory.volume =
        ⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume := by
    -- Monotone convergence sends the compact log truncations back to the full `αlog` integral.
    calc
      ∫⁻ x, αlog x ∂MeasureTheory.volume =
          ∫⁻ x, ⨆ M, αlogN M x ∂MeasureTheory.volume := by
            congr with x
            simpa [αlogN] using (iSup_supportTrunc_apply αlog x).symm
      _ = ⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume :=
          MeasureTheory.lintegral_iSup hαlogN_measurable hαlogN_mono
  have hβlog_lintegral :
      ∫⁻ y, βlog y ∂MeasureTheory.volume =
        ⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume := by
    -- The same monotone-convergence rewrite applies to `βlog`.
    calc
      ∫⁻ y, βlog y ∂MeasureTheory.volume =
          ∫⁻ y, ⨆ M, βlogN M y ∂MeasureTheory.volume := by
            congr with y
            simpa [βlogN] using (iSup_supportTrunc_apply βlog y).symm
      _ = ⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume :=
          MeasureTheory.lintegral_iSup hβlogN_measurable hβlogN_mono
  have hγlog_lintegral :
      ∫⁻ z, γlog z ∂MeasureTheory.volume =
        ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := by
    -- And likewise for the target `γlog`.
    calc
      ∫⁻ z, γlog z ∂MeasureTheory.volume =
          ∫⁻ z, ⨆ M, γlogN M z ∂MeasureTheory.volume := by
            congr with z
            simpa [γlogN] using (iSup_supportTrunc_apply γlog z).symm
      _ = ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume :=
          MeasureTheory.lintegral_iSup hγlogN_measurable hγlogN_mono
  have hαlog_int_mono :
      Monotone (fun M => ∫⁻ x, αlogN M x ∂MeasureTheory.volume) := by
    intro M L hML
    -- Integral monotonicity follows from pointwise monotonicity of the truncations.
    exact MeasureTheory.lintegral_mono (fun x => hαlogN_mono hML x)
  have hβlog_int_mono :
      Monotone (fun M => ∫⁻ y, βlogN M y ∂MeasureTheory.volume) := by
    intro M L hML
    -- The same integral monotonicity statement holds for `βlog`.
    exact MeasureTheory.lintegral_mono (fun y => hβlogN_mono hML y)
  have hlog_diag_sup :
      (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) ≤
        ⨆ M,
          (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- A single large truncation index dominates any pair of compact log truncations.
    have hA_rpow :
        (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ =
          ⨆ M, (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ :=
      (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
    have hB_rpow :
        (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) =
          ⨆ M, (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) :=
      (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
    rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
    refine iSup_le ?_
    intro m
    rw [ENNReal.mul_iSup]
    refine iSup_le ?_
    intro l
    refine le_iSup_of_le (max m l) ?_
    exact mul_le_mul'
      (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le
        (hαlog_int_mono (Nat.le_max_left m l)))
      (ENNReal.monotone_rpow_of_nonneg
        (sub_nonneg.mpr hθ_mem.2.le) (hβlog_int_mono (Nat.le_max_right m l)))
  have hlog_sup_le :
      (⨆ M,
        (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
        ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := by
    refine iSup_le ?_
    intro M
    exact le_iSup_of_le M (htrunc M)
  -- Route correction: after the fixed-radius theorem is proved, the half-line statement is just
  -- the standard monotone-convergence passage back from compact log truncations.
  calc
    ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume =
        ∫⁻ z, γlog z ∂MeasureTheory.volume := by
          rw [← hγ_log]
    _ = ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := hγlog_lintegral
    _ ≥
        ⨆ M,
          (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_sup_le
    _ ≥
        (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_diag_sup
    _ =
        (∫⁻ x, αlog x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlog y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [hαlog_lintegral, hβlog_lintegral]
    _ =
        (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [hα_log, hβ_log]

/-- Each fixed support truncation of the cutoff-log transports satisfies the full integral
Prékopa-Leindler inequality. -/
private lemma fixedSupportCutoffLogIntegralCore
    {α β γ : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hα_measurable : Measurable α)
    (hβ_measurable : Measurable β)
    (hγ_measurable : Measurable γ)
    (hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    let αlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) αlog
    let βlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) βlog
    let γlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) γlog
    let αlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlogCut M
    let βlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlogCut M
    let γlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlogCut M
    ∀ M : ℕ,
      ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume ≥
        (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
  dsimp
  intro M
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
  let αlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) αlog
  let βlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) βlog
  let γlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) γlog
  let αlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc αlogCut N
  let βlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc βlogCut N
  let γlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc γlogCut N
  let A : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < αlogCutN M x}
  let B : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < βlogCutN M y}
  let C : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < γlogCutN M z}
  have hαlogCut_measurable : Measurable αlogCut := by
    -- The cutoff log profile is measurable because both the transport and the indicator are.
    simpa [αlogCut, αlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hα_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hβlogCut_measurable : Measurable βlogCut := by
    -- The same measurability statement holds for `βlogCut`.
    simpa [βlogCut, βlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hβ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hγlogCut_measurable : Measurable γlogCut := by
    -- And likewise for `γlogCut`.
    simpa [γlogCut, γlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hγ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hαlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → αlogCutN M x = 0 := by
    intro x hx
    -- Outside `[-M, M]`, the support truncation vanishes by construction.
    simpa [αlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := αlogCut) (N := M) (x := x) hx)
  have hβlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → βlogCutN M x = 0 := by
    intro x hx
    -- The same support description holds for `βlogCutN`.
    simpa [βlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := βlogCut) (N := M) (x := x) hx)
  have hγlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → γlogCutN M x = 0 := by
    intro x hx
    -- And likewise for `γlogCutN`.
    simpa [γlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := γlogCut) (N := M) (x := x) hx)
  have hA_antitone : Antitone A := by
    -- The strict-superlevel volume profile of `αlogCutN M` is antitone in the threshold.
    simpa [A] using strictSuperlevelProfile_antitone (αlogCutN M)
  have hB_antitone : Antitone B := by
    -- The same monotonicity statement holds for `βlogCutN M`.
    simpa [B] using strictSuperlevelProfile_antitone (βlogCutN M)
  have hC_antitone : Antitone C := by
    -- And likewise for `γlogCutN M`.
    simpa [C] using strictSuperlevelProfile_antitone (γlogCutN M)
  have hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤ := by
    intro s hs
    -- Positive strict superlevel sets stay inside the compact support interval `[-M, M]`.
    apply volume_lt_top_of_subset_supportInterval
    exact strictSuperlevel_subset_support hαlogCutN_support hs
  have hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤ := by
    intro t ht
    -- The same finite-volume reduction applies to `βlogCutN M`.
    apply volume_lt_top_of_subset_supportInterval
    exact strictSuperlevel_subset_support hβlogCutN_support ht
  have hkernel_fixed :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ)) := by
    -- Route correction: the fixed-`M` statement now factors through the compactly supported
    -- strict-superlevel profiles of the truncated cutoff-log functions.
    simpa [A, B, C] using
      (cutoffLogFixedSupportProfileKernel
        (α := α) (β := β) (γ := γ)
        hθ_mem hα_measurable hβ_measurable hγ_measurable hkernel_profile M)
  have hα_profile :
      ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume =
        ∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume := by
    -- Layer-cake rewrites the truncated cutoff-log integral as its strict-superlevel profile.
    simpa [A] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hαlogCut_measurable M) (f := αlogCutN M))
  have hβ_profile :
      ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume =
        ∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume := by
    -- The same layer-cake identity applies to `βlogCutN M`.
    simpa [B] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hβlogCut_measurable M) (f := βlogCutN M))
  have hγ_profile :
      ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume := by
    -- And likewise for `γlogCutN M`.
    simpa [C] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hγlogCut_measurable M) (f := γlogCutN M))
  have hcore :
      ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume ≥
        (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- Route correction: the main theorem no longer blocks on the outer cutoff-log transport; all
    -- remaining work is the isolated positive-half-line profile core for the fixed support
    -- truncation profiles `A`, `B`, and `C`.
    exact fixedSupportPositiveHalflineProfileCore
      hθ_mem hA_antitone hB_antitone hC_antitone hA_lt_top hB_lt_top hkernel_fixed
  calc
    ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume := hγ_profile
    _ ≥
        (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := hcore
    _ =
        (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [hα_profile, hβ_profile]

/-- The missing primitive interval-`(0, 1)` positive-profile inequality. -/
private lemma positiveProfileUnitCutoffCore
    {α β γ : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hα_antitone : Antitone α)
    (hβ_antitone : Antitone β)
    (hγ_antitone : Antitone γ)
    (hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ))) :
    ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume ≥
      (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume) ^ θ *
        (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume) ^ (1 - θ) := by
  have hα_measurable : Measurable α := by
    -- Antitone real profiles are measurable.
    simpa using (Antitone.measurable hα_antitone)
  have hβ_measurable : Measurable β := by
    -- The same monotonicity-to-measurability argument applies to `β`.
    simpa using (Antitone.measurable hβ_antitone)
  have hγ_measurable : Measurable γ := by
    -- And likewise for the target profile `γ`.
    simpa using (Antitone.measurable hγ_antitone)
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
  let αlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) αlog
  let βlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) βlog
  let γlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) γlog
  have hα_logCut :
      ∫⁻ x, αlogCut x ∂MeasureTheory.volume =
        ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume := by
    -- The interval-cutoff profile on `(0,1)` is exactly the cutoff-log transport of `α`.
    simpa [αlog, αlogCut] using cutoffLogIntervalIntegralRewrite α
  have hβ_logCut :
      ∫⁻ y, βlogCut y ∂MeasureTheory.volume =
        ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume := by
    -- The same logarithmic cutoff rewrite applies to `β`.
    simpa [βlog, βlogCut] using cutoffLogIntervalIntegralRewrite β
  have hγ_logCut :
      ∫⁻ z, γlogCut z ∂MeasureTheory.volume =
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume := by
    -- And likewise for the target profile `γ`.
    simpa [γlog, γlogCut] using cutoffLogIntervalIntegralRewrite γ
  have hαlogCut_measurable : Measurable αlogCut := by
    -- The cutoff log profile is measurable because both the transport and the indicator are.
    simpa [αlogCut, αlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hα_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hβlogCut_measurable : Measurable βlogCut := by
    -- The same measurability statement holds for `βlogCut`.
    simpa [βlogCut, βlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hβ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hγlogCut_measurable : Measurable γlogCut := by
    -- And likewise for `γlogCut`.
    simpa [γlogCut, γlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hγ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  let αlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlogCut M
  let βlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlogCut M
  let γlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlogCut M
  have hαlogCutN_measurable : ∀ M, Measurable (αlogCutN M) := by
    intro M
    -- Compact support truncation preserves measurability for the cutoff `α` log profile.
    simpa [αlogCutN] using supportTrunc_measurable hαlogCut_measurable M
  have hβlogCutN_measurable : ∀ M, Measurable (βlogCutN M) := by
    intro M
    -- The same support truncation argument applies to `βlogCut`.
    simpa [βlogCutN] using supportTrunc_measurable hβlogCut_measurable M
  have hγlogCutN_measurable : ∀ M, Measurable (γlogCutN M) := by
    intro M
    -- And likewise for `γlogCutN`.
    simpa [γlogCutN] using supportTrunc_measurable hγlogCut_measurable M
  have hαlogCutN_mono : Monotone αlogCutN := by
    intro M L hML x
    -- Enlarging the compact support interval only increases the truncated cutoff profile.
    simpa [αlogCutN] using supportTrunc_mono (f := αlogCut) hML x
  have hβlogCutN_mono : Monotone βlogCutN := by
    intro M L hML y
    -- The same pointwise monotonicity holds for the `β` cutoff truncations.
    simpa [βlogCutN] using supportTrunc_mono (f := βlogCut) hML y
  have hγlogCutN_mono : Monotone γlogCutN := by
    intro M L hML z
    -- And again for the target cutoff truncations.
    simpa [γlogCutN] using supportTrunc_mono (f := γlogCut) hML z
  have htrunc :
      ∀ M : ℕ,
        ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume ≥
          (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- Route correction: isolate the genuinely missing primitive as the fixed-support cutoff-log
    -- inequality, so the outer theorem only performs the monotone-limit passage.
    simpa [αlog, βlog, γlog, αlogCut, βlogCut, γlogCut, αlogCutN, βlogCutN, γlogCutN] using
      (fixedSupportCutoffLogIntegralCore
        (α := α) (β := β) (γ := γ)
        hθ_mem hα_measurable hβ_measurable hγ_measurable hkernel_profile)
  have hαlogCut_lintegral :
      ∫⁻ x, αlogCut x ∂MeasureTheory.volume =
        ⨆ M, ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume := by
    -- Monotone convergence sends the compact cutoff truncations back to the full `αlogCut`
    -- integral.
    simpa [αlogCutN] using cutoffLogMonotoneLimit hαlogCut_measurable
  have hβlogCut_lintegral :
      ∫⁻ y, βlogCut y ∂MeasureTheory.volume =
        ⨆ M, ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume := by
    -- The same monotone-convergence rewrite applies to `βlogCut`.
    simpa [βlogCutN] using cutoffLogMonotoneLimit hβlogCut_measurable
  have hγlogCut_lintegral :
      ∫⁻ z, γlogCut z ∂MeasureTheory.volume =
        ⨆ M, ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume := by
    -- And likewise for the target cutoff log profile.
    simpa [γlogCutN] using cutoffLogMonotoneLimit hγlogCut_measurable
  have hαlogCut_int_mono :
      Monotone (fun M => ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) := by
    intro M L hML
    -- Integral monotonicity follows from pointwise monotonicity of the truncations.
    exact MeasureTheory.lintegral_mono (fun x => hαlogCutN_mono hML x)
  have hβlogCut_int_mono :
      Monotone (fun M => ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) := by
    intro M L hML
    -- The same integral monotonicity statement holds for `βlogCut`.
    exact MeasureTheory.lintegral_mono (fun y => hβlogCutN_mono hML y)
  have hlog_diag_sup :
      (⨆ M, ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
          (⨆ M, ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) ≤
        ⨆ M,
          (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- A single large truncation index dominates any pair of compact cutoff truncations.
    have hA_rpow :
        (⨆ M, ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ =
          ⨆ M, (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ :=
      (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
    have hB_rpow :
        (⨆ M, ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) =
          ⨆ M, (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) :=
      (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
    rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
    refine iSup_le ?_
    intro m
    rw [ENNReal.mul_iSup]
    refine iSup_le ?_
    intro n
    refine le_iSup_of_le (max m n) ?_
    exact mul_le_mul'
      (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le
        (hαlogCut_int_mono (Nat.le_max_left m n)))
      (ENNReal.monotone_rpow_of_nonneg
        (sub_nonneg.mpr hθ_mem.2.le) (hβlogCut_int_mono (Nat.le_max_right m n)))
  have hlog_sup_le :
      (⨆ M,
        (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
        ⨆ M, ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume := by
    refine iSup_le ?_
    intro M
    exact le_iSup_of_le M (htrunc M)
  -- Route correction: the later recursive route through `positive_profile_value_truncation_bridge`
  -- is circular here. Once the fixed-support cutoff-log estimate is isolated as `htrunc`, the
  -- remaining argument is the deterministic monotone-convergence diagonal passage back to the full
  -- cutoff profiles.
  calc
    ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume =
        ∫⁻ z, γlogCut z ∂MeasureTheory.volume := by
          rw [← hγ_logCut]
    _ = ⨆ M, ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume := hγlogCut_lintegral
    _ ≥
        ⨆ M,
          (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_sup_le
    _ ≥
        (⨆ M, ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
          (⨆ M, ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_diag_sup
    _ =
        (∫⁻ x, αlogCut x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogCut y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [hαlogCut_lintegral, hβlogCut_lintegral]
    _ =
        (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [hα_logCut, hβ_logCut]

/-- A compactly supported bounded kernel satisfies every finite value-truncation
Prékopa-Leindler estimate. -/
private lemma compactSupport_value_truncation_bridge_unit
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (N : ℕ)
    (hf_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f x = 0)
    (hg_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g x = 0)
    (hh_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h x = 0)
    (h_kernel :
      ∀ x y : ℝ,
        h (θ * x + (1 - θ) * y) ≥ f x ^ θ * g y ^ (1 - θ)) :
    ∫⁻ z, min (1 : ENNReal) (h z) ∂MeasureTheory.volume ≥
      (∫⁻ x, min (1 : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, min (1 : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
  let α : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < f x}
  let β : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < g y}
  let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < h z}
  have hα_antitone : Antitone α := by
    -- The strict-superlevel profile of `f` is antitone in the threshold parameter.
    simpa [α] using strictSuperlevelProfile_antitone f
  have hβ_antitone : Antitone β := by
    -- The same monotonicity statement holds for `g`.
    simpa [β] using strictSuperlevelProfile_antitone g
  have hγ_antitone : Antitone γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using strictSuperlevelProfile_antitone h
  have hα_profile :
      ∫⁻ x, min (1 : ENNReal) (f x) ∂MeasureTheory.volume =
        ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume := by
    -- Rewrite the unit truncation of `f` as the strict-superlevel profile over `(0, 1)`.
    simpa [α] using ennreal_lintegral_trunc_eq_profile_trunc hf_measurable 1
  have hβ_profile :
      ∫⁻ y, min (1 : ENNReal) (g y) ∂MeasureTheory.volume =
        ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume := by
    -- The same unit-cutoff layer-cake identity holds for `g`.
    simpa [β] using ennreal_lintegral_trunc_eq_profile_trunc hg_measurable 1
  have hγ_profile :
      ∫⁻ z, min (1 : ENNReal) (h z) ∂MeasureTheory.volume =
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume := by
    -- And likewise for the target function `h`.
    simpa [γ] using ennreal_lintegral_trunc_eq_profile_trunc hh_measurable 1
  have hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t ->
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    -- Route correction: first extract the multiplicative profile kernel directly from the compact
    -- support assumptions before transporting it to cutoff-log coordinates.
    simpa [α, β, γ] using
      (compactSupport_strictSuperlevelProfile_kernel
        (a := f) (b := g) (c := h)
        hθ_mem hf_measurable hg_measurable hh_measurable N
        hf_support hg_support hh_support h_kernel)
  have hprofile :
      ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume ≥
        (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- Reduce the compact-support unit-cutoff statement to the standalone interval-profile core.
    exact positiveProfileUnitCutoffCore hθ_mem hα_antitone hβ_antitone hγ_antitone hkernel_profile
  -- Rewrite the three unit truncations to strict-superlevel profile integrals and close with the
  -- interval-profile inequality above.
  calc
    ∫⁻ z, min (1 : ENNReal) (h z) ∂MeasureTheory.volume =
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume := hγ_profile
    _ ≥
        (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume) ^ (1 - θ) :=
            hprofile
    _ =
        (∫⁻ x, min (1 : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, min (1 : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [← hα_profile, ← hβ_profile]

/-- A compactly supported bounded kernel satisfies every finite value-truncation
Prékopa-Leindler estimate. -/
private lemma compactSupport_value_truncation_bridge
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (N : ℕ)
    (hf_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f x = 0)
    (hg_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g x = 0)
    (hh_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h x = 0)
    (Rf Rg : ENNReal)
    (hRf_lt_top : Rf < ⊤)
    (hRg_lt_top : Rg < ⊤)
    (hf_bound : ∀ x : ℝ, f x ≤ Rf)
    (hg_bound : ∀ y : ℝ, g y ≤ Rg)
    (h_kernel :
      ∀ x y : ℝ,
        h (θ * x + (1 - θ) * y) ≥ f x ^ θ * g y ^ (1 - θ)) :
    ∀ n : ℕ,
      ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume ≥
        (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
  intro n
  cases n with
  | zero =>
      -- At cutoff `0`, every truncation vanishes, so the inequality is immediate.
      simp [ENNReal.zero_rpow_of_pos hθ_mem.1,
        ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2)]
  | succ m =>
      let k : ENNReal := ((Nat.succ m : ℕ) : ENNReal)
      let f1 : ℝ → ENNReal := fun x => k⁻¹ * f x
      let g1 : ℝ → ENNReal := fun y => k⁻¹ * g y
      let h1 : ℝ → ENNReal := fun z => k⁻¹ * h z
      have hk_ne_zero : k ≠ 0 := by
        dsimp [k]
        norm_num
      have hk_ne_top : k ≠ ⊤ := by
        dsimp [k]
        simp
      have hf1_measurable : Measurable f1 := by
        -- Scaling by a constant preserves measurability.
        simpa [f1] using measurable_const.mul hf_measurable
      have hg1_measurable : Measurable g1 := by
        -- The same normalization applies to `g`.
        simpa [g1] using measurable_const.mul hg_measurable
      have hh1_measurable : Measurable h1 := by
        -- And likewise for `h`.
        simpa [h1] using measurable_const.mul hh_measurable
      have hf1_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f1 x = 0 := by
        intro x hx
        -- The compact support interval is unchanged by value normalization.
        simp [f1, hf_support hx]
      have hg1_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g1 x = 0 := by
        intro x hx
        -- The same support statement holds for the normalized `g`.
        simp [g1, hg_support hx]
      have hh1_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h1 x = 0 := by
        intro x hx
        -- And likewise for the normalized target function.
        simp [h1, hh_support hx]
      have hscaled_rpow :
          ∀ x y : ℝ,
            f1 x ^ θ * g1 y ^ (1 - θ) = k⁻¹ * (f x ^ θ * g y ^ (1 - θ)) := by
        intro x y
        dsimp [f1, g1]
        have hkinv_ne_zero : k⁻¹ ≠ 0 := by
          simpa using hk_ne_top
        have hkinv_ne_top : k⁻¹ ≠ ⊤ := by
          intro htop
          exact hk_ne_zero (ENNReal.inv_eq_top.mp htop)
        -- Route correction: normalize both factors first, then recombine the powers using
        -- `θ + (1 - θ) = 1` so the common factor is exactly `k⁻¹`.
        calc
          (k⁻¹ * f x) ^ θ * (k⁻¹ * g y) ^ (1 - θ) =
              (k⁻¹ ^ θ * f x ^ θ) * (k⁻¹ ^ (1 - θ) * g y ^ (1 - θ)) := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ hθ_mem.1.le,
                  ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hθ_mem.2.le)]
          _ = (k⁻¹ ^ θ * k⁻¹ ^ (1 - θ)) * (f x ^ θ * g y ^ (1 - θ)) := by
                ac_rfl
          _ = (k⁻¹ ^ (θ + (1 - θ))) * (f x ^ θ * g y ^ (1 - θ)) := by
                rw [← ENNReal.rpow_add _ _ hkinv_ne_zero hkinv_ne_top]
          _ = k⁻¹ * (f x ^ θ * g y ^ (1 - θ)) := by
                rw [show θ + (1 - θ) = 1 by ring, ENNReal.rpow_one]
      have h1_kernel :
          ∀ x y : ℝ, h1 (θ * x + (1 - θ) * y) ≥ f1 x ^ θ * g1 y ^ (1 - θ) := by
        intro x y
        -- After normalizing the values, the affine kernel is preserved because the common factor
        -- `k⁻¹` distributes across the weighted geometric mean.
        calc
          h1 (θ * x + (1 - θ) * y) = k⁻¹ * h (θ * x + (1 - θ) * y) := by
              rfl
          _ ≥ k⁻¹ * (f x ^ θ * g y ^ (1 - θ)) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                mul_le_mul_right (h_kernel x y) k⁻¹
          _ = f1 x ^ θ * g1 y ^ (1 - θ) := by
              rw [hscaled_rpow]
      have hunit := compactSupport_value_truncation_bridge_unit
        (f := f1) (g := g1) (h := h1)
        hθ_mem hf1_measurable hg1_measurable hh1_measurable N
        hf1_support hg1_support hh1_support h1_kernel
      have hscale_integral (u : ℝ → ENNReal) :
          (∫⁻ z, min k (u z) ∂MeasureTheory.volume) =
            (∫⁻ z, min (1 : ENNReal) (k⁻¹ * u z) ∂MeasureTheory.volume) * k := by
        have hfun :
            (fun z => min k (u z)) =
              (fun z => min (1 : ENNReal) (k⁻¹ * u z) * k) := by
          funext z
          -- The truncation identity `min k u = k * min 1 (k⁻¹ * u)` is the exact rescaling
          -- needed to pass back from the normalized theorem.
          calc
            min k (u z) = min (1 * k) ((k⁻¹ * u z) * k) := by
              congr 1
              · simp
              · calc
                  u z = u z * k⁻¹ * k := by
                      rw [ENNReal.inv_mul_cancel_right hk_ne_zero hk_ne_top]
                  _ = (k⁻¹ * u z) * k := by
                      ac_rfl
            _ = min (1 : ENNReal) (k⁻¹ * u z) * k := by
                  simpa using (min_mul_mul_right (1 : ENNReal) (k⁻¹ * u z) k)
        rw [hfun]
        exact MeasureTheory.lintegral_mul_const' k
          (fun z => min (1 : ENNReal) (k⁻¹ * u z)) hk_ne_top
      have hk_pow :
          (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ))) * k =
            ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) * k) ^ θ *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := by
        -- The product-side rescaling is compatible with the exponents because `θ + (1 - θ) = 1`.
        calc
          (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ))) * k =
              ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ)) *
                  (k ^ (θ + (1 - θ))) := by
                    rw [show k ^ (θ + (1 - θ)) = k by
                      rw [show θ + (1 - θ) = 1 by ring, ENNReal.rpow_one]]
          _ = (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) * k ^ θ) *
                (((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ)) *
                  k ^ (1 - θ)) := by
                    rw [ENNReal.rpow_add _ _ hk_ne_zero hk_ne_top]
                    ac_rfl
          _ = ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) * k) ^ θ *
                ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := by
                    rw [← ENNReal.mul_rpow_of_nonneg _ _ hθ_mem.1.le,
                      ← ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hθ_mem.2.le)]
      have hh_eq := hscale_integral h
      have hf_eq := hscale_integral f
      have hg_eq := hscale_integral g
      -- Route correction: once the unit-cutoff theorem is available, undo the normalization on
      -- all three integrals to recover the original cutoff `k = n.succ`.
      calc
        (∫⁻ z, min k (h z) ∂MeasureTheory.volume) =
            (∫⁻ z, min (1 : ENNReal) (h1 z) ∂MeasureTheory.volume) * k := by
              simpa [h1] using hh_eq
        _ ≥
            (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ))) * k := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_left hunit k
        _ = ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) * k) ^ θ *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := hk_pow
        _ = ((∫⁻ x, min (1 : ENNReal) (k⁻¹ * f x) ∂MeasureTheory.volume) * k) ^ θ *
              ((∫⁻ y, min (1 : ENNReal) (k⁻¹ * g y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := by
              rfl
        _ =
            (∫⁻ x, min k (f x) ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, min k (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [← hf_eq, ← hg_eq]

/-- The bounded-value bridge for positive profiles isolates the remaining `Nat.succ` truncation
step away from the outer compact-support theorem. -/
private lemma positive_profile_value_truncation_bridge
    {A B C : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_antitone : Antitone A)
    (hB_antitone : Antitone B)
    (hC_antitone : Antitone C)
    (hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤)
    (hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤)
    (hkernel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ))) :
    let Apos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) A
    let Bpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) B
    let Cpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) C
    ∀ n : ℕ,
      ∫⁻ r, min (n : ENNReal) (Cpos r) ∂MeasureTheory.volume ≥
        (∫⁻ s, min (n : ENNReal) (Apos s) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t, min (n : ENNReal) (Bpos t) ∂MeasureTheory.volume) ^ (1 - θ) := by
  dsimp
  intro n
  cases n with
  | zero =>
      -- At value cutoff `0`, all three truncated integrals vanish.
      simp [ENNReal.zero_rpow_of_pos hθ_mem.1,
        ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2)]
  | succ m =>
      let n : ℕ := m + 1
      have hA_measurable : Measurable A := by
        -- Antitone real profiles are measurable.
        simpa using (Antitone.measurable hA_antitone)
      have hB_measurable : Measurable B := by
        -- The same monotonicity-to-measurability argument applies to `B`.
        simpa using (Antitone.measurable hB_antitone)
      have hC_measurable : Measurable C := by
        -- And likewise for `C`.
        simpa using (Antitone.measurable hC_antitone)
      let Alog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
      let Blog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
      let Clog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
      have hAlog_measurable : Measurable Alog := by
        -- The logarithmic transport is measurable because both `exp` and `A` are measurable.
        simpa [Alog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hA_measurable.comp Real.measurable_exp))
      have hBlog_measurable : Measurable Blog := by
        -- The same change-of-variables measurability statement holds for `Blog`.
        simpa [Blog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hB_measurable.comp Real.measurable_exp))
      have hClog_measurable : Measurable Clog := by
        -- And likewise for `Clog`.
        simpa [Clog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hC_measurable.comp Real.measurable_exp))
      let Apos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) A
      let Bpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) B
      let Cpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) C
      let φA : ℝ → ENNReal := fun r => min (n : ENNReal) (Apos r)
      let φB : ℝ → ENNReal := fun r => min (n : ENNReal) (Bpos r)
      let φC : ℝ → ENNReal := fun r => min (n : ENNReal) (Cpos r)
      let a : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * φA (Real.exp x)
      let b : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * φB (Real.exp y)
      let c : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * φC (Real.exp z)
      let aN : ℕ → ℝ → ENNReal := fun M => supportTrunc a M
      let bN : ℕ → ℝ → ENNReal := fun M => supportTrunc b M
      let cN : ℕ → ℝ → ENNReal := fun M => supportTrunc c M
      have hApos_measurable : Measurable Apos := by
        -- Restricting `A` to the positive half-line preserves measurability.
        simpa [Apos] using hA_measurable.indicator measurableSet_Ioi
      have hBpos_measurable : Measurable Bpos := by
        -- The same positive-half-line restriction works for `B`.
        simpa [Bpos] using hB_measurable.indicator measurableSet_Ioi
      have hCpos_measurable : Measurable Cpos := by
        -- And likewise for `C`.
        simpa [Cpos] using hC_measurable.indicator measurableSet_Ioi
      have hφA_measurable : Measurable φA := by
        -- Finite value truncation preserves measurability for the positive `A`-profile.
        simpa [φA] using measurable_const.min hApos_measurable
      have hφB_measurable : Measurable φB := by
        -- The same truncation statement holds for `B`.
        simpa [φB] using measurable_const.min hBpos_measurable
      have hφC_measurable : Measurable φC := by
        -- And likewise for `C`.
        simpa [φC] using measurable_const.min hCpos_measurable
      have hφA_zero_off :
          ∀ ⦃s : ℝ⦄, s ∉ Set.Ioi (0 : ℝ) → φA s = 0 := by
        intro s hs
        -- Outside the positive half-line, the truncated positive `A`-profile vanishes.
        simp [φA, Apos, hs]
      have hφB_zero_off :
          ∀ ⦃t : ℝ⦄, t ∉ Set.Ioi (0 : ℝ) → φB t = 0 := by
        intro t ht
        -- The same vanishing statement holds for `B`.
        simp [φB, Bpos, ht]
      have hφC_zero_off :
          ∀ ⦃r : ℝ⦄, r ∉ Set.Ioi (0 : ℝ) → φC r = 0 := by
        intro r hr
        -- And likewise for `C`.
        simp [φC, Cpos, hr]
      have hkernel_trunc :
          ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
            φA s ^ θ * φB t ^ (1 - θ) ≤ φC (s ^ θ * t ^ (1 - θ)) := by
        intro s t hs ht
        have hgeom :=
          value_truncation_geom_mean_le hθ_mem n (A s) (B t)
        have hst_pos : 0 < s ^ θ * t ^ (1 - θ) := by
          positivity
        -- Route correction: the value cutoff must be inserted before transporting the kernel to
        -- logarithmic coordinates.
        calc
          φA s ^ θ * φB t ^ (1 - θ) =
              min (n : ENNReal) (A s) ^ θ * min (n : ENNReal) (B t) ^ (1 - θ) := by
                simp [φA, φB, Apos, Bpos, hs, ht]
          _ ≤ min (n : ENNReal) (A s ^ θ * B t ^ (1 - θ)) := hgeom
          _ ≤ min (n : ENNReal) (C (s ^ θ * t ^ (1 - θ))) := by
                exact min_le_min le_rfl (hkernel hs ht)
          _ = φC (s ^ θ * t ^ (1 - θ)) := by
                simp [φC, Cpos, hst_pos]
      have ha_measurable : Measurable a := by
        -- The logarithmic transport is measurable because both `exp` and `φA` are measurable.
        simpa [a] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hφA_measurable.comp Real.measurable_exp))
      have hb_measurable : Measurable b := by
        -- The same change-of-variables measurability statement holds for `b`.
        simpa [b] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hφB_measurable.comp Real.measurable_exp))
      have hc_measurable : Measurable c := by
        -- And likewise for `c`.
        simpa [c] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hφC_measurable.comp Real.measurable_exp))
      have hA_log :
          ∫⁻ x, a x ∂MeasureTheory.volume =
            ∫⁻ s, min (n : ENNReal) (Apos s) ∂MeasureTheory.volume := by
        -- The already value-truncated positive profile is exactly the log transport of `a`.
        calc
          ∫⁻ x, a x ∂MeasureTheory.volume =
              ∫⁻ s in Set.Ioi 0, φA s ∂MeasureTheory.volume := by
                simpa [a, φA] using (log_profile_lintegral_eq (phi := φA)).symm
          _ = ∫⁻ s, Set.indicator (Set.Ioi (0 : ℝ)) φA s ∂MeasureTheory.volume := by
                simp [MeasureTheory.lintegral_indicator, measurableSet_Ioi]
          _ = ∫⁻ s, φA s ∂MeasureTheory.volume := by
                refine MeasureTheory.lintegral_congr_ae ?_
                exact Filter.Eventually.of_forall fun s => by
                  by_cases hs : s ∈ Set.Ioi (0 : ℝ)
                  · simp [Set.indicator, hs]
                  · simp [Set.indicator, hs, hφA_zero_off hs]
          _ = ∫⁻ s, min (n : ENNReal) (Apos s) ∂MeasureTheory.volume := by
                rfl
      have hB_log :
          ∫⁻ y, b y ∂MeasureTheory.volume =
            ∫⁻ t, min (n : ENNReal) (Bpos t) ∂MeasureTheory.volume := by
        -- The same logarithmic rewrite applies to the value-truncated `B`-profile.
        calc
          ∫⁻ y, b y ∂MeasureTheory.volume =
              ∫⁻ t in Set.Ioi 0, φB t ∂MeasureTheory.volume := by
                simpa [b, φB] using (log_profile_lintegral_eq (phi := φB)).symm
          _ = ∫⁻ t, Set.indicator (Set.Ioi (0 : ℝ)) φB t ∂MeasureTheory.volume := by
                simp [MeasureTheory.lintegral_indicator, measurableSet_Ioi]
          _ = ∫⁻ t, φB t ∂MeasureTheory.volume := by
                refine MeasureTheory.lintegral_congr_ae ?_
                exact Filter.Eventually.of_forall fun t => by
                  by_cases ht : t ∈ Set.Ioi (0 : ℝ)
                  · simp [Set.indicator, ht]
                  · simp [Set.indicator, ht, hφB_zero_off ht]
          _ = ∫⁻ t, min (n : ENNReal) (Bpos t) ∂MeasureTheory.volume := by
                rfl
      have hC_log :
          ∫⁻ z, c z ∂MeasureTheory.volume =
            ∫⁻ r, min (n : ENNReal) (Cpos r) ∂MeasureTheory.volume := by
        -- And likewise for the target value-truncated `C`-profile.
        calc
          ∫⁻ z, c z ∂MeasureTheory.volume =
              ∫⁻ r in Set.Ioi 0, φC r ∂MeasureTheory.volume := by
                simpa [c, φC] using (log_profile_lintegral_eq (phi := φC)).symm
          _ = ∫⁻ r, Set.indicator (Set.Ioi (0 : ℝ)) φC r ∂MeasureTheory.volume := by
                simp [MeasureTheory.lintegral_indicator, measurableSet_Ioi]
          _ = ∫⁻ r, φC r ∂MeasureTheory.volume := by
                refine MeasureTheory.lintegral_congr_ae ?_
                exact Filter.Eventually.of_forall fun r => by
                  by_cases hr : r ∈ Set.Ioi (0 : ℝ)
                  · simp [Set.indicator, hr]
                  · simp [Set.indicator, hr, hφC_zero_off hr]
          _ = ∫⁻ r, min (n : ENNReal) (Cpos r) ∂MeasureTheory.volume := by
                rfl
      have hlog_kernel :
          ∀ x y : ℝ, c (θ * x + (1 - θ) * y) ≥ a x ^ θ * b y ^ (1 - θ) := by
        intro x y
        -- The multiplicative kernel for the value-truncated profiles becomes additive after the
        -- logarithmic transport.
        simpa [a, b, c] using
          (log_profile_kernel_transport
            (α := φA) (β := φB) (γ := φC) hθ_mem hkernel_trunc x y)
      have haN_measurable : ∀ M, Measurable (aN M) := by
        intro M
        -- Compact support truncation preserves measurability for `a`.
        simpa [aN] using supportTrunc_measurable ha_measurable M
      have hbN_measurable : ∀ M, Measurable (bN M) := by
        intro M
        -- The same support truncation argument applies to `b`.
        simpa [bN] using supportTrunc_measurable hb_measurable M
      have hcN_measurable : ∀ M, Measurable (cN M) := by
        intro M
        -- And likewise for `c`.
        simpa [cN] using supportTrunc_measurable hc_measurable M
      have haN_mono : Monotone aN := by
        intro M L hML x
        -- Enlarging the support interval only increases the truncated `a`.
        simpa [aN] using supportTrunc_mono (f := a) hML x
      have hbN_mono : Monotone bN := by
        intro M L hML y
        -- The same pointwise monotonicity holds for `b`.
        simpa [bN] using supportTrunc_mono (f := b) hML y
      have hcN_mono : Monotone cN := by
        intro M L hML z
        -- And again for the target `c`.
        simpa [cN] using supportTrunc_mono (f := c) hML z
      have htrunc :
          ∀ M : ℕ,
            ∫⁻ z, cN M z ∂MeasureTheory.volume ≥
              (∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
        intro M
        have hkernel_support :
            ∀ x y : ℝ, cN M (θ * x + (1 - θ) * y) ≥ aN M x ^ θ * bN M y ^ (1 - θ) := by
          -- Route correction: isolate the fixed-radius support-truncated kernel first so the only
          -- remaining blocker is the standalone bounded-value compact-support theorem.
          simpa [aN, bN, cN] using
            (supportTrunc_affine_kernel
              (f := a) (g := b) (h := c) hθ_mem hlog_kernel M)
        have haN_support :
            ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → aN M x = 0 := by
          intro x hx
          -- Outside `[-M, M]`, the support truncation of `a` vanishes by construction.
          simpa [aN] using
            (supportTrunc_eq_zero_of_not_mem (f := a) (N := M) (x := x) hx)
        have hbN_support :
            ∀ ⦃y : ℝ⦄, y ∉ Set.Icc (-(M : ℝ)) M → bN M y = 0 := by
          intro y hy
          -- The same support cutoff description holds for `b`.
          simpa [bN] using
            (supportTrunc_eq_zero_of_not_mem (f := b) (N := M) (x := y) hy)
        have hcN_support :
            ∀ ⦃z : ℝ⦄, z ∉ Set.Icc (-(M : ℝ)) M → cN M z = 0 := by
          intro z hz
          -- And likewise for `c`.
          simpa [cN] using
            (supportTrunc_eq_zero_of_not_mem (f := c) (N := M) (x := z) hz)
        have haN_bound :
            ∀ x : ℝ,
              aN M x ≤ ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) := by
          intro x
          by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
          · rcases hx with ⟨hx_left, hx_right⟩
            have hx_mem : x ∈ Set.Icc (-(M : ℝ)) M := ⟨hx_left, hx_right⟩
            have hexp_left : Real.exp (-(M : ℝ)) ≤ Real.exp x := by
              exact Real.exp_le_exp.mpr hx_left
            have hexp_right : Real.exp x ≤ Real.exp M := by
              exact Real.exp_le_exp.mpr hx_right
            have hφA_le : φA (Real.exp x) ≤ A (Real.exp x) := by
              -- On the positive half-line, value truncation only decreases `A`.
              simp [φA, Apos, Real.exp_pos]
            have hA_le : A (Real.exp x) ≤ A (Real.exp (-(M : ℝ))) := hA_antitone hexp_left
            have hexp_le :
                ENNReal.ofReal (Real.exp x) ≤ ENNReal.ofReal (Real.exp M) :=
              ENNReal.ofReal_le_ofReal hexp_right
            -- Combine the value truncation bound with the endpoint control from antitonicity.
            calc
              aN M x = ENNReal.ofReal (Real.exp x) * φA (Real.exp x) := by
                simp [aN, a, supportTrunc, hx_mem]
              _ ≤ ENNReal.ofReal (Real.exp x) * A (Real.exp x) := by
                    exact mul_le_mul' le_rfl hφA_le
              _ ≤ ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) := by
                    exact mul_le_mul' hexp_le hA_le
          · -- Outside the support window, `aN M` already vanishes.
            simp [aN, supportTrunc, hx]
        have hbN_bound :
            ∀ y : ℝ,
              bN M y ≤ ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) := by
          intro y
          by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
          · rcases hy with ⟨hy_left, hy_right⟩
            have hy_mem : y ∈ Set.Icc (-(M : ℝ)) M := ⟨hy_left, hy_right⟩
            have hexp_left : Real.exp (-(M : ℝ)) ≤ Real.exp y := by
              exact Real.exp_le_exp.mpr hy_left
            have hexp_right : Real.exp y ≤ Real.exp M := by
              exact Real.exp_le_exp.mpr hy_right
            have hφB_le : φB (Real.exp y) ≤ B (Real.exp y) := by
              -- On the positive half-line, value truncation only decreases `B`.
              simp [φB, Bpos, Real.exp_pos]
            have hB_le : B (Real.exp y) ≤ B (Real.exp (-(M : ℝ))) := hB_antitone hexp_left
            have hexp_le :
                ENNReal.ofReal (Real.exp y) ≤ ENNReal.ofReal (Real.exp M) :=
              ENNReal.ofReal_le_ofReal hexp_right
            -- The same endpoint control bounds the transported `B`-profile on `[-M, M]`.
            calc
              bN M y = ENNReal.ofReal (Real.exp y) * φB (Real.exp y) := by
                simp [bN, b, supportTrunc, hy_mem]
              _ ≤ ENNReal.ofReal (Real.exp y) * B (Real.exp y) := by
                    exact mul_le_mul' le_rfl hφB_le
              _ ≤ ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) := by
                    exact mul_le_mul' hexp_le hB_le
          · -- Outside the support window, `bN M` already vanishes.
            simp [bN, supportTrunc, hy]
        have hA_cap_lt_top :
            ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) < ⊤ := by
          -- The explicit `A`-bound is finite because `A` is finite on positive radii.
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hA_lt_top (Real.exp_pos _))
        have hB_cap_lt_top :
            ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) < ⊤ := by
          -- The same finiteness statement holds for the explicit `B`-bound.
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hB_lt_top (Real.exp_pos _))
        have hvalue_trunc :
            ∀ n : ℕ,
              ∫⁻ z, min (n : ENNReal) (cN M z) ∂MeasureTheory.volume ≥
                (∫⁻ x, min (n : ENNReal) (aN M x) ∂MeasureTheory.volume) ^ θ *
                  (∫⁻ y, min (n : ENNReal) (bN M y) ∂MeasureTheory.volume) ^ (1 - θ) := by
          -- Route correction: the old circular route through later compact-support wrappers is
          -- replaced by the dedicated standalone bounded-value compact-support theorem.
          exact compactSupport_value_truncation_bridge
            (f := aN M) (g := bN M) (h := cN M)
            hθ_mem (haN_measurable M) (hbN_measurable M) (hcN_measurable M)
            M haN_support hbN_support hcN_support
            (ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))))
            (ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))))
            hA_cap_lt_top hB_cap_lt_top haN_bound hbN_bound hkernel_support
        -- Once every finite value truncation of `aN M`, `bN M`, and `cN M` satisfies the
        -- inequality, monotone convergence upgrades it to the full fixed-support statement.
        exact prekopaLeindler_from_value_truncations
          hθ_mem (haN_measurable M) (hbN_measurable M) (hcN_measurable M) hvalue_trunc
      have ha_lintegral :
          ∫⁻ x, a x ∂MeasureTheory.volume =
            ⨆ M, ∫⁻ x, aN M x ∂MeasureTheory.volume := by
        -- Monotone convergence sends the support truncations back to the full `a`-integral.
        calc
          ∫⁻ x, a x ∂MeasureTheory.volume =
              ∫⁻ x, ⨆ M, aN M x ∂MeasureTheory.volume := by
                congr with x
                simpa [aN] using (iSup_supportTrunc_apply a x).symm
          _ = ⨆ M, ∫⁻ x, aN M x ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup haN_measurable haN_mono
      have hb_lintegral :
          ∫⁻ y, b y ∂MeasureTheory.volume =
            ⨆ M, ∫⁻ y, bN M y ∂MeasureTheory.volume := by
        -- The same monotone-convergence rewrite applies to `b`.
        calc
          ∫⁻ y, b y ∂MeasureTheory.volume =
              ∫⁻ y, ⨆ M, bN M y ∂MeasureTheory.volume := by
                congr with y
                simpa [bN] using (iSup_supportTrunc_apply b y).symm
          _ = ⨆ M, ∫⁻ y, bN M y ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup hbN_measurable hbN_mono
      have hc_lintegral :
          ∫⁻ z, c z ∂MeasureTheory.volume =
            ⨆ M, ∫⁻ z, cN M z ∂MeasureTheory.volume := by
        -- And likewise for the target `c`.
        calc
          ∫⁻ z, c z ∂MeasureTheory.volume =
              ∫⁻ z, ⨆ M, cN M z ∂MeasureTheory.volume := by
                congr with z
                simpa [cN] using (iSup_supportTrunc_apply c z).symm
          _ = ⨆ M, ∫⁻ z, cN M z ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup hcN_measurable hcN_mono
      have ha_int_mono :
          Monotone (fun M => ∫⁻ x, aN M x ∂MeasureTheory.volume) := by
        intro M L hML
        -- Integral monotonicity follows from pointwise monotonicity of `aN`.
        exact MeasureTheory.lintegral_mono (fun x => haN_mono hML x)
      have hb_int_mono :
          Monotone (fun M => ∫⁻ y, bN M y ∂MeasureTheory.volume) := by
        intro M L hML
        -- The same integral monotonicity statement holds for `bN`.
        exact MeasureTheory.lintegral_mono (fun y => hbN_mono hML y)
      have hdiag_sup :
          (⨆ M, ∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
              (⨆ M, ∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) ≤
            ⨆ M,
              (∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
        -- A single large support radius dominates any pair of truncation indices.
        have hA_rpow :
            (⨆ M, ∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ =
              ⨆ M, (∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ :=
          (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
        have hB_rpow :
            (⨆ M, ∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) =
              ⨆ M, (∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) :=
          (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
        rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
        refine iSup_le ?_
        intro m
        rw [ENNReal.mul_iSup]
        refine iSup_le ?_
        intro l
        refine le_iSup_of_le (max m l) ?_
        exact mul_le_mul'
          (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (ha_int_mono (Nat.le_max_left m l)))
          (ENNReal.monotone_rpow_of_nonneg
            (sub_nonneg.mpr hθ_mem.2.le) (hb_int_mono (Nat.le_max_right m l)))
      have hsup_le :
          (⨆ M,
            (∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
            ⨆ M, ∫⁻ z, cN M z ∂MeasureTheory.volume := by
        refine iSup_le ?_
        intro M
        exact le_iSup_of_le M (htrunc M)
      have hresult :
          ∫⁻ z, c z ∂MeasureTheory.volume ≥
            (∫⁻ x, a x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, b y ∂MeasureTheory.volume) ^ (1 - θ) := by
        -- Once the fixed-support inequalities are available, monotone convergence in the support
        -- radius upgrades them to the full log-transported value-truncated profiles.
        calc
          ∫⁻ z, c z ∂MeasureTheory.volume =
              ⨆ M, ∫⁻ z, cN M z ∂MeasureTheory.volume := hc_lintegral
          _ ≥
              ⨆ M,
                (∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
                  (∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) := hsup_le
          _ ≥
              (⨆ M, ∫⁻ x, aN M x ∂MeasureTheory.volume) ^ θ *
                (⨆ M, ∫⁻ y, bN M y ∂MeasureTheory.volume) ^ (1 - θ) := hdiag_sup
          _ =
              (∫⁻ x, a x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, b y ∂MeasureTheory.volume) ^ (1 - θ) := by
                  rw [ha_lintegral, hb_lintegral]
      -- Route correction: the old proof tried to recurse on lower value cutoffs. The current
      -- route freezes the cutoff `n`, transports the truncated positive profiles to log
      -- coordinates, proves the fixed-support inequality there, and then lets the support radius
      -- tend to infinity.
      calc
        ∫⁻ r, min (n : ENNReal) (Cpos r) ∂MeasureTheory.volume =
            ∫⁻ z, c z ∂MeasureTheory.volume := by
              rw [← hC_log]
        _ ≥
            (∫⁻ x, a x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, b y ∂MeasureTheory.volume) ^ (1 - θ) := hresult
        _ =
            (∫⁻ s, min (n : ENNReal) (Apos s) ∂MeasureTheory.volume) ^ θ *
              (∫⁻ t, min (n : ENNReal) (Bpos t) ∂MeasureTheory.volume) ^ (1 - θ) := by
                rw [hA_log, hB_log]

/-- The remaining compactly supported logarithmic-profile truncation step needed for the direct
compact-support Prékopa-Leindler argument. -/
private lemma positive_profile_core_compact_support_direct_log_profile_base
    {α β γ : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hα_measurable : Measurable α)
    (hβ_measurable : Measurable β)
    (hγ_measurable : Measurable γ)
    (hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t ->
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
    let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
    let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
    ∀ M : ℕ,
      ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
        (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
  dsimp
  intro M
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
  let αlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc αlog L
  let βlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc βlog L
  let γlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc γlog L
  let A : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < αlogN M x}
  let B : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < βlogN M y}
  let C : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < γlogN M z}
  change
    ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
      (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ)
  have hlog_kernel :
      ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
    intro x y
    -- The multiplicative profile kernel becomes additive after the logarithmic transport.
    simpa [αlog, βlog, γlog] using
      (log_profile_kernel_transport (α := α) (β := β) (γ := γ) hθ_mem hkernel_profile x y)
  have hlog_trunc_kernel :
      ∀ x y,
        γlogN M (θ * x + (1 - θ) * y) ≥
          αlogN M x ^ θ * βlogN M y ^ (1 - θ) := by
    intro x y
    by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
    · by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
      · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(M : ℝ)) M := by
          rcases hx with ⟨hx_left, hx_right⟩
          rcases hy with ⟨hy_left, hy_right⟩
          -- Affine combinations of points in `[-M, M]` stay in the same compact interval.
          constructor <;>
            nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
        -- On the common truncation interval, the support cutoffs disappear.
        simpa [αlogN, βlogN, γlogN, supportTrunc, hx, hy, hz] using hlog_kernel x y
      · have hy_zero : βlogN M y = 0 := by
          simp [βlogN, supportTrunc, hy]
        -- If `y` leaves the truncation window, the right-hand side already vanishes.
        rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hx_zero : αlogN M x = 0 := by
        simp [αlogN, supportTrunc, hx]
      -- Symmetrically when `x` leaves the truncation window.
      rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  have hαlog_measurable : Measurable αlog := by
    -- The logarithmic transport is measurable because both `exp` and `α` are measurable.
    simpa [αlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hα_measurable.comp Real.measurable_exp))
  have hβlog_measurable : Measurable βlog := by
    -- The same change-of-variables measurability statement holds for `βlog`.
    simpa [βlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hβ_measurable.comp Real.measurable_exp))
  have hγlog_measurable : Measurable γlog := by
    -- And likewise for `γlog`.
    simpa [γlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hγ_measurable.comp Real.measurable_exp))
  have hαlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → αlogN M x = 0 := by
    intro x hx
    -- Outside `[-M, M]`, the support truncation of `αlog` vanishes by construction.
    simpa [αlogN] using (supportTrunc_eq_zero_of_not_mem (f := αlog) (N := M) (x := x) hx)
  have hβlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → βlogN M x = 0 := by
    intro x hx
    -- The same support cutoff description holds for `βlog`.
    simpa [βlogN] using (supportTrunc_eq_zero_of_not_mem (f := βlog) (N := M) (x := x) hx)
  have hγlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → γlogN M x = 0 := by
    intro x hx
    -- And likewise for `γlog`.
    simpa [γlogN] using (supportTrunc_eq_zero_of_not_mem (f := γlog) (N := M) (x := x) hx)
  have hA_antitone : Antitone A := by
    -- Strict-superlevel volume profiles are antitone in the threshold parameter.
    simpa [A] using strictSuperlevelProfile_antitone (αlogN M)
  have hB_antitone : Antitone B := by
    -- The same monotonicity statement holds for `βlogN M`.
    simpa [B] using strictSuperlevelProfile_antitone (βlogN M)
  have hC_antitone : Antitone C := by
    -- And likewise for `γlogN M`.
    simpa [C] using strictSuperlevelProfile_antitone (γlogN M)
  have hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤ := by
    intro s hs
    -- Positive strict superlevel sets stay inside the compact support interval `[-M, M]`.
    apply volume_lt_top_of_subset_supportInterval
    exact strictSuperlevel_subset_support hαlogN_support hs
  have hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤ := by
    intro t ht
    -- The same finite-volume reduction applies to `βlogN M`.
    apply volume_lt_top_of_subset_supportInterval
    exact strictSuperlevel_subset_support hβlogN_support ht
  have hkernel_fixed :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ)) := by
    -- Route correction: the remaining kernel on the strict-superlevel profiles is now obtained
    -- directly from the fixed compactly supported log transports, without re-entering the later
    -- wrapper chain.
    simpa [A, B, C] using
      (compactSupport_strictSuperlevelProfile_kernel
        (a := αlogN M) (b := βlogN M) (c := γlogN M)
        hθ_mem (supportTrunc_measurable hαlog_measurable M)
        (supportTrunc_measurable hβlog_measurable M)
        (supportTrunc_measurable hγlog_measurable M)
        M hαlogN_support hβlogN_support hγlogN_support hlog_trunc_kernel)
  have hα_profile :
      ∫⁻ x, αlogN M x ∂MeasureTheory.volume =
        ∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume := by
    -- Layer-cake rewrites the truncated log integral as its strict-superlevel profile.
    simpa [A] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hαlog_measurable M) (f := αlogN M))
  have hβ_profile :
      ∫⁻ y, βlogN M y ∂MeasureTheory.volume =
        ∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume := by
    -- The same layer-cake identity applies to `βlogN M`.
    simpa [B] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hβlog_measurable M) (f := βlogN M))
  have hγ_profile :
      ∫⁻ z, γlogN M z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume := by
    -- And likewise for `γlogN M`.
    simpa [C] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hγlog_measurable M) (f := γlogN M))
  have hcore :
      ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume ≥
        (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := by
    have hA_measurable : Measurable A := by
      -- Strict-superlevel profiles are measurable because they are antitone.
      simpa using (Antitone.measurable hA_antitone)
    have hB_measurable : Measurable B := by
      -- The same monotonicity-to-measurability argument applies to `B`.
      simpa using (Antitone.measurable hB_antitone)
    have hC_measurable : Measurable C := by
      -- And likewise for `C`.
      simpa using (Antitone.measurable hC_antitone)
    let Apos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) A
    let Bpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) B
    let Cpos : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ)) C
    have hApos_measurable : Measurable Apos := by
      -- Restricting the positive-profile to `(0, ∞)` preserves measurability.
      simpa [Apos] using hA_measurable.indicator measurableSet_Ioi
    have hBpos_measurable : Measurable Bpos := by
      -- The same positive-half-line restriction works for `B`.
      simpa [Bpos] using hB_measurable.indicator measurableSet_Ioi
    have hCpos_measurable : Measurable Cpos := by
      -- And likewise for `C`.
      simpa [Cpos] using hC_measurable.indicator measurableSet_Ioi
    have htrunc :
        ∀ n : ℕ,
          ∫⁻ r, min (n : ENNReal) (Cpos r) ∂MeasureTheory.volume ≥
            (∫⁻ s, min (n : ENNReal) (Apos s) ∂MeasureTheory.volume) ^ θ *
              (∫⁻ t, min (n : ENNReal) (Bpos t) ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- Route correction: factor the broken inline `Nat.succ` branch through the dedicated
      -- bounded-value positive-profile bridge, so the target theorem only depends on the corrected
      -- truncation object rather than mismatched lower-layer profile identities.
      simpa [Apos, Bpos, Cpos] using
        (positive_profile_value_truncation_bridge
          (A := A) (B := B) (C := C)
          hθ_mem hA_antitone hB_antitone hC_antitone hA_lt_top hB_lt_top hkernel_fixed)
    -- Once every finite value truncation satisfies Prékopa-Leindler, monotone convergence upgrades
    -- the estimates to the full positive-half-line integrals of `A`, `B`, and `C`.
    simpa [Apos, Bpos, Cpos, MeasureTheory.lintegral_indicator] using
      (prekopaLeindler_from_value_truncations
        hθ_mem hApos_measurable hBpos_measurable hCpos_measurable htrunc)
  calc
    ∫⁻ z, γlogN M z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume := hγ_profile
    _ ≥
        (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := hcore
    _ =
        (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [← hα_profile, ← hβ_profile]

/-- A compactly supported one-dimensional ENNReal kernel satisfies Prékopa-Leindler on `ℝ`. -/
private lemma positive_profile_core_compact_support_direct
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (N : ℕ)
    (hf_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f x = 0)
    (hg_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g x = 0)
    (hh_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h x = 0)
    (h_kernel :
      ∀ x y : ℝ,
        h (θ * x + (1 - θ) * y) ≥ f x ^ θ * g y ^ (1 - θ)) :
    ∫⁻ z, h z ∂MeasureTheory.volume ≥
      (∫⁻ x, f x ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, g y ∂MeasureTheory.volume) ^ (1 - θ) := by
  let α : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < f x}
  let β : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < g y}
  let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < h z}
  have hα_antitone : Antitone α := by
    -- The strict-superlevel profile of `f` is antitone in the threshold parameter.
    simpa [α] using strictSuperlevelProfile_antitone f
  have hβ_antitone : Antitone β := by
    -- The same monotonicity statement holds for `g`.
    simpa [β] using strictSuperlevelProfile_antitone g
  have hγ_antitone : Antitone γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using strictSuperlevelProfile_antitone h
  have hα_measurable : Measurable α := by
    -- Antitone real profiles are measurable.
    simpa [α] using (Antitone.measurable hα_antitone)
  have hβ_measurable : Measurable β := by
    -- The same monotonicity-to-measurability argument applies to `β`.
    simpa [β] using (Antitone.measurable hβ_antitone)
  have hγ_measurable : Measurable γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using (Antitone.measurable hγ_antitone)
  have hα_profile :
      ∫⁻ x, f x ∂MeasureTheory.volume =
        ∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume := by
    -- The layer-cake identity rewrites the `f`-integral in terms of its strict-superlevel
    -- profile.
    simpa [α] using ennreal_lintegral_eq_strictSuperlevelProfile hf_measurable (f := f)
  have hβ_profile :
      ∫⁻ y, g y ∂MeasureTheory.volume =
        ∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume := by
    -- The same strict-superlevel formula applies to `g`.
    simpa [β] using ennreal_lintegral_eq_strictSuperlevelProfile hg_measurable (f := g)
  have hγ_profile :
      ∫⁻ z, h z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := by
    -- And likewise for the target function `h`.
    simpa [γ] using ennreal_lintegral_eq_strictSuperlevelProfile hh_measurable (f := h)
  have hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t → α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    -- Route correction: instead of re-entering the recursive logarithmic transport, first extract
    -- the exact strict-superlevel kernel that already follows from compact support on the source
    -- side.
    simpa [α, β, γ] using
      (compactSupport_strictSuperlevelProfile_kernel
        (a := f) (b := g) (c := h)
        hθ_mem hf_measurable hg_measurable hh_measurable N
        hf_support hg_support hh_support h_kernel)
  have h_profile :
      ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume ≥
        (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := by
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    have hα_log :
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
          ∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume := by
      -- The `f`-profile over `Set.Ioi 0` is exactly the full-line integral of its log transport.
      simpa [αlog] using (log_profile_lintegral_eq (phi := α)).symm
    have hβ_log :
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
          ∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume := by
      -- The same logarithmic change of variables applies to `β`.
      simpa [βlog] using (log_profile_lintegral_eq (phi := β)).symm
    have hγ_log :
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
          ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := by
      -- And likewise for the target profile `γ`.
      simpa [γlog] using (log_profile_lintegral_eq (phi := γ)).symm
    have hlog_kernel :
        ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
      intro x y
      -- Route correction: the multiplicative profile kernel becomes additive after the logarithmic
      -- transport `r = exp x`.
      simpa [αlog, βlog, γlog] using
        (log_profile_kernel_transport (α := α) (β := β) (γ := γ) hθ_mem hkernel_profile x y)
    let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
    let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
    let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
    have hαlog_measurable : Measurable αlog := by
      -- The logarithmic transport is measurable because both `exp` and `α` are measurable.
      simpa [αlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hα_measurable.comp Real.measurable_exp))
    have hβlog_measurable : Measurable βlog := by
      -- The same change-of-variables measurability statement holds for `βlog`.
      simpa [βlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hβ_measurable.comp Real.measurable_exp))
    have hγlog_measurable : Measurable γlog := by
      -- And again for `γlog`.
      simpa [γlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hγ_measurable.comp Real.measurable_exp))
    have hαlogN_measurable : ∀ M, Measurable (αlogN M) := by
      intro M
      -- Compact support truncation preserves measurability for the transported `α`-profile.
      simpa [αlogN] using supportTrunc_measurable hαlog_measurable M
    have hβlogN_measurable : ∀ M, Measurable (βlogN M) := by
      intro M
      -- The same support truncation argument applies to `βlog`.
      simpa [βlogN] using supportTrunc_measurable hβlog_measurable M
    have hγlogN_measurable : ∀ M, Measurable (γlogN M) := by
      intro M
      -- And likewise for `γlog`.
      simpa [γlogN] using supportTrunc_measurable hγlog_measurable M
    have hαlogN_mono : Monotone αlogN := by
      intro M L hML x
      -- Enlarging the compact truncation interval only increases the truncated `αlog` profile.
      simpa [αlogN] using supportTrunc_mono (f := αlog) hML x
    have hβlogN_mono : Monotone βlogN := by
      intro M L hML y
      -- The same pointwise monotonicity holds for the `βlog` truncations.
      simpa [βlogN] using supportTrunc_mono (f := βlog) hML y
    have hγlogN_mono : Monotone γlogN := by
      intro M L hML z
      -- And again for the target `γlog` truncations.
      simpa [γlogN] using supportTrunc_mono (f := γlog) hML z
    have htrunc :
        ∀ M : ℕ,
          ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
            (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- Route correction: the whole remaining analytic gap is isolated in the dedicated helper
      -- `positive_profile_core_compact_support_direct_log_profile_base`.
      simpa [α, β, γ, αlog, βlog, γlog, αlogN, βlogN, γlogN] using
        (positive_profile_core_compact_support_direct_log_profile_base
          (α := α) (β := β) (γ := γ)
          hθ_mem hα_measurable hβ_measurable hγ_measurable hkernel_profile)
    have hαlog_lintegral :
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume := by
      -- Monotone convergence sends the compact log truncations back to the full `αlog` integral.
      calc
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
            ∫⁻ x, ⨆ M, αlogN M x ∂MeasureTheory.volume := by
              congr with x
              simpa [αlogN] using (iSup_supportTrunc_apply αlog x).symm
        _ = ⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hαlogN_measurable hαlogN_mono
    have hβlog_lintegral :
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume := by
      -- The same monotone-convergence rewrite applies to `βlog`.
      calc
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
            ∫⁻ y, ⨆ M, βlogN M y ∂MeasureTheory.volume := by
              congr with y
              simpa [βlogN] using (iSup_supportTrunc_apply βlog y).symm
        _ = ⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hβlogN_measurable hβlogN_mono
    have hγlog_lintegral :
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := by
      -- And likewise for the target `γlog`.
      calc
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
            ∫⁻ z, ⨆ M, γlogN M z ∂MeasureTheory.volume := by
              congr with z
              simpa [γlogN] using (iSup_supportTrunc_apply γlog z).symm
        _ = ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hγlogN_measurable hγlogN_mono
    have hαlog_int_mono :
        Monotone (fun M => ∫⁻ x, αlogN M x ∂MeasureTheory.volume) := by
      intro M L hML
      -- Integral monotonicity follows from pointwise monotonicity of the truncations.
      exact MeasureTheory.lintegral_mono (fun x => hαlogN_mono hML x)
    have hβlog_int_mono :
        Monotone (fun M => ∫⁻ y, βlogN M y ∂MeasureTheory.volume) := by
      intro M L hML
      -- The same integral monotonicity statement holds for `βlog`.
      exact MeasureTheory.lintegral_mono (fun y => hβlogN_mono hML y)
    have hlog_diag_sup :
        (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) ≤
          ⨆ M,
            (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- A single large truncation index dominates any pair of compact log truncations.
      have hA_rpow :
          (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ =
            ⨆ M, (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ :=
        (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
      have hB_rpow :
          (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) =
            ⨆ M, (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) :=
        (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
      rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
      refine iSup_le ?_
      intro m
      rw [ENNReal.mul_iSup]
      refine iSup_le ?_
      intro n
      refine le_iSup_of_le (max m n) ?_
      exact mul_le_mul'
        (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (hαlog_int_mono (Nat.le_max_left m n)))
        (ENNReal.monotone_rpow_of_nonneg
          (sub_nonneg.mpr hθ_mem.2.le) (hβlog_int_mono (Nat.le_max_right m n)))
    have hlog_sup_le :
        (⨆ M,
          (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
          ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := by
      refine iSup_le ?_
      intro M
      exact le_iSup_of_le M (htrunc M)
    -- Route correction: once the bounded log-truncation step is isolated as `htrunc`, the rest of
    -- the argument is the deterministic monotone-convergence passage back to the full line.
    calc
      ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume = ∫⁻ z, γlog z ∂MeasureTheory.volume := by
        symm
        exact hγ_log
      _ = ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := hγlog_lintegral
      _ ≥
          ⨆ M,
            (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_sup_le
      _ ≥
          (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_diag_sup
      _ =
          (∫⁻ x, αlog x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlog y ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [hαlog_lintegral, hβlog_lintegral]
      _ =
          (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
            (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [hα_log, hβ_log]
  calc
    ∫⁻ z, h z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := hγ_profile
    _ ≥
        (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := h_profile
    _ =
        (∫⁻ x, f x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, g y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [← hα_profile, ← hβ_profile]

/-- The fixed-radius support-truncated logarithmic transports satisfy the bounded-value
Prékopa-Leindler inequality at each finite truncation level. -/
private lemma positive_profile_core_log_trunc_bounded_value
    {A B C : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_antitone : Antitone A)
    (hB_antitone : Antitone B)
    (hC_antitone : Antitone C)
    (hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤)
    (hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤)
    (hkernel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
    let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
    let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
    let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
    ∀ M n : ℕ,
      ∫⁻ z, min (n : ENNReal) (γlogN M z) ∂MeasureTheory.volume ≥
        (∫⁻ x, min (n : ENNReal) (αlogN M x) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, min (n : ENNReal) (βlogN M y) ∂MeasureTheory.volume) ^ (1 - θ) := by
  dsimp
  intro M n
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
  let αlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc αlog L
  let βlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc βlog L
  let γlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc γlog L
  let α : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < αlogN M x}
  let β : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < βlogN M y}
  let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < γlogN M z}
  have hαlog_measurable : Measurable αlog := by
    have hA_measurable : Measurable A := by
      -- Antitone real profiles are measurable.
      simpa using (Antitone.measurable hA_antitone)
    -- The logarithmic transport is measurable because both `exp` and `A` are measurable.
    simpa [αlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hA_measurable.comp Real.measurable_exp))
  have hβlog_measurable : Measurable βlog := by
    have hB_measurable : Measurable B := by
      -- Antitone real profiles are measurable.
      simpa using (Antitone.measurable hB_antitone)
    -- The same change-of-variables measurability statement holds for `βlog`.
    simpa [βlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hB_measurable.comp Real.measurable_exp))
  have hγlog_measurable : Measurable γlog := by
    have hC_measurable : Measurable C := by
      -- Antitone real profiles are measurable.
      simpa using (Antitone.measurable hC_antitone)
    -- And likewise for `γlog`.
    simpa [γlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hC_measurable.comp Real.measurable_exp))
  have hlog_kernel :
      ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
    intro x y
    -- The multiplicative profile kernel becomes additive after the logarithmic transport.
    simpa [αlog, βlog, γlog] using
      (log_profile_kernel_transport (α := A) (β := B) (γ := C) hθ_mem hkernel x y)
  have hlog_trunc_kernel :
      ∀ x y,
        γlogN M (θ * x + (1 - θ) * y) ≥
          αlogN M x ^ θ * βlogN M y ^ (1 - θ) := by
    intro x y
    by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
    · by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
      · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(M : ℝ)) M := by
          rcases hx with ⟨hx_left, hx_right⟩
          rcases hy with ⟨hy_left, hy_right⟩
          -- The affine combination of two points in `[-M, M]` stays in `[-M, M]`.
          constructor <;>
            nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
        -- On the common truncation interval, the support cutoffs disappear.
        simpa [αlogN, βlogN, γlogN, supportTrunc, hx, hy, hz] using hlog_kernel x y
      · have hy_zero : βlogN M y = 0 := by
          simp [βlogN, supportTrunc, hy]
        -- If `y` lies outside the truncation window, the right-hand side already vanishes.
        rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hx_zero : αlogN M x = 0 := by
        simp [αlogN, supportTrunc, hx]
      -- Symmetrically when `x` leaves the truncation window.
      rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  have hαlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → αlogN M x = 0 := by
    intro x hx
    -- Outside `[-M, M]`, the truncation of `αlog` vanishes by construction.
    simpa [αlogN] using (supportTrunc_eq_zero_of_not_mem (f := αlog) (N := M) (x := x) hx)
  have hβlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → βlogN M x = 0 := by
    intro x hx
    -- The same support cutoff description holds for `βlog`.
    simpa [βlogN] using (supportTrunc_eq_zero_of_not_mem (f := βlog) (N := M) (x := x) hx)
  have hγlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → γlogN M x = 0 := by
    intro x hx
    -- And likewise for `γlog`.
    simpa [γlogN] using (supportTrunc_eq_zero_of_not_mem (f := γlog) (N := M) (x := x) hx)
  have hα_bound :
      ∀ x : ℝ, αlogN M x ≤ ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) := by
    -- The transported `A`-profile is uniformly bounded on the truncation window.
    simpa [αlogN, αlog] using supportTrunc_log_profile_bound hA_antitone M
  have hβ_bound :
      ∀ y : ℝ, βlogN M y ≤ ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) := by
    -- The same uniform bound holds for the transported `B`-profile.
    simpa [βlogN, βlog] using supportTrunc_log_profile_bound hB_antitone M
  have hα_cap_lt_top :
      ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) < ⊤ := by
    -- The explicit `A`-bound is finite because `A` is finite on positive radii.
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hA_lt_top (Real.exp_pos _))
  have hβ_cap_lt_top :
      ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) < ⊤ := by
    -- The same finiteness statement holds for the explicit `B`-bound.
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hB_lt_top (Real.exp_pos _))
  have hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    -- The strict-superlevel profiles of the fixed support-truncated log triple satisfy the same
    -- multiplicative kernel.
    simpa [α, β, γ] using
      (compactSupport_strictSuperlevelProfile_kernel
        (a := αlogN M) (b := βlogN M) (c := γlogN M)
        hθ_mem (supportTrunc_measurable hαlog_measurable M)
        (supportTrunc_measurable hβlog_measurable M)
        (supportTrunc_measurable hγlog_measurable M)
        M hαlogN_support hβlogN_support hγlogN_support hlog_trunc_kernel)
  -- Route correction: the remaining blocker is now isolated to the finite-interval profile
  -- argument on `(0,n)`. The pointwise bounds and the fixed-`M` profile kernel above are the
  -- exact ingredients needed to finish the non-recursive bounded-value step from Agent C's plan.
  by_cases hn : n = 0
  · -- At cutoff `n = 0`, all three value-truncated integrals vanish immediately.
    subst hn
    simp [ENNReal.zero_rpow_of_pos hθ_mem.1, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2)]
  · have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
    have hα_antitone : Antitone α := by
      -- Strict-superlevel volume profiles are antitone in the threshold parameter.
      simpa [α] using strictSuperlevelProfile_antitone (αlogN M)
    have hβ_antitone : Antitone β := by
      -- The same monotonicity statement holds for `β`.
      simpa [β] using strictSuperlevelProfile_antitone (βlogN M)
    have hγ_antitone : Antitone γ := by
      -- And likewise for `γ`.
      simpa [γ] using strictSuperlevelProfile_antitone (γlogN M)
    have hα_measurable : Measurable α := by
      -- Antitone real profiles are measurable.
      simpa using (Antitone.measurable hα_antitone)
    have hβ_measurable : Measurable β := by
      -- The same monotonicity-to-measurability argument applies to `β`.
      simpa using (Antitone.measurable hβ_antitone)
    have hγ_measurable : Measurable γ := by
      -- And likewise for the target profile `γ`.
      simpa using (Antitone.measurable hγ_antitone)
    have hα_trunc :
        ∫⁻ x, min (n : ENNReal) (αlogN M x) ∂MeasureTheory.volume =
          ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) n) α s ∂MeasureTheory.volume := by
      -- Rewrite the value-truncated `αlogN M` integral as its strict-superlevel profile on
      -- `(0,n)`.
      simpa [α] using
        ennreal_lintegral_trunc_eq_profile_trunc (supportTrunc_measurable hαlog_measurable M) n
    have hβ_trunc :
        ∫⁻ y, min (n : ENNReal) (βlogN M y) ∂MeasureTheory.volume =
          ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) n) β t ∂MeasureTheory.volume := by
      -- The same truncated layer-cake identity applies to `βlogN M`.
      simpa [β] using
        ennreal_lintegral_trunc_eq_profile_trunc (supportTrunc_measurable hβlog_measurable M) n
    have hγ_trunc :
        ∫⁻ z, min (n : ENNReal) (γlogN M z) ∂MeasureTheory.volume =
          ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n) γ r ∂MeasureTheory.volume := by
      -- And likewise for `γlogN M`.
      simpa [γ] using
        ennreal_lintegral_trunc_eq_profile_trunc (supportTrunc_measurable hγlog_measurable M) n
    let αcap : ℝ := (ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ)))).toReal
    let βcap : ℝ := (ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ)))).toReal
    have hαcap_eq : ENNReal.ofReal αcap =
        ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ))) := by
      change ENNReal.ofReal
          ((ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ)))).toReal) =
        ENNReal.ofReal (Real.exp M) * A (Real.exp (-(M : ℝ)))
      exact ENNReal.ofReal_toReal hα_cap_lt_top.ne
    have hβcap_eq : ENNReal.ofReal βcap =
        ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ))) := by
      change ENNReal.ofReal
          ((ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ)))).toReal) =
        ENNReal.ofReal (Real.exp M) * B (Real.exp (-(M : ℝ)))
      exact ENNReal.ofReal_toReal hβ_cap_lt_top.ne
    have hα_zero_above :
        ∀ ⦃s : ℝ⦄, αcap ≤ s → α s = 0 := by
      intro s hs
      -- The `α`-profile vanishes once the threshold reaches the explicit finite cap.
      have hs_real :
          αcap ≤ s := hs
      have hzero :=
        strictSuperlevelProfile_eq_zero_of_pointwise_bound
          (f := αlogN M)
          (R := αcap)
          (s := s)
          (fun x => by
            rw [hαcap_eq]
            exact hα_bound x)
          hs_real
      simpa [α] using hzero
    have hβ_zero_above :
        ∀ ⦃t : ℝ⦄, βcap ≤ t → β t = 0 := by
      intro t ht
      -- The same explicit cap kills the `β`-profile above its threshold.
      have ht_real :
          βcap ≤ t := ht
      have hzero :=
        strictSuperlevelProfile_eq_zero_of_pointwise_bound
          (f := βlogN M)
          (R := βcap)
          (s := t)
          (fun y => by
            rw [hβcap_eq]
            exact hβ_bound y)
          ht_real
      simpa [β] using hzero
    have hprofile :
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n) γ r ∂MeasureTheory.volume ≥
          (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) n) α s ∂MeasureTheory.volume) ^ θ *
            (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) n) β t ∂MeasureTheory.volume) ^ (1 - θ) := by
      let αn : ℝ → ENNReal := Set.indicator (Set.Ioo (0 : ℝ) n) α
      let βn : ℝ → ENNReal := Set.indicator (Set.Ioo (0 : ℝ) n) β
      let γn : ℝ → ENNReal := Set.indicator (Set.Ioo (0 : ℝ) n) γ
      have hαn_measurable : Measurable αn := by
        -- The interval-cutoff `α`-profile stays measurable after the indicator restriction.
        simpa [αn] using hα_measurable.indicator measurableSet_Ioo
      have hβn_measurable : Measurable βn := by
        -- The same interval cutoff preserves measurability for `β`.
        simpa [βn] using hβ_measurable.indicator measurableSet_Ioo
      have hγn_measurable : Measurable γn := by
        -- And likewise for the target profile `γ`.
        simpa [γn] using hγ_measurable.indicator measurableSet_Ioo
      have hIoo_inter_Ioi :
          Set.Ioo (0 : ℝ) n ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) n := by
        -- The interval `(0,n)` already lies in the positive half-line because `n > 0`.
        ext s
        constructor
        · intro hs
          exact hs.1
        · intro hs
          exact ⟨hs, hs.1⟩
      have hkernel_interval :
          ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
            αn s ^ θ * βn t ^ (1 - θ) ≤ γn (s ^ θ * t ^ (1 - θ)) := by
        intro s t hs ht
        by_cases hs_mem : s ∈ Set.Ioo (0 : ℝ) n
        · by_cases ht_mem : t ∈ Set.Ioo (0 : ℝ) n
          · have hgeom :
                s ^ θ * t ^ (1 - θ) ≤ θ * s + (1 - θ) * t := by
              -- Weighted AM-GM controls the multiplicative interpolation by the affine one.
              exact Real.geom_mean_le_arith_mean2_weighted
                hθ_mem.1.le (sub_nonneg.mpr hθ_mem.2.le) hs.le ht.le (by ring)
            have hsum_lt : θ * s + (1 - θ) * t < n := by
              -- The affine interpolation stays strictly below `n` because both inputs do.
              nlinarith [hθ_mem.1, hθ_mem.2, hs_mem.2, ht_mem.2]
            have hst_mem : s ^ θ * t ^ (1 - θ) ∈ Set.Ioo (0 : ℝ) n := by
              constructor
              · -- Positive inputs keep the weighted geometric mean positive.
                positivity
              · exact lt_of_le_of_lt hgeom hsum_lt
            -- On the interval `(0,n)`, the cutoff indicators are transparent.
            simpa [αn, βn, γn, hs_mem, ht_mem, hst_mem] using hkernel_profile hs ht
          · have hβn_zero : βn t = 0 := by
              simp [βn, ht_mem]
            -- If `t` leaves the cutoff interval, the right-hand side already vanishes.
            rw [hβn_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
            exact bot_le
        · have hαn_zero : αn s = 0 := by
            simp [αn, hs_mem]
          -- Symmetrically when `s` leaves the cutoff interval.
          rw [hαn_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
          exact bot_le
      let αnlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * αn (Real.exp x)
      let βnlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * βn (Real.exp y)
      let γnlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γn (Real.exp z)
      have hαnlog_lintegral :
          ∫⁻ x, αnlog x ∂MeasureTheory.volume =
            ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) n) α s ∂MeasureTheory.volume := by
        -- The interval-cutoff `α`-profile is exactly the log transport of `αn`.
        calc
          ∫⁻ x, αnlog x ∂MeasureTheory.volume =
              ∫⁻ s in Set.Ioi 0, αn s ∂MeasureTheory.volume := by
                simpa [αnlog] using (log_profile_lintegral_eq (phi := αn)).symm
          _ = ∫⁻ s, αn s ∂MeasureTheory.volume := by
                simpa [αn, MeasureTheory.lintegral_indicator, hIoo_inter_Ioi]
          _ = ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) n) α s ∂MeasureTheory.volume := by
                rfl
      have hβnlog_lintegral :
          ∫⁻ y, βnlog y ∂MeasureTheory.volume =
            ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) n) β t ∂MeasureTheory.volume := by
        -- The same logarithmic change of variables applies to `βn`.
        calc
          ∫⁻ y, βnlog y ∂MeasureTheory.volume =
              ∫⁻ t in Set.Ioi 0, βn t ∂MeasureTheory.volume := by
                simpa [βnlog] using (log_profile_lintegral_eq (phi := βn)).symm
          _ = ∫⁻ t, βn t ∂MeasureTheory.volume := by
                simpa [βn, MeasureTheory.lintegral_indicator, hIoo_inter_Ioi]
          _ = ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) n) β t ∂MeasureTheory.volume := by
                rfl
      have hγnlog_lintegral :
          ∫⁻ z, γnlog z ∂MeasureTheory.volume =
            ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n) γ r ∂MeasureTheory.volume := by
        -- And likewise for the target interval-cutoff profile `γn`.
        calc
          ∫⁻ z, γnlog z ∂MeasureTheory.volume =
              ∫⁻ r in Set.Ioi 0, γn r ∂MeasureTheory.volume := by
                simpa [γnlog] using (log_profile_lintegral_eq (phi := γn)).symm
          _ = ∫⁻ r, γn r ∂MeasureTheory.volume := by
                simpa [γn, MeasureTheory.lintegral_indicator, hIoo_inter_Ioi]
          _ = ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n) γ r ∂MeasureTheory.volume := by
                rfl
      let αnlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc αnlog L
      let βnlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc βnlog L
      let γnlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc γnlog L
      have hαnlog_measurable : Measurable αnlog := by
        -- The logarithmic transport is measurable because both `exp` and `αn` are measurable.
        simpa [αnlog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hαn_measurable.comp Real.measurable_exp))
      have hβnlog_measurable : Measurable βnlog := by
        -- The same change-of-variables measurability statement holds for `βnlog`.
        simpa [βnlog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hβn_measurable.comp Real.measurable_exp))
      have hγnlog_measurable : Measurable γnlog := by
        -- And again for `γnlog`.
        simpa [γnlog] using
          ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
            (hγn_measurable.comp Real.measurable_exp))
      have hαnlogN_measurable : ∀ L, Measurable (αnlogN L) := by
        intro L
        -- Compact support truncation preserves measurability for the transported `αn`-profile.
        simpa [αnlogN] using supportTrunc_measurable hαnlog_measurable L
      have hβnlogN_measurable : ∀ L, Measurable (βnlogN L) := by
        intro L
        -- The same support truncation argument applies to `βnlog`.
        simpa [βnlogN] using supportTrunc_measurable hβnlog_measurable L
      have hγnlogN_measurable : ∀ L, Measurable (γnlogN L) := by
        intro L
        -- And likewise for `γnlog`.
        simpa [γnlogN] using supportTrunc_measurable hγnlog_measurable L
      have hαnlogN_mono : Monotone αnlogN := by
        intro L L' hLL' x
        -- Enlarging the compact truncation interval only increases the truncated `αnlog` profile.
        simpa [αnlogN] using supportTrunc_mono (f := αnlog) hLL' x
      have hβnlogN_mono : Monotone βnlogN := by
        intro L L' hLL' y
        -- The same pointwise monotonicity holds for the `βnlog` truncations.
        simpa [βnlogN] using supportTrunc_mono (f := βnlog) hLL' y
      have hγnlogN_mono : Monotone γnlogN := by
        intro L L' hLL' z
        -- And again for the target `γnlog` truncations.
        simpa [γnlogN] using supportTrunc_mono (f := γnlog) hLL' z
      have hlog_kernel :
          ∀ x y : ℝ, γnlog (θ * x + (1 - θ) * y) ≥ αnlog x ^ θ * βnlog y ^ (1 - θ) := by
        intro x y
        -- The multiplicative interval-cutoff kernel becomes additive after the logarithmic
        -- transport.
        simpa [αnlog, βnlog, γnlog] using
          (log_profile_kernel_transport
            (α := αn) (β := βn) (γ := γn) hθ_mem hkernel_interval x y)
      have hlog_trunc_kernel :
          ∀ L x y,
            γnlogN L (θ * x + (1 - θ) * y) ≥
              αnlogN L x ^ θ * βnlogN L y ^ (1 - θ) := by
        intro L x y
        by_cases hx : x ∈ Set.Icc (-(L : ℝ)) L
        · by_cases hy : y ∈ Set.Icc (-(L : ℝ)) L
          · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(L : ℝ)) L := by
              rcases hx with ⟨hx_left, hx_right⟩
              rcases hy with ⟨hy_left, hy_right⟩
              -- Affine combinations preserve the common compact truncation interval.
              constructor <;>
                nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
            -- On the common truncation interval, the support cutoffs disappear.
            simpa [αnlogN, βnlogN, γnlogN, supportTrunc, hx, hy, hz] using hlog_kernel x y
          · have hy_zero : βnlogN L y = 0 := by
              simp [βnlogN, supportTrunc, hy]
            -- If `y` leaves the truncation window, the right-hand side already vanishes.
            rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
            exact bot_le
        · have hx_zero : αnlogN L x = 0 := by
            simp [αnlogN, supportTrunc, hx]
          -- Symmetrically when `x` leaves the truncation window.
          rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
          exact bot_le
      have htrunc :
          ∀ L : ℕ,
            ∫⁻ z, γnlogN L z ∂MeasureTheory.volume ≥
              (∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) := by
        intro L
        have hαnlogN_supportL :
            ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(L : ℝ)) L → αnlogN L x = 0 := by
          intro x hx
          -- Outside `[-L, L]`, the support truncation of `αnlog` vanishes.
          simpa [αnlogN] using
            (supportTrunc_eq_zero_of_not_mem (f := αnlog) (N := L) (x := x) hx)
        have hβnlogN_supportL :
            ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(L : ℝ)) L → βnlogN L x = 0 := by
          intro x hx
          -- The same support cutoff description holds for `βnlog`.
          simpa [βnlogN] using
            (supportTrunc_eq_zero_of_not_mem (f := βnlog) (N := L) (x := x) hx)
        have hγnlogN_supportL :
            ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(L : ℝ)) L → γnlogN L x = 0 := by
          intro x hx
          -- And likewise for `γnlog`.
          simpa [γnlogN] using
            (supportTrunc_eq_zero_of_not_mem (f := γnlog) (N := L) (x := x) hx)
        -- Route correction: the original target now reduces to a single compact-support theorem
        -- applied to the fixed-radius log truncations of the interval-cutoff profiles.
        simpa [αnlog, βnlog, γnlog, αnlogN, βnlogN, γnlogN] using
          (positive_profile_core_compact_support_direct
            (f := αnlogN L) (g := βnlogN L) (h := γnlogN L)
            hθ_mem (supportTrunc_measurable hαnlog_measurable L)
            (supportTrunc_measurable hβnlog_measurable L)
            (supportTrunc_measurable hγnlog_measurable L)
            L hαnlogN_supportL hβnlogN_supportL hγnlogN_supportL
            (hlog_trunc_kernel L))
      have hαnlog_lintegral_full :
          ∫⁻ x, αnlog x ∂MeasureTheory.volume =
            ⨆ L, ∫⁻ x, αnlogN L x ∂MeasureTheory.volume := by
        -- Monotone convergence sends the compact log truncations back to the full `αnlog`
        -- integral.
        calc
          ∫⁻ x, αnlog x ∂MeasureTheory.volume =
              ∫⁻ x, ⨆ L, αnlogN L x ∂MeasureTheory.volume := by
                congr with x
                simpa [αnlogN] using (iSup_supportTrunc_apply αnlog x).symm
          _ = ⨆ L, ∫⁻ x, αnlogN L x ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup hαnlogN_measurable hαnlogN_mono
      have hβnlog_lintegral_full :
          ∫⁻ y, βnlog y ∂MeasureTheory.volume =
            ⨆ L, ∫⁻ y, βnlogN L y ∂MeasureTheory.volume := by
        -- The same monotone-convergence rewrite applies to `βnlog`.
        calc
          ∫⁻ y, βnlog y ∂MeasureTheory.volume =
              ∫⁻ y, ⨆ L, βnlogN L y ∂MeasureTheory.volume := by
                congr with y
                simpa [βnlogN] using (iSup_supportTrunc_apply βnlog y).symm
          _ = ⨆ L, ∫⁻ y, βnlogN L y ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup hβnlogN_measurable hβnlogN_mono
      have hγnlog_lintegral_full :
          ∫⁻ z, γnlog z ∂MeasureTheory.volume =
            ⨆ L, ∫⁻ z, γnlogN L z ∂MeasureTheory.volume := by
        -- And likewise for the target `γnlog`.
        calc
          ∫⁻ z, γnlog z ∂MeasureTheory.volume =
              ∫⁻ z, ⨆ L, γnlogN L z ∂MeasureTheory.volume := by
                congr with z
                simpa [γnlogN] using (iSup_supportTrunc_apply γnlog z).symm
          _ = ⨆ L, ∫⁻ z, γnlogN L z ∂MeasureTheory.volume :=
              MeasureTheory.lintegral_iSup hγnlogN_measurable hγnlogN_mono
      have hαnlog_int_mono :
          Monotone (fun L => ∫⁻ x, αnlogN L x ∂MeasureTheory.volume) := by
        intro L L' hLL'
        -- Integral monotonicity follows from pointwise monotonicity of the truncations.
        exact MeasureTheory.lintegral_mono (fun x => hαnlogN_mono hLL' x)
      have hβnlog_int_mono :
          Monotone (fun L => ∫⁻ y, βnlogN L y ∂MeasureTheory.volume) := by
        intro L L' hLL'
        -- The same integral monotonicity statement holds for `βnlog`.
        exact MeasureTheory.lintegral_mono (fun y => hβnlogN_mono hLL' y)
      have hlog_diag_sup :
          (⨆ L, ∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
              (⨆ L, ∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) ≤
            ⨆ L,
              (∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) := by
        -- A single large truncation index dominates any pair of compact log truncations.
        have hA_rpow :
            (⨆ L, ∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ =
              ⨆ L, (∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ :=
          (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
        have hB_rpow :
            (⨆ L, ∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) =
              ⨆ L, (∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) :=
          (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
        rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
        refine iSup_le ?_
        intro m
        rw [ENNReal.mul_iSup]
        refine iSup_le ?_
        intro l
        refine le_iSup_of_le (max m l) ?_
        exact mul_le_mul'
          (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le
            (hαnlog_int_mono (Nat.le_max_left m l)))
          (ENNReal.monotone_rpow_of_nonneg
            (sub_nonneg.mpr hθ_mem.2.le) (hβnlog_int_mono (Nat.le_max_right m l)))
      have hlog_sup_le :
          (⨆ L,
            (∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
            ⨆ L, ∫⁻ z, γnlogN L z ∂MeasureTheory.volume := by
        refine iSup_le ?_
        intro L
        exact le_iSup_of_le L (htrunc L)
      -- Route correction: once the fixed-radius compact-support theorem is isolated, the rest is
      -- the standard monotone-convergence passage back to the original interval-cutoff profiles.
      calc
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n) γ r ∂MeasureTheory.volume =
            ∫⁻ z, γnlog z ∂MeasureTheory.volume := by
              rw [hγnlog_lintegral]
        _ = ⨆ L, ∫⁻ z, γnlogN L z ∂MeasureTheory.volume := hγnlog_lintegral_full
        _ ≥
            ⨆ L,
              (∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_sup_le
        _ ≥
            (⨆ L, ∫⁻ x, αnlogN L x ∂MeasureTheory.volume) ^ θ *
              (⨆ L, ∫⁻ y, βnlogN L y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_diag_sup
        _ =
            (∫⁻ x, αnlog x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βnlog y ∂MeasureTheory.volume) ^ (1 - θ) := by
                rw [hαnlog_lintegral_full, hβnlog_lintegral_full]
        _ =
            (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) n) α s ∂MeasureTheory.volume) ^ θ *
              (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) n) β t ∂MeasureTheory.volume) ^ (1 - θ) := by
                rw [hαnlog_lintegral, hβnlog_lintegral]
    -- Rewrite the bounded-value goal back to the three truncated layer-cake integrals.
    rw [hγ_trunc, hα_trunc, hβ_trunc]
    exact hprofile

/-- The fixed-radius cutoff-log inequality is the remaining primitive positive-profile step needed
for the bounded-value compact-support argument. -/
private lemma positive_profile_core_log_trunc_step
    {A B C : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_antitone : Antitone A)
    (hB_antitone : Antitone B)
    (hC_antitone : Antitone C)
    (hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤)
    (hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤)
    (hkernel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
    let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
    let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
    let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
    ∀ M : ℕ,
      ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
        (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
  dsimp
  intro M
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
  let αlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc αlog L
  let βlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc βlog L
  let γlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc γlog L
  change
    ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
      (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ)
  have hlog_kernel :
      ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
    intro x y
    -- The multiplicative profile kernel becomes additive after the logarithmic transport.
    simpa [αlog, βlog, γlog] using
      (log_profile_kernel_transport (α := A) (β := B) (γ := C) hθ_mem hkernel x y)
  have hlog_trunc_kernel :
      ∀ x y,
        γlogN M (θ * x + (1 - θ) * y) ≥
          αlogN M x ^ θ * βlogN M y ^ (1 - θ) := by
    intro x y
    by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
    · by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
      · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(M : ℝ)) M := by
          rcases hx with ⟨hx_left, hx_right⟩
          rcases hy with ⟨hy_left, hy_right⟩
          -- The affine combination of two points in `[-M, M]` stays in `[-M, M]`.
          constructor <;>
            nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
        -- On the common truncation interval, the support cutoffs disappear.
        simpa [αlogN, βlogN, γlogN, supportTrunc, hx, hy, hz] using hlog_kernel x y
      · have hy_zero : βlogN M y = 0 := by
          simp [βlogN, supportTrunc, hy]
        -- If `y` lies outside the truncation window, the right-hand side already vanishes.
        rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hx_zero : αlogN M x = 0 := by
        simp [αlogN, supportTrunc, hx]
      -- Symmetrically when `x` leaves the truncation window.
      rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  have hA_measurable : Measurable A := by
    -- Antitone real profiles are measurable.
    simpa using (Antitone.measurable hA_antitone)
  have hB_measurable : Measurable B := by
    -- The same monotonicity-to-measurability argument applies to `B`.
    simpa using (Antitone.measurable hB_antitone)
  have hC_measurable : Measurable C := by
    -- And likewise for the target profile `C`.
    simpa using (Antitone.measurable hC_antitone)
  have hαlog_measurable : Measurable αlog := by
    -- The logarithmic transport is measurable because both `exp` and `A` are measurable.
    simpa [αlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hA_measurable.comp Real.measurable_exp))
  have hβlog_measurable : Measurable βlog := by
    -- The same change-of-variables measurability statement holds for `βlog`.
    simpa [βlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hB_measurable.comp Real.measurable_exp))
  have hγlog_measurable : Measurable γlog := by
    -- And again for `γlog`.
    simpa [γlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hC_measurable.comp Real.measurable_exp))
  have hαlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → αlogN M x = 0 := by
    intro x hx
    -- Outside `[-M, M]`, the truncation of `αlog` vanishes by construction.
    simpa [αlogN] using (supportTrunc_eq_zero_of_not_mem (f := αlog) (N := M) (x := x) hx)
  have hβlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → βlogN M x = 0 := by
    intro x hx
    -- The same support cutoff description holds for `βlog`.
    simpa [βlogN] using (supportTrunc_eq_zero_of_not_mem (f := βlog) (N := M) (x := x) hx)
  have hγlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → γlogN M x = 0 := by
    intro x hx
    -- And likewise for `γlog`.
    simpa [γlogN] using (supportTrunc_eq_zero_of_not_mem (f := γlog) (N := M) (x := x) hx)
  have htrunc :
      ∀ n : ℕ,
        ∫⁻ z, min (n : ENNReal) (γlogN M z) ∂MeasureTheory.volume ≥
          (∫⁻ x, min (n : ENNReal) (αlogN M x) ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, min (n : ENNReal) (βlogN M y) ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- Route correction: the fixed-`M` theorem is now reduced to the bounded-value profile lemma,
    -- so the only remaining unresolved step is the finite-interval layer-cake argument in `n`.
    simpa [αlog, βlog, γlog, αlogN, βlogN, γlogN] using
      (positive_profile_core_log_trunc_bounded_value
        (A := A) (B := B) (C := C)
        hθ_mem hA_antitone hB_antitone hC_antitone hA_lt_top hB_lt_top hkernel M)
  -- Once the bounded-value estimates are available for every finite cutoff, the target follows by
  -- monotone convergence in the truncation level.
  exact prekopaLeindler_from_value_truncations hθ_mem
    (supportTrunc_measurable hαlog_measurable M)
    (supportTrunc_measurable hβlog_measurable M)
    (supportTrunc_measurable hγlog_measurable M)
    htrunc

/-- The fixed-radius cutoff-log inequality is the remaining primitive positive-profile step needed
for the bounded-value compact-support argument. -/
private lemma prekopaLeindler_real_positive_profile_core
    {A B C : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_antitone : Antitone A)
    (hB_antitone : Antitone B)
    (hC_antitone : Antitone C)
    (hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤)
    (hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤)
    (hkernel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ))) :
    ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume ≥
      (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
        (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := by
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * A (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * B (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * C (Real.exp z)
  let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
  let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
  let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
  have hA_measurable : Measurable A := by
    -- Antitone real profiles are measurable.
    simpa using (Antitone.measurable hA_antitone)
  have hB_measurable : Measurable B := by
    -- The same monotonicity-to-measurability argument applies to `B`.
    simpa using (Antitone.measurable hB_antitone)
  have hC_measurable : Measurable C := by
    -- And likewise for the target profile `C`.
    simpa using (Antitone.measurable hC_antitone)
  have hα_log :
      ∫⁻ x, αlog x ∂MeasureTheory.volume =
        ∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume := by
    -- The `A`-profile over `Set.Ioi 0` is exactly the full-line integral of its log transport.
    simpa [αlog] using (log_profile_lintegral_eq (phi := A)).symm
  have hβ_log :
      ∫⁻ y, βlog y ∂MeasureTheory.volume =
        ∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume := by
    -- The same logarithmic change of variables applies to `B`.
    simpa [βlog] using (log_profile_lintegral_eq (phi := B)).symm
  have hγ_log :
      ∫⁻ z, γlog z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume := by
    -- And likewise for the target profile `C`.
    simpa [γlog] using (log_profile_lintegral_eq (phi := C)).symm
  have hαlog_measurable : Measurable αlog := by
    -- The logarithmic transport is measurable because both `exp` and `A` are measurable.
    simpa [αlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hA_measurable.comp Real.measurable_exp))
  have hβlog_measurable : Measurable βlog := by
    -- The same change-of-variables measurability statement holds for `βlog`.
    simpa [βlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hB_measurable.comp Real.measurable_exp))
  have hγlog_measurable : Measurable γlog := by
    -- And again for `γlog`.
    simpa [γlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hC_measurable.comp Real.measurable_exp))
  have hαlogN_measurable : ∀ M, Measurable (αlogN M) := by
    intro M
    -- Compact support truncation preserves measurability for the transported `A`-profile.
    simpa [αlogN] using supportTrunc_measurable hαlog_measurable M
  have hβlogN_measurable : ∀ M, Measurable (βlogN M) := by
    intro M
    -- The same support truncation argument applies to `βlog`.
    simpa [βlogN] using supportTrunc_measurable hβlog_measurable M
  have hγlogN_measurable : ∀ M, Measurable (γlogN M) := by
    intro M
    -- And likewise for `γlog`.
    simpa [γlogN] using supportTrunc_measurable hγlog_measurable M
  have hαlogN_mono : Monotone αlogN := by
    intro M L hML x
    -- Enlarging the compact truncation interval only increases the truncated `αlog` profile.
    simpa [αlogN] using supportTrunc_mono (f := αlog) hML x
  have hβlogN_mono : Monotone βlogN := by
    intro M L hML y
    -- The same pointwise monotonicity holds for the `βlog` truncations.
    simpa [βlogN] using supportTrunc_mono (f := βlog) hML y
  have hγlogN_mono : Monotone γlogN := by
    intro M L hML z
    -- And again for the target `γlog` truncations.
    simpa [γlogN] using supportTrunc_mono (f := γlog) hML z
  have htrunc :
      ∀ M : ℕ,
        ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
          (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- Route correction: the positive-profile theorem now only depends on the isolated fixed-stage
    -- compact-support statement above, not on any later recursive wrapper.
    simpa [αlog, βlog, γlog, αlogN, βlogN, γlogN] using
      (positive_profile_core_log_trunc_step
        (A := A) (B := B) (C := C)
        hθ_mem hA_antitone hB_antitone hC_antitone hA_lt_top hB_lt_top hkernel)
  have hαlog_lintegral :
      ∫⁻ x, αlog x ∂MeasureTheory.volume =
        ⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume := by
    -- Monotone convergence sends the compact log truncations back to the full `αlog` integral.
    calc
      ∫⁻ x, αlog x ∂MeasureTheory.volume =
          ∫⁻ x, ⨆ M, αlogN M x ∂MeasureTheory.volume := by
            congr with x
            simpa [αlogN] using (iSup_supportTrunc_apply αlog x).symm
      _ = ⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume :=
          MeasureTheory.lintegral_iSup hαlogN_measurable hαlogN_mono
  have hβlog_lintegral :
      ∫⁻ y, βlog y ∂MeasureTheory.volume =
        ⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume := by
    -- The same monotone-convergence rewrite applies to `βlog`.
    calc
      ∫⁻ y, βlog y ∂MeasureTheory.volume =
          ∫⁻ y, ⨆ M, βlogN M y ∂MeasureTheory.volume := by
            congr with y
            simpa [βlogN] using (iSup_supportTrunc_apply βlog y).symm
      _ = ⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume :=
          MeasureTheory.lintegral_iSup hβlogN_measurable hβlogN_mono
  have hγlog_lintegral :
      ∫⁻ z, γlog z ∂MeasureTheory.volume =
        ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := by
    -- And likewise for the target `γlog`.
    calc
      ∫⁻ z, γlog z ∂MeasureTheory.volume =
          ∫⁻ z, ⨆ M, γlogN M z ∂MeasureTheory.volume := by
            congr with z
            simpa [γlogN] using (iSup_supportTrunc_apply γlog z).symm
      _ = ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume :=
          MeasureTheory.lintegral_iSup hγlogN_measurable hγlogN_mono
  have hαlog_int_mono :
      Monotone (fun M => ∫⁻ x, αlogN M x ∂MeasureTheory.volume) := by
    intro M L hML
    -- Integral monotonicity follows from pointwise monotonicity of the truncations.
    exact MeasureTheory.lintegral_mono (fun x => hαlogN_mono hML x)
  have hβlog_int_mono :
      Monotone (fun M => ∫⁻ y, βlogN M y ∂MeasureTheory.volume) := by
    intro M L hML
    -- The same integral monotonicity statement holds for `βlog`.
    exact MeasureTheory.lintegral_mono (fun y => hβlogN_mono hML y)
  have hlog_diag_sup :
      (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) ≤
        ⨆ M,
          (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- A single large truncation index dominates any pair of compact log truncations.
    have hA_rpow :
        (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ =
          ⨆ M, (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ :=
      (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
    have hB_rpow :
        (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) =
          ⨆ M, (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) :=
      (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
    rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
    refine iSup_le ?_
    intro m
    rw [ENNReal.mul_iSup]
    refine iSup_le ?_
    intro n
    refine le_iSup_of_le (max m n) ?_
    exact mul_le_mul'
      (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (hαlog_int_mono (Nat.le_max_left m n)))
      (ENNReal.monotone_rpow_of_nonneg
        (sub_nonneg.mpr hθ_mem.2.le) (hβlog_int_mono (Nat.le_max_right m n)))
  have hlog_sup_le :
      (⨆ M,
        (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
        ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := by
    refine iSup_le ?_
    intro M
    exact le_iSup_of_le M (htrunc M)
  -- Route correction: once the bounded log-truncation step is isolated as `htrunc`, the rest of
  -- the argument is the deterministic monotone-convergence passage back to the full line.
  calc
    ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume = ∫⁻ z, γlog z ∂MeasureTheory.volume := by
      symm
      exact hγ_log
    _ = ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := hγlog_lintegral
    _ ≥
        ⨆ M,
          (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_sup_le
    _ ≥
        (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_diag_sup
    _ =
        (∫⁻ x, αlog x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlog y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [hαlog_lintegral, hβlog_lintegral]
    _ =
        (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [hα_log, hβ_log]

/-- The fixed-radius cutoff-log truncations induce the required multiplicative kernel on their
strict-superlevel volume profiles. -/
private lemma prekopaLeindler_real_log_cut_trunc_profile_kernel
    {α β γ : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hα_measurable : Measurable α)
    (hβ_measurable : Measurable β)
    (hγ_measurable : Measurable γ)
    (hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)))
    (M : ℕ) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    let αlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) αlog
    let βlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) βlog
    let γlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) γlog
    let αlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc αlogCut N
    let βlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc βlogCut N
    let γlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc γlogCut N
    let A : ℝ → ENNReal :=
      fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < αlogCutN M x}
    let B : ℝ → ENNReal :=
      fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < βlogCutN M y}
    let C : ℝ → ENNReal :=
      fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < γlogCutN M z}
    ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
      A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ)) := by
  dsimp
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
  let αlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) αlog
  let βlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) βlog
  let γlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) γlog
  let αlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc αlogCut N
  let βlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc βlogCut N
  let γlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc γlogCut N
  let A : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < αlogCutN M x}
  let B : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < βlogCutN M y}
  let C : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < γlogCutN M z}
  have hlog_kernel :
      ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
    intro x y
    -- The multiplicative kernel becomes additive after the logarithmic transport.
    simpa [αlog, βlog, γlog] using
      (log_profile_kernel_transport (α := α) (β := β) (γ := γ) hθ_mem hkernel_profile x y)
  have hlogCut_kernel :
      ∀ x y : ℝ, γlogCut (θ * x + (1 - θ) * y) ≥ αlogCut x ^ θ * βlogCut y ^ (1 - θ) := by
    intro x y
    by_cases hx : x < 0
    · by_cases hy : y < 0
      · have hz : θ * x + (1 - θ) * y < 0 := by
          -- Affine combinations of negative inputs stay negative.
          nlinarith [hθ_mem.1, hθ_mem.2, hx, hy]
        -- On `(-∞, 0)`, the cutoff indicators are transparent.
        simpa [αlogCut, βlogCut, γlogCut, Set.indicator, hx, hy, hz] using hlog_kernel x y
      · have hy_mem : y ∉ Set.Iio (0 : ℝ) := by simpa using hy
        have hy_zero : βlogCut y = 0 := by
          simp [βlogCut, hy_mem]
        -- If `y` leaves the cutoff half-line, the right-hand side already vanishes.
        rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hx_mem : x ∉ Set.Iio (0 : ℝ) := by simpa using hx
      have hx_zero : αlogCut x = 0 := by
        simp [αlogCut, hx_mem]
      -- Symmetrically, the first cutoff factor vanishes outside `(-∞, 0)`.
      rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  have hαlogCut_measurable : Measurable αlogCut := by
    -- The cutoff log profile is measurable because the transport and the indicator are measurable.
    simpa [αlogCut, αlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hα_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hβlogCut_measurable : Measurable βlogCut := by
    -- The same measurability argument applies to `βlogCut`.
    simpa [βlogCut, βlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hβ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hγlogCut_measurable : Measurable γlogCut := by
    -- And likewise for `γlogCut`.
    simpa [γlogCut, γlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hγ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hαlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → αlogCutN M x = 0 := by
    intro x hx
    -- Outside `[-M, M]`, the support truncation vanishes by construction.
    simpa [αlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := αlogCut) (N := M) (x := x) hx)
  have hβlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → βlogCutN M x = 0 := by
    intro x hx
    -- The same support description holds for `βlogCutN`.
    simpa [βlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := βlogCut) (N := M) (x := x) hx)
  have hγlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → γlogCutN M x = 0 := by
    intro x hx
    -- And likewise for `γlogCutN`.
    simpa [γlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := γlogCut) (N := M) (x := x) hx)
  have hlogCut_trunc_kernel :
      ∀ x y,
        γlogCutN M (θ * x + (1 - θ) * y) ≥
          αlogCutN M x ^ θ * βlogCutN M y ^ (1 - θ) := by
    intro x y
    by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
    · by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
      · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(M : ℝ)) M := by
          rcases hx with ⟨hx_left, hx_right⟩
          rcases hy with ⟨hy_left, hy_right⟩
          -- Affine combinations preserve the common truncation interval.
          constructor <;>
            nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
        -- On the common truncation interval, the support cutoffs disappear.
        simpa [αlogCutN, βlogCutN, γlogCutN, supportTrunc, hx, hy, hz] using
          hlogCut_kernel x y
      · have hy_zero : βlogCutN M y = 0 := by
          simp [βlogCutN, supportTrunc, hy]
        -- If `y` leaves the truncation window, the right-hand side already vanishes.
        rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hx_zero : αlogCutN M x = 0 := by
        simp [αlogCutN, supportTrunc, hx]
      -- Symmetrically when `x` leaves the truncation window.
      rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  -- The fixed compactly supported cutoff-log triple now fits the strict-superlevel profile kernel.
  simpa [A, B, C] using
    (compactSupport_strictSuperlevelProfile_kernel
      (a := αlogCutN M) (b := βlogCutN M) (c := γlogCutN M)
      hθ_mem (supportTrunc_measurable hαlogCut_measurable M)
      (supportTrunc_measurable hβlogCut_measurable M)
      (supportTrunc_measurable hγlogCut_measurable M)
      M hαlogCutN_support hβlogCutN_support hγlogCutN_support hlogCut_trunc_kernel)

/-- The fixed-radius cutoff-log inequality is the remaining primitive positive-profile step needed
for the bounded-value compact-support argument. -/
private lemma prekopaLeindler_real_log_cut_trunc_step
    {α β γ : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hα_measurable : Measurable α)
    (hβ_measurable : Measurable β)
    (hγ_measurable : Measurable γ)
    (hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    let αlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) αlog
    let βlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) βlog
    let γlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) γlog
    let αlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlogCut M
    let βlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlogCut M
    let γlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlogCut M
    ∀ M : ℕ,
      ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume ≥
        (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
  dsimp
  intro M
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
  let αlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) αlog
  let βlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) βlog
  let γlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) γlog
  let αlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc αlogCut N
  let βlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc βlogCut N
  let γlogCutN : ℕ → ℝ → ENNReal := fun N => supportTrunc γlogCut N
  let A : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < αlogCutN M x}
  let B : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < βlogCutN M y}
  let C : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < γlogCutN M z}
  have hαlogCut_measurable : Measurable αlogCut := by
    -- The cutoff log profile is measurable because both the transport and the indicator are.
    simpa [αlogCut, αlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hα_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hβlogCut_measurable : Measurable βlogCut := by
    -- The same measurability statement holds for `βlogCut`.
    simpa [βlogCut, βlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hβ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hγlogCut_measurable : Measurable γlogCut := by
    -- And likewise for `γlogCut`.
    simpa [γlogCut, γlog] using
      (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hγ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
  have hαlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → αlogCutN M x = 0 := by
    intro x hx
    -- Outside `[-M, M]`, the support truncation vanishes by construction.
    simpa [αlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := αlogCut) (N := M) (x := x) hx)
  have hβlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → βlogCutN M x = 0 := by
    intro x hx
    -- The same support description holds for `βlogCutN`.
    simpa [βlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := βlogCut) (N := M) (x := x) hx)
  have hγlogCutN_support :
      ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → γlogCutN M x = 0 := by
    intro x hx
    -- And likewise for `γlogCutN`.
    simpa [γlogCutN] using
      (supportTrunc_eq_zero_of_not_mem (f := γlogCut) (N := M) (x := x) hx)
  have hA_antitone : Antitone A := by
    -- The strict-superlevel volume profile of `αlogCutN M` is antitone in the threshold.
    simpa [A] using strictSuperlevelProfile_antitone (αlogCutN M)
  have hB_antitone : Antitone B := by
    -- The same monotonicity statement holds for `βlogCutN M`.
    simpa [B] using strictSuperlevelProfile_antitone (βlogCutN M)
  have hC_antitone : Antitone C := by
    -- And likewise for `γlogCutN M`.
    simpa [C] using strictSuperlevelProfile_antitone (γlogCutN M)
  have hA_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → A s < ⊤ := by
    intro s hs
    -- Positive strict superlevel sets stay inside the compact support interval `[-M, M]`.
    apply volume_lt_top_of_subset_supportInterval
    exact strictSuperlevel_subset_support hαlogCutN_support hs
  have hB_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → B t < ⊤ := by
    intro t ht
    -- The same finite-volume reduction applies to `βlogCutN M`.
    apply volume_lt_top_of_subset_supportInterval
    exact strictSuperlevel_subset_support hβlogCutN_support ht
  have hkernel_fixed :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        A s ^ θ * B t ^ (1 - θ) ≤ C (s ^ θ * t ^ (1 - θ)) := by
    -- Route correction: the fixed-`M` statement now factors through the compactly supported
    -- strict-superlevel profiles of the truncated cutoff-log functions.
    simpa [A, B, C] using
      (prekopaLeindler_real_log_cut_trunc_profile_kernel
        (α := α) (β := β) (γ := γ)
        hθ_mem hα_measurable hβ_measurable hγ_measurable hkernel_profile M)
  have hα_profile :
      ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume =
        ∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume := by
    -- Layer-cake rewrites the truncated cutoff-log integral as its strict-superlevel profile.
    simpa [A] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hαlogCut_measurable M) (f := αlogCutN M))
  have hβ_profile :
      ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume =
        ∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume := by
    -- The same layer-cake identity applies to `βlogCutN M`.
    simpa [B] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hβlogCut_measurable M) (f := βlogCutN M))
  have hγ_profile :
      ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume := by
    -- And likewise for `γlogCutN M`.
    simpa [C] using
      (ennreal_lintegral_eq_strictSuperlevelProfile
        (supportTrunc_measurable hγlogCut_measurable M) (f := γlogCutN M))
  have hcore :
      ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume ≥
        (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- The remaining analytic input is the isolated positive-profile core theorem above.
    exact prekopaLeindler_real_positive_profile_core
      hθ_mem hA_antitone hB_antitone hC_antitone hA_lt_top hB_lt_top hkernel_fixed
  calc
    ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, C r ∂MeasureTheory.volume := hγ_profile
    _ ≥
        (∫⁻ s in Set.Ioi 0, A s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, B t ∂MeasureTheory.volume) ^ (1 - θ) := hcore
    _ =
        (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [hα_profile, hβ_profile]

/-- The bounded-value compact-support Prékopa-Leindler step on `ℝ`. -/
private lemma prekopaLeindler_real_compact_support_direct_trunc_one
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (N : ℕ)
    (hf_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f x = 0)
    (hg_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g x = 0)
    (hh_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h x = 0)
    (h_kernel :
      ∀ x y : ℝ,
        h (θ * x + (1 - θ) * y) ≥ f x ^ θ * g y ^ (1 - θ)) :
    ∫⁻ z, min (1 : ENNReal) (h z) ∂MeasureTheory.volume ≥
      (∫⁻ x, min (1 : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, min (1 : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
  let α : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < f x}
  let β : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < g y}
  let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < h z}
  have hα_antitone : Antitone α := by
    -- The strict-superlevel profile of `f` is antitone in the threshold parameter.
    simpa [α] using strictSuperlevelProfile_antitone f
  have hβ_antitone : Antitone β := by
    -- The same monotonicity statement holds for `g`.
    simpa [β] using strictSuperlevelProfile_antitone g
  have hγ_antitone : Antitone γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using strictSuperlevelProfile_antitone h
  have hα_measurable : Measurable α := by
    -- Antitone real profiles are measurable.
    simpa [α] using (Antitone.measurable hα_antitone)
  have hβ_measurable : Measurable β := by
    -- The same monotonicity-to-measurability argument applies to `β`.
    simpa [β] using (Antitone.measurable hβ_antitone)
  have hγ_measurable : Measurable γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using (Antitone.measurable hγ_antitone)
  have hα_profile :
      ∫⁻ x, min (1 : ENNReal) (f x) ∂MeasureTheory.volume =
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) α r ∂MeasureTheory.volume := by
    -- Rewrite the unit truncation of `f` as the strict-superlevel profile over `(0,1)`.
    simpa [α] using ennreal_lintegral_trunc_eq_profile_trunc hf_measurable 1
  have hβ_profile :
      ∫⁻ y, min (1 : ENNReal) (g y) ∂MeasureTheory.volume =
        ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume := by
    -- The same unit-cutoff layer-cake identity holds for `g`.
    simpa [β] using ennreal_lintegral_trunc_eq_profile_trunc hg_measurable 1
  have hγ_profile :
      ∫⁻ z, min (1 : ENNReal) (h z) ∂MeasureTheory.volume =
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume := by
    -- And likewise for the target function `h`.
    simpa [γ] using ennreal_lintegral_trunc_eq_profile_trunc hh_measurable 1
  have hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t -> α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    -- Route correction: first extract the multiplicative profile kernel directly from compact
    -- support before transporting it to the cutoff log side.
    simpa [α, β, γ] using
      (compactSupport_strictSuperlevelProfile_kernel
        (a := f) (b := g) (c := h)
        hθ_mem hf_measurable hg_measurable hh_measurable N
        hf_support hg_support hh_support h_kernel)
  have h_profile :
      ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume ≥
        (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume) ^ (1 - θ) := by
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    let αlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) αlog
    let βlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) βlog
    let γlogCut : ℝ → ENNReal := Set.indicator (Set.Iio (0 : ℝ)) γlog
    have hIoo_inter_Ioi :
        Set.Ioo (0 : ℝ) 1 ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
      -- The cutoff interval `(0,1)` already lies inside the positive half-line.
      ext s
      constructor
      · intro hs
        exact hs.1
      · intro hs
        exact ⟨hs, hs.1⟩
    have hα_logCut :
        ∫⁻ x, αlogCut x ∂MeasureTheory.volume =
          ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume := by
      -- The cutoff profile on `(0,1)` is exactly the log transport supported on `(-∞,0)`.
      calc
        ∫⁻ x, αlogCut x ∂MeasureTheory.volume =
            ∫⁻ s in Set.Ioi 0, Set.indicator (Set.Ioo (0 : ℝ) 1) α s
              ∂MeasureTheory.volume := by
                simpa [αlog, αlogCut, Set.indicator, Real.exp_pos, Real.exp_lt_one_iff] using
                  (log_profile_lintegral_eq (phi := Set.indicator (Set.Ioo (0 : ℝ) 1) α)).symm
        _ = ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume := by
              simpa [MeasureTheory.lintegral_indicator, hIoo_inter_Ioi]
    have hβ_logCut :
        ∫⁻ y, βlogCut y ∂MeasureTheory.volume =
          ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume := by
      -- The same logarithmic cutoff rewrite applies to `β`.
      calc
        ∫⁻ y, βlogCut y ∂MeasureTheory.volume =
            ∫⁻ t in Set.Ioi 0, Set.indicator (Set.Ioo (0 : ℝ) 1) β t
              ∂MeasureTheory.volume := by
                simpa [βlog, βlogCut, Set.indicator, Real.exp_pos, Real.exp_lt_one_iff] using
                  (log_profile_lintegral_eq (phi := Set.indicator (Set.Ioo (0 : ℝ) 1) β)).symm
        _ = ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume := by
              simpa [MeasureTheory.lintegral_indicator, hIoo_inter_Ioi]
    have hγ_logCut :
        ∫⁻ z, γlogCut z ∂MeasureTheory.volume =
          ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume := by
      -- And likewise for the target profile `γ`.
      calc
        ∫⁻ z, γlogCut z ∂MeasureTheory.volume =
            ∫⁻ r in Set.Ioi 0, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r
              ∂MeasureTheory.volume := by
                simpa [γlog, γlogCut, Set.indicator, Real.exp_pos, Real.exp_lt_one_iff] using
                  (log_profile_lintegral_eq (phi := Set.indicator (Set.Ioo (0 : ℝ) 1) γ)).symm
        _ = ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume := by
              simpa [MeasureTheory.lintegral_indicator, hIoo_inter_Ioi]
    have hlog_kernel :
        ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
      intro x y
      -- The multiplicative profile kernel becomes additive after the logarithmic transport.
      simpa [αlog, βlog, γlog] using
        (log_profile_kernel_transport (α := α) (β := β) (γ := γ) hθ_mem hkernel_profile x y)
    have hlogCut_kernel :
        ∀ x y : ℝ, γlogCut (θ * x + (1 - θ) * y) ≥ αlogCut x ^ θ * βlogCut y ^ (1 - θ) := by
      intro x y
      by_cases hx : x < 0
      · by_cases hy : y < 0
        · have hz : θ * x + (1 - θ) * y < 0 := by
            -- Affine combinations of two negative inputs remain negative.
            nlinarith [hθ_mem.1, hθ_mem.2, hx, hy]
          -- On `(-∞,0)`, the cutoff indicators are transparent.
          simpa [αlogCut, βlogCut, γlogCut, Set.indicator, hx, hy, hz] using hlog_kernel x y
        · have hy_mem : y ∉ Set.Iio (0 : ℝ) := by simpa using hy
          have hy_zero : βlogCut y = 0 := by
            simp [βlogCut, hy_mem]
          -- If `y` leaves the cutoff half-line, the right-hand side already vanishes.
          rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
          exact bot_le
      · have hx_mem : x ∉ Set.Iio (0 : ℝ) := by simpa using hx
        have hx_zero : αlogCut x = 0 := by
          simp [αlogCut, hx_mem]
        -- Symmetrically, the first cutoff factor vanishes outside `(-∞,0)`.
        rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
        exact bot_le
    let αlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlogCut M
    let βlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlogCut M
    let γlogCutN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlogCut M
    have hαlogCut_measurable : Measurable αlogCut := by
      -- The cutoff log profile is measurable because both the transport and the indicator are.
      simpa [αlogCut, αlog] using
        (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hα_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
    have hβlogCut_measurable : Measurable βlogCut := by
      -- The same measurability statement holds for `βlogCut`.
      simpa [βlogCut, βlog] using
        (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hβ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
    have hγlogCut_measurable : Measurable γlogCut := by
      -- And likewise for `γlogCut`.
      simpa [γlogCut, γlog] using
        (((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hγ_measurable.comp Real.measurable_exp)).indicator measurableSet_Iio)
    have hαlogCutN_measurable : ∀ M, Measurable (αlogCutN M) := by
      intro M
      -- Compact support truncation preserves measurability for the cutoff `α` log profile.
      simpa [αlogCutN] using supportTrunc_measurable hαlogCut_measurable M
    have hβlogCutN_measurable : ∀ M, Measurable (βlogCutN M) := by
      intro M
      -- The same support truncation argument applies to `βlogCut`.
      simpa [βlogCutN] using supportTrunc_measurable hβlogCut_measurable M
    have hγlogCutN_measurable : ∀ M, Measurable (γlogCutN M) := by
      intro M
      -- And likewise for `γlogCutN`.
      simpa [γlogCutN] using supportTrunc_measurable hγlogCut_measurable M
    have hαlogCutN_mono : Monotone αlogCutN := by
      intro M L hML x
      -- Enlarging the compact support interval only increases the truncated cutoff profile.
      simpa [αlogCutN] using supportTrunc_mono (f := αlogCut) hML x
    have hβlogCutN_mono : Monotone βlogCutN := by
      intro M L hML y
      -- The same pointwise monotonicity holds for the `β` cutoff truncations.
      simpa [βlogCutN] using supportTrunc_mono (f := βlogCut) hML y
    have hγlogCutN_mono : Monotone γlogCutN := by
      intro M L hML z
      -- And again for the target cutoff truncations.
      simpa [γlogCutN] using supportTrunc_mono (f := γlogCut) hML z
    have hlogCut_trunc_kernel :
        ∀ M x y,
          γlogCutN M (θ * x + (1 - θ) * y) ≥
            αlogCutN M x ^ θ * βlogCutN M y ^ (1 - θ) := by
      intro M x y
      by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
      · by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
        · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(M : ℝ)) M := by
            rcases hx with ⟨hx_left, hx_right⟩
            rcases hy with ⟨hy_left, hy_right⟩
            -- Affine combinations preserve the common compact truncation interval.
            constructor <;>
              nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
          -- On the common truncation interval, the support cutoffs disappear.
          simpa [αlogCutN, βlogCutN, γlogCutN, supportTrunc, hx, hy, hz] using
            hlogCut_kernel x y
        · have hy_zero : βlogCutN M y = 0 := by
            simp [βlogCutN, supportTrunc, hy]
          -- If `y` leaves the truncation window, the right-hand side already vanishes.
          rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
          exact bot_le
      · have hx_zero : αlogCutN M x = 0 := by
          simp [αlogCutN, supportTrunc, hx]
        -- Symmetrically when `x` leaves the truncation window.
        rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
        exact bot_le
    have htrunc :
        ∀ M : ℕ,
          ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume ≥
            (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- Route correction: isolate the genuinely missing primitive theorem as a separate helper,
      -- so the current bounded-value compact-support proof only performs the local specialization.
      simpa [αlog, βlog, γlog, αlogCut, βlogCut, γlogCut, αlogCutN, βlogCutN, γlogCutN] using
        (prekopaLeindler_real_log_cut_trunc_step
          (α := α) (β := β) (γ := γ)
          hθ_mem hα_measurable hβ_measurable hγ_measurable hkernel_profile)
    have hαlogCut_lintegral :
        ∫⁻ x, αlogCut x ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume := by
      -- Monotone convergence sends the compact cutoff truncations back to the full `αlogCut`
      -- integral.
      calc
        ∫⁻ x, αlogCut x ∂MeasureTheory.volume =
            ∫⁻ x, ⨆ M, αlogCutN M x ∂MeasureTheory.volume := by
              congr with x
              simpa [αlogCutN] using (iSup_supportTrunc_apply αlogCut x).symm
        _ = ⨆ M, ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hαlogCutN_measurable hαlogCutN_mono
    have hβlogCut_lintegral :
        ∫⁻ y, βlogCut y ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume := by
      -- The same monotone-convergence rewrite applies to `βlogCut`.
      calc
        ∫⁻ y, βlogCut y ∂MeasureTheory.volume =
            ∫⁻ y, ⨆ M, βlogCutN M y ∂MeasureTheory.volume := by
              congr with y
              simpa [βlogCutN] using (iSup_supportTrunc_apply βlogCut y).symm
        _ = ⨆ M, ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hβlogCutN_measurable hβlogCutN_mono
    have hγlogCut_lintegral :
        ∫⁻ z, γlogCut z ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume := by
      -- And likewise for the target cutoff log profile.
      calc
        ∫⁻ z, γlogCut z ∂MeasureTheory.volume =
            ∫⁻ z, ⨆ M, γlogCutN M z ∂MeasureTheory.volume := by
              congr with z
              simpa [γlogCutN] using (iSup_supportTrunc_apply γlogCut z).symm
        _ = ⨆ M, ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hγlogCutN_measurable hγlogCutN_mono
    have hαlogCut_int_mono :
        Monotone (fun M => ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) := by
      intro M L hML
      -- Integral monotonicity follows from pointwise monotonicity of the truncations.
      exact MeasureTheory.lintegral_mono (fun x => hαlogCutN_mono hML x)
    have hβlogCut_int_mono :
        Monotone (fun M => ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) := by
      intro M L hML
      -- The same integral monotonicity statement holds for `βlogCut`.
      exact MeasureTheory.lintegral_mono (fun y => hβlogCutN_mono hML y)
    have hlog_diag_sup :
        (⨆ M, ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
            (⨆ M, ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) ≤
          ⨆ M,
            (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- A single large truncation index dominates any pair of compact cutoff truncations.
      have hA_rpow :
          (⨆ M, ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ =
            ⨆ M, (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ :=
        (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
      have hB_rpow :
          (⨆ M, ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) =
            ⨆ M, (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) :=
        (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
      rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
      refine iSup_le ?_
      intro m
      rw [ENNReal.mul_iSup]
      refine iSup_le ?_
      intro n
      refine le_iSup_of_le (max m n) ?_
      exact mul_le_mul'
        (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le
          (hαlogCut_int_mono (Nat.le_max_left m n)))
        (ENNReal.monotone_rpow_of_nonneg
          (sub_nonneg.mpr hθ_mem.2.le) (hβlogCut_int_mono (Nat.le_max_right m n)))
    have hlog_sup_le :
        (⨆ M,
          (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
          ⨆ M, ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume := by
      refine iSup_le ?_
      intro M
      exact le_iSup_of_le M (htrunc M)
    -- Route correction: once the finite-stage cutoff-log estimate is isolated as `htrunc`, the
    -- rest is the standard monotone-convergence diagonal passage back to the full cutoff profiles.
    calc
      ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume =
          ∫⁻ z, γlogCut z ∂MeasureTheory.volume := by
            rw [← hγ_logCut]
      _ = ⨆ M, ∫⁻ z, γlogCutN M z ∂MeasureTheory.volume := hγlogCut_lintegral
      _ ≥
          ⨆ M,
            (∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_sup_le
      _ ≥
          (⨆ M, ∫⁻ x, αlogCutN M x ∂MeasureTheory.volume) ^ θ *
            (⨆ M, ∫⁻ y, βlogCutN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_diag_sup
      _ =
          (∫⁻ x, αlogCut x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogCut y ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [hαlogCut_lintegral, hβlogCut_lintegral]
      _ =
          (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume) ^ θ *
            (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [hα_logCut, hβ_logCut]
  calc
    ∫⁻ z, min (1 : ENNReal) (h z) ∂MeasureTheory.volume =
        ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) γ r ∂MeasureTheory.volume := hγ_profile
    _ ≥
        (∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) 1) α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) 1) β t ∂MeasureTheory.volume) ^ (1 - θ) :=
        h_profile
    _ =
        (∫⁻ x, min (1 : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, min (1 : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [← hα_profile, ← hβ_profile]

/-- The bounded-value compact-support Prékopa-Leindler step on `ℝ`. -/
private lemma prekopaLeindler_real_compact_support_direct_trunc
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (N : ℕ)
    (hf_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f x = 0)
    (hg_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g x = 0)
    (hh_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h x = 0)
    (h_kernel :
      ∀ x y : ℝ,
        h (θ * x + (1 - θ) * y) ≥ f x ^ θ * g y ^ (1 - θ)) :
    ∀ n : ℕ,
      ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume ≥
        (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
  intro n
  cases n with
  | zero =>
      -- At cutoff `0`, every truncation vanishes, so the inequality is immediate.
      simp [ENNReal.zero_rpow_of_pos hθ_mem.1,
        ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2)]
  | succ m =>
      let k : ENNReal := ((Nat.succ m : ℕ) : ENNReal)
      let f1 : ℝ → ENNReal := fun x => k⁻¹ * f x
      let g1 : ℝ → ENNReal := fun y => k⁻¹ * g y
      let h1 : ℝ → ENNReal := fun z => k⁻¹ * h z
      have hk_ne_zero : k ≠ 0 := by
        dsimp [k]
        norm_num
      have hk_ne_top : k ≠ ⊤ := by
        dsimp [k]
        simp
      have hf1_measurable : Measurable f1 := by
        -- Scaling by a constant preserves measurability.
        simpa [f1] using measurable_const.mul hf_measurable
      have hg1_measurable : Measurable g1 := by
        -- The same normalization applies to `g`.
        simpa [g1] using measurable_const.mul hg_measurable
      have hh1_measurable : Measurable h1 := by
        -- And likewise for `h`.
        simpa [h1] using measurable_const.mul hh_measurable
      have hf1_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f1 x = 0 := by
        intro x hx
        -- The compact support interval is unchanged by value normalization.
        simp [f1, hf_support hx]
      have hg1_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g1 x = 0 := by
        intro x hx
        -- The same support statement holds for the normalized `g`.
        simp [g1, hg_support hx]
      have hh1_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h1 x = 0 := by
        intro x hx
        -- And likewise for the normalized target function.
        simp [h1, hh_support hx]
      have hscaled_rpow :
          ∀ x y : ℝ,
            f1 x ^ θ * g1 y ^ (1 - θ) = k⁻¹ * (f x ^ θ * g y ^ (1 - θ)) := by
        intro x y
        dsimp [f1, g1]
        have hkinv_ne_zero : k⁻¹ ≠ 0 := by
          simpa using hk_ne_top
        have hkinv_ne_top : k⁻¹ ≠ ⊤ := by
          intro htop
          exact hk_ne_zero (ENNReal.inv_eq_top.mp htop)
        -- The normalized kernel gains a single factor `k⁻¹` because the exponents sum to `1`.
        calc
          (k⁻¹ * f x) ^ θ * (k⁻¹ * g y) ^ (1 - θ) =
              (k⁻¹ ^ θ * f x ^ θ) * (k⁻¹ ^ (1 - θ) * g y ^ (1 - θ)) := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ hθ_mem.1.le,
                  ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hθ_mem.2.le)]
          _ = (k⁻¹ ^ θ * k⁻¹ ^ (1 - θ)) * (f x ^ θ * g y ^ (1 - θ)) := by
                ac_rfl
          _ = (k⁻¹ ^ (θ + (1 - θ))) * (f x ^ θ * g y ^ (1 - θ)) := by
                rw [← ENNReal.rpow_add _ _ hkinv_ne_zero hkinv_ne_top]
          _ = k⁻¹ * (f x ^ θ * g y ^ (1 - θ)) := by
                rw [show θ + (1 - θ) = 1 by ring, ENNReal.rpow_one]
      have h1_kernel :
          ∀ x y : ℝ, h1 (θ * x + (1 - θ) * y) ≥ f1 x ^ θ * g1 y ^ (1 - θ) := by
        intro x y
        -- Route correction: after normalizing the values, the kernel is preserved because the
        -- common factor `k⁻¹` distributes across the weighted geometric mean.
        calc
          h1 (θ * x + (1 - θ) * y) = k⁻¹ * h (θ * x + (1 - θ) * y) := by
              rfl
          _ ≥ k⁻¹ * (f x ^ θ * g y ^ (1 - θ)) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                mul_le_mul_right (h_kernel x y) k⁻¹
          _ = f1 x ^ θ * g1 y ^ (1 - θ) := by
              rw [hscaled_rpow]
      -- Apply the normalized unit-cutoff theorem to the rescaled triple.
      have hunit := prekopaLeindler_real_compact_support_direct_trunc_one
        (f := f1) (g := g1) (h := h1)
        hθ_mem hf1_measurable hg1_measurable hh1_measurable N
        hf1_support hg1_support hh1_support h1_kernel
      have hscale_integral (u : ℝ → ENNReal) :
          (∫⁻ z, min k (u z) ∂MeasureTheory.volume) =
            (∫⁻ z, min (1 : ENNReal) (k⁻¹ * u z) ∂MeasureTheory.volume) * k := by
        have hfun :
            (fun z => min k (u z)) =
              (fun z => min (1 : ENNReal) (k⁻¹ * u z) * k) := by
          funext z
          -- The truncation identity `min k u = k * min 1 (k⁻¹ * u)` is the exact rescaling
          -- needed to pass back from the normalized theorem.
          calc
            min k (u z) = min (1 * k) ((k⁻¹ * u z) * k) := by
              congr 1
              · simp
              · calc
                  u z = u z * k⁻¹ * k := by
                      rw [ENNReal.inv_mul_cancel_right hk_ne_zero hk_ne_top]
                  _ = (k⁻¹ * u z) * k := by
                      ac_rfl
            _ = min (1 : ENNReal) (k⁻¹ * u z) * k := by
                  simpa using (min_mul_mul_right (1 : ENNReal) (k⁻¹ * u z) k)
        rw [hfun]
        exact MeasureTheory.lintegral_mul_const' k
          (fun z => min (1 : ENNReal) (k⁻¹ * u z)) hk_ne_top
      have hk_pow :
          (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ))) * k =
            ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) * k) ^ θ *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := by
        -- The product-side rescaling is compatible with the exponents because `θ + (1 - θ) = 1`.
        calc
          (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ))) * k =
              ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ *
                (∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ)) *
                  (k ^ (θ + (1 - θ))) := by
                    rw [show k ^ (θ + (1 - θ)) = k by
                      rw [show θ + (1 - θ) = 1 by ring, ENNReal.rpow_one]]
          _ = (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) * k ^ θ) *
                (((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ)) *
                  k ^ (1 - θ)) := by
                    rw [ENNReal.rpow_add _ _ hk_ne_zero hk_ne_top]
                    ac_rfl
          _ = ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) * k) ^ θ *
                ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := by
                    rw [← ENNReal.mul_rpow_of_nonneg _ _ hθ_mem.1.le,
                      ← ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hθ_mem.2.le)]
      have hh_eq := hscale_integral h
      have hf_eq := hscale_integral f
      have hg_eq := hscale_integral g
      -- Undo the normalization on all three integrals to recover the original cutoff `k`.
      calc
        (∫⁻ z, min k (h z) ∂MeasureTheory.volume) =
            (∫⁻ z, min (1 : ENNReal) (h1 z) ∂MeasureTheory.volume) * k := by
              simpa [h1] using hh_eq
        _ ≥
            (((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) ^ θ) *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) ^ (1 - θ))) * k := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_left hunit k
        _ = ((∫⁻ x, min (1 : ENNReal) (f1 x) ∂MeasureTheory.volume) * k) ^ θ *
              ((∫⁻ y, min (1 : ENNReal) (g1 y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := hk_pow
        _ = ((∫⁻ x, min (1 : ENNReal) (k⁻¹ * f x) ∂MeasureTheory.volume) * k) ^ θ *
              ((∫⁻ y, min (1 : ENNReal) (k⁻¹ * g y) ∂MeasureTheory.volume) * k) ^ (1 - θ) := by
              rfl
        _ =
            (∫⁻ x, min k (f x) ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, min k (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [← hf_eq, ← hg_eq]

/-- The compact-support one-dimensional ENNReal Prékopa-Leindler inequality on `ℝ`, obtained by
passing from bounded-value truncations to the full functions by monotone convergence. -/
private lemma prekopaLeindler_real_compact_support_direct
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (N : ℕ)
    (hf_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f x = 0)
    (hg_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g x = 0)
    (hh_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h x = 0)
    (h_kernel :
      ∀ x y : ℝ,
        h (θ * x + (1 - θ) * y) ≥ f x ^ θ * g y ^ (1 - θ)) :
    ∫⁻ z, h z ∂MeasureTheory.volume ≥
      (∫⁻ x, f x ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, g y ∂MeasureTheory.volume) ^ (1 - θ) := by
  have htrunc :
      ∀ n : ℕ,
        ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume ≥
          (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
    intro n
    -- The direct bounded-value theorem is the only remaining localized input.
    exact prekopaLeindler_real_compact_support_direct_trunc
      hθ_mem hf_measurable hg_measurable hh_measurable N
      hf_support hg_support hh_support h_kernel n
  have hpointwise_iSup :
      ∀ (u : ℝ → ENNReal) (x : ℝ), (⨆ n : ℕ, min (n : ENNReal) (u x)) = u x := by
    intro u x
    apply le_antisymm
    · refine iSup_le ?_
      intro n
      exact min_le_right _ _
    · by_cases htop : u x = ⊤
      · simpa [htop, ENNReal.iSup_natCast]
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, (u x).toReal < n := exists_nat_gt (u x).toReal
        have hle : u x ≤ n := by
          rw [← ENNReal.toReal_le_toReal htop (by simp)]
          exact le_of_lt hn
        calc
          u x = min (n : ENNReal) (u x) := by simp [min_eq_right hle]
          _ ≤ ⨆ m : ℕ, min (m : ENNReal) (u x) := by
              exact le_iSup (fun m : ℕ => min (m : ENNReal) (u x)) n
  have hftr_measurable : ∀ n : ℕ, Measurable (fun x => min (n : ENNReal) (f x)) := by
    intro n
    -- Finite value truncation preserves measurability.
    exact measurable_const.min hf_measurable
  have hgtr_measurable : ∀ n : ℕ, Measurable (fun y => min (n : ENNReal) (g y)) := by
    intro n
    -- The same measurability statement holds for `g`.
    exact measurable_const.min hg_measurable
  have hhtr_measurable : ∀ n : ℕ, Measurable (fun z => min (n : ENNReal) (h z)) := by
    intro n
    -- And likewise for `h`.
    exact measurable_const.min hh_measurable
  have hftr_mono : Monotone (fun n : ℕ => fun x => min (n : ENNReal) (f x)) := by
    intro n m hnm x
    -- Increasing the cutoff can only increase the truncated function.
    exact min_le_min (by exact_mod_cast hnm) le_rfl
  have hgtr_mono : Monotone (fun n : ℕ => fun y => min (n : ENNReal) (g y)) := by
    intro n m hnm y
    -- The same pointwise monotonicity holds for `g`.
    exact min_le_min (by exact_mod_cast hnm) le_rfl
  have hhtr_mono : Monotone (fun n : ℕ => fun z => min (n : ENNReal) (h z)) := by
    intro n m hnm z
    -- And again for `h`.
    exact min_le_min (by exact_mod_cast hnm) le_rfl
  have hf_lintegral :
      ∫⁻ x, f x ∂MeasureTheory.volume =
        ⨆ n : ℕ, ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume := by
    -- Monotone convergence upgrades the bounded-value truncations back to `f`.
    calc
      ∫⁻ x, f x ∂MeasureTheory.volume =
          ∫⁻ x, ⨆ n : ℕ, min (n : ENNReal) (f x) ∂MeasureTheory.volume := by
            congr with x
            symm
            exact hpointwise_iSup f x
      _ = ⨆ n : ℕ, ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume := by
            exact MeasureTheory.lintegral_iSup hftr_measurable hftr_mono
  have hg_lintegral :
      ∫⁻ y, g y ∂MeasureTheory.volume =
        ⨆ n : ℕ, ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume := by
    -- The same monotone-convergence passage applies to `g`.
    calc
      ∫⁻ y, g y ∂MeasureTheory.volume =
          ∫⁻ y, ⨆ n : ℕ, min (n : ENNReal) (g y) ∂MeasureTheory.volume := by
            congr with y
            symm
            exact hpointwise_iSup g y
      _ = ⨆ n : ℕ, ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume := by
            exact MeasureTheory.lintegral_iSup hgtr_measurable hgtr_mono
  have hh_lintegral :
      ∫⁻ z, h z ∂MeasureTheory.volume =
        ⨆ n : ℕ, ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume := by
    -- And likewise for the target function `h`.
    calc
      ∫⁻ z, h z ∂MeasureTheory.volume =
          ∫⁻ z, ⨆ n : ℕ, min (n : ENNReal) (h z) ∂MeasureTheory.volume := by
            congr with z
            symm
            exact hpointwise_iSup h z
      _ = ⨆ n : ℕ, ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume := by
            exact MeasureTheory.lintegral_iSup hhtr_measurable hhtr_mono
  have hf_int_mono :
      Monotone (fun n : ℕ => ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) := by
    intro n m hnm
    -- Integral monotonicity follows from pointwise monotonicity of the truncations.
    exact MeasureTheory.lintegral_mono (fun x => hftr_mono hnm x)
  have hg_int_mono :
      Monotone (fun n : ℕ => ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) := by
    intro n m hnm
    -- The same integral monotonicity statement holds for `g`.
    exact MeasureTheory.lintegral_mono (fun y => hgtr_mono hnm y)
  have hdiag_sup :
      (⨆ n : ℕ, ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (⨆ n : ℕ, ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) ≤
        ⨆ n : ℕ,
          (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- A single truncation index dominates any pair of finite value cutoffs.
    have hA_rpow :
        (⨆ n : ℕ, ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ =
          ⨆ n : ℕ, (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ :=
      (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
    have hB_rpow :
        (⨆ n : ℕ, ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) =
          ⨆ n : ℕ, (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) :=
      (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
    rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
    refine iSup_le ?_
    intro m
    rw [ENNReal.mul_iSup]
    refine iSup_le ?_
    intro n
    refine le_iSup_of_le (max m n) ?_
    exact mul_le_mul'
      (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (hf_int_mono (Nat.le_max_left m n)))
      (ENNReal.monotone_rpow_of_nonneg
        (sub_nonneg.mpr hθ_mem.2.le) (hg_int_mono (Nat.le_max_right m n)))
  have hsup_le :
      (⨆ n : ℕ,
        (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ)) ≤
        ⨆ n : ℕ, ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume := by
    refine iSup_le ?_
    intro n
    exact le_iSup_of_le n (htrunc n)
  -- Route correction: once the bounded-value compact-support estimate is isolated, the remaining
  -- argument is the standard monotone-convergence diagonal passage back to the untruncated
  -- integrals.
  calc
    ∫⁻ z, h z ∂MeasureTheory.volume =
        ⨆ n : ℕ, ∫⁻ z, min (n : ENNReal) (h z) ∂MeasureTheory.volume := hh_lintegral
    _ ≥
        ⨆ n : ℕ,
          (∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := hsup_le
    _ ≥
        (⨆ n : ℕ, ∫⁻ x, min (n : ENNReal) (f x) ∂MeasureTheory.volume) ^ θ *
          (⨆ n : ℕ, ∫⁻ y, min (n : ENNReal) (g y) ∂MeasureTheory.volume) ^ (1 - θ) := hdiag_sup
    _ =
        (∫⁻ x, f x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, g y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [hf_lintegral, hg_lintegral]

/-- The unresolved compactly supported logarithmic-truncation step in the one-dimensional proof. -/
private lemma prekopaLeindler_real_log_profile_trunc_base
    {α β γ : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hα_measurable : Measurable α)
    (hβ_measurable : Measurable β)
    (hγ_measurable : Measurable γ)
    (hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t ->
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ))) :
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
    let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
    let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
    ∀ M : ℕ,
      ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
        (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
  dsimp
  intro M
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
  let αlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc αlog L
  let βlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc βlog L
  let γlogN : ℕ → ℝ → ENNReal := fun L => supportTrunc γlog L
  change
    ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
      (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ)
  have hlog_kernel :
      ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
    intro x y
    -- The multiplicative profile kernel becomes additive after the logarithmic transport.
    simpa [αlog, βlog, γlog] using
      (log_profile_kernel_transport (α := α) (β := β) (γ := γ) hθ_mem hkernel_profile x y)
  have hlog_trunc_kernel :
      ∀ x y,
        γlogN M (θ * x + (1 - θ) * y) ≥
          αlogN M x ^ θ * βlogN M y ^ (1 - θ) := by
    intro x y
    by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
    · by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
      · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(M : ℝ)) M := by
          rcases hx with ⟨hx_left, hx_right⟩
          rcases hy with ⟨hy_left, hy_right⟩
          -- The affine combination of two points in `[-M, M]` stays in `[-M, M]`.
          constructor <;>
            nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
        -- On the common truncation interval, the support cutoffs disappear.
        simpa [αlogN, βlogN, γlogN, supportTrunc, hx, hy, hz] using hlog_kernel x y
      · have hy_zero : βlogN M y = 0 := by
          simp [βlogN, supportTrunc, hy]
        -- If `y` lies outside the truncation window, the right-hand side already vanishes.
        rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hx_zero : αlogN M x = 0 := by
        simp [αlogN, supportTrunc, hx]
      -- And symmetrically when `x` leaves the truncation window.
      rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  have hαlog_measurable : Measurable αlog := by
    -- The logarithmic transport is measurable because both `exp` and `α` are measurable.
    simpa [αlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hα_measurable.comp Real.measurable_exp))
  have hβlog_measurable : Measurable βlog := by
    -- The same change-of-variables measurability statement holds for `βlog`.
    simpa [βlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hβ_measurable.comp Real.measurable_exp))
  have hγlog_measurable : Measurable γlog := by
    -- And again for `γlog`.
    simpa [γlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hγ_measurable.comp Real.measurable_exp))
  have hαlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → αlogN M x = 0 := by
    intro x hx
    -- Outside `[-M, M]`, the truncation of `αlog` vanishes by construction.
    simpa [αlogN] using (supportTrunc_eq_zero_of_not_mem (f := αlog) (N := M) (x := x) hx)
  have hβlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → βlogN M x = 0 := by
    intro x hx
    -- The same support cutoff description holds for `βlog`.
    simpa [βlogN] using (supportTrunc_eq_zero_of_not_mem (f := βlog) (N := M) (x := x) hx)
  have hγlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(M : ℝ)) M → γlogN M x = 0 := by
    intro x hx
    -- And likewise for `γlog`.
    simpa [γlogN] using (supportTrunc_eq_zero_of_not_mem (f := γlog) (N := M) (x := x) hx)
  -- Route correction: the target now reduces to the earlier compact-support line theorem instead
  -- of re-entering the recursive logarithmic profile machinery.
  simpa [αlog, βlog, γlog, αlogN, βlogN, γlogN] using
    (prekopaLeindler_real_compact_support_direct
      (f := αlogN M) (g := βlogN M) (h := γlogN M)
      hθ_mem (supportTrunc_measurable hαlog_measurable M)
      (supportTrunc_measurable hβlog_measurable M)
      (supportTrunc_measurable hγlog_measurable M)
      M hαlogN_support hβlogN_support hγlogN_support hlog_trunc_kernel)

/-- The unresolved compactly supported logarithmic-truncation step in the one-dimensional proof. -/
private lemma prekopaLeindler_real_compact_support_aux
    {f g h : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (N : ℕ)
    (hf_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → f x = 0)
    (hg_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → g x = 0)
    (hh_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → h x = 0)
    (h_kernel :
      ∀ x y : ℝ,
        h (θ * x + (1 - θ) * y) ≥ f x ^ θ * g y ^ (1 - θ)) :
    ∫⁻ z, h z ∂MeasureTheory.volume ≥
      (∫⁻ x, f x ∂MeasureTheory.volume) ^ θ *
        (∫⁻ y, g y ∂MeasureTheory.volume) ^ (1 - θ) := by
  let α : ℝ → ENNReal := fun s => MeasureTheory.volume {x : ℝ | ENNReal.ofReal s < f x}
  let β : ℝ → ENNReal := fun t => MeasureTheory.volume {y : ℝ | ENNReal.ofReal t < g y}
  let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < h z}
  have hα_antitone : Antitone α := by
    -- The strict-superlevel profile of `f` is antitone in the threshold parameter.
    simpa [α] using strictSuperlevelProfile_antitone f
  have hβ_antitone : Antitone β := by
    -- The same monotonicity statement holds for `g`.
    simpa [β] using strictSuperlevelProfile_antitone g
  have hγ_antitone : Antitone γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using strictSuperlevelProfile_antitone h
  have hα_measurable : Measurable α := by
    -- Antitone real profiles are measurable.
    simpa [α] using (Antitone.measurable hα_antitone)
  have hβ_measurable : Measurable β := by
    -- The same monotonicity-to-measurability argument applies to `β`.
    simpa [β] using (Antitone.measurable hβ_antitone)
  have hγ_measurable : Measurable γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using (Antitone.measurable hγ_antitone)
  have hα_profile :
      ∫⁻ x, f x ∂MeasureTheory.volume =
        ∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume := by
    -- The layer-cake identity rewrites the `f`-integral in terms of its strict-superlevel
    -- profile.
    simpa [α] using ennreal_lintegral_eq_strictSuperlevelProfile hf_measurable (f := f)
  have hβ_profile :
      ∫⁻ y, g y ∂MeasureTheory.volume =
        ∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume := by
    -- The same strict-superlevel formula applies to `g`.
    simpa [β] using ennreal_lintegral_eq_strictSuperlevelProfile hg_measurable (f := g)
  have hγ_profile :
      ∫⁻ z, h z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := by
    -- And likewise for the target function `h`.
    simpa [γ] using ennreal_lintegral_eq_strictSuperlevelProfile hh_measurable (f := h)
  have hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t → α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    -- Route correction: instead of re-entering the recursive logarithmic transport, first extract
    -- the exact strict-superlevel kernel that already follows from compact support on the source
    -- side.
    simpa [α, β, γ] using
      (compactSupport_strictSuperlevelProfile_kernel
        (a := f) (b := g) (c := h)
        hθ_mem hf_measurable hg_measurable hh_measurable N
        hf_support hg_support hh_support h_kernel)
  have h_profile :
      ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume ≥
        (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := by
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    have hα_log :
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
          ∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume := by
      -- The `f`-profile over `Set.Ioi 0` is exactly the full-line integral of its log transport.
      simpa [αlog] using (log_profile_lintegral_eq (phi := α)).symm
    have hβ_log :
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
          ∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume := by
      -- The same logarithmic change of variables applies to `β`.
      simpa [βlog] using (log_profile_lintegral_eq (phi := β)).symm
    have hγ_log :
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
          ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := by
      -- And likewise for the target profile `γ`.
      simpa [γlog] using (log_profile_lintegral_eq (phi := γ)).symm
    have hlog_kernel :
        ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
      intro x y
      -- Route correction: the multiplicative profile kernel becomes additive after the logarithmic
      -- transport `r = exp x`.
      simpa [αlog, βlog, γlog] using
        (log_profile_kernel_transport (α := α) (β := β) (γ := γ) hθ_mem hkernel_profile x y)
    let αlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc αlog M
    let βlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc βlog M
    let γlogN : ℕ → ℝ → ENNReal := fun M => supportTrunc γlog M
    have hαlog_measurable : Measurable αlog := by
      -- The logarithmic transport is measurable because both `exp` and `α` are measurable.
      simpa [αlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hα_measurable.comp Real.measurable_exp))
    have hβlog_measurable : Measurable βlog := by
      -- The same change-of-variables measurability statement holds for `βlog`.
      simpa [βlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hβ_measurable.comp Real.measurable_exp))
    have hγlog_measurable : Measurable γlog := by
      -- And again for `γlog`.
      simpa [γlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hγ_measurable.comp Real.measurable_exp))
    have hαlogN_measurable : ∀ M, Measurable (αlogN M) := by
      intro M
      -- Compact support truncation preserves measurability for the transported `α`-profile.
      simpa [αlogN] using supportTrunc_measurable hαlog_measurable M
    have hβlogN_measurable : ∀ M, Measurable (βlogN M) := by
      intro M
      -- The same support truncation argument applies to `βlog`.
      simpa [βlogN] using supportTrunc_measurable hβlog_measurable M
    have hγlogN_measurable : ∀ M, Measurable (γlogN M) := by
      intro M
      -- And likewise for `γlog`.
      simpa [γlogN] using supportTrunc_measurable hγlog_measurable M
    have hαlogN_mono : Monotone αlogN := by
      intro M L hML x
      -- Enlarging the compact truncation interval only increases the truncated `αlog` profile.
      simpa [αlogN] using supportTrunc_mono (f := αlog) hML x
    have hβlogN_mono : Monotone βlogN := by
      intro M L hML y
      -- The same pointwise monotonicity holds for the `βlog` truncations.
      simpa [βlogN] using supportTrunc_mono (f := βlog) hML y
    have hγlogN_mono : Monotone γlogN := by
      intro M L hML z
      -- And again for the target `γlog` truncations.
      simpa [γlogN] using supportTrunc_mono (f := γlog) hML z
    have hlog_trunc_kernel :
        ∀ M x y,
          γlogN M (θ * x + (1 - θ) * y) ≥
            αlogN M x ^ θ * βlogN M y ^ (1 - θ) := by
      intro M x y
      by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
      · by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
        · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(M : ℝ)) M := by
            rcases hx with ⟨hx_left, hx_right⟩
            rcases hy with ⟨hy_left, hy_right⟩
            -- The affine combination of two points in `[-M, M]` stays in `[-M, M]`.
            constructor <;>
              nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
          -- On the common compact support interval, the truncations are transparent.
          simpa [αlogN, βlogN, γlogN, supportTrunc, hx, hy, hz] using hlog_kernel x y
        · have hy_zero : βlogN M y = 0 := by
            simp [βlogN, supportTrunc, hy]
          -- If `y` leaves the truncation window, the right-hand side already vanishes.
          rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
          exact bot_le
      · have hx_zero : αlogN M x = 0 := by
          simp [αlogN, supportTrunc, hx]
        -- Symmetrically when `x` leaves the truncation window.
        rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
        exact bot_le
    have htrunc :
        ∀ M : ℕ,
          ∫⁻ z, γlogN M z ∂MeasureTheory.volume ≥
            (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- Route correction: the target theorem no longer contains the unresolved analytic base
      -- step inline; it now delegates to the isolated bounded log-truncation helper above.
      simpa [αlog, βlog, γlog, αlogN, βlogN, γlogN] using
        (prekopaLeindler_real_log_profile_trunc_base
          (α := α) (β := β) (γ := γ)
          hθ_mem hα_measurable hβ_measurable hγ_measurable hkernel_profile)
    have hαlog_lintegral :
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume := by
      -- Monotone convergence sends the compact log truncations back to the full `αlog` integral.
      calc
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
            ∫⁻ x, ⨆ M, αlogN M x ∂MeasureTheory.volume := by
              congr with x
              simpa [αlogN] using (iSup_supportTrunc_apply αlog x).symm
        _ = ⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hαlogN_measurable hαlogN_mono
    have hβlog_lintegral :
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume := by
      -- The same monotone-convergence rewrite applies to `βlog`.
      calc
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
            ∫⁻ y, ⨆ M, βlogN M y ∂MeasureTheory.volume := by
              congr with y
              simpa [βlogN] using (iSup_supportTrunc_apply βlog y).symm
        _ = ⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hβlogN_measurable hβlogN_mono
    have hγlog_lintegral :
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
          ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := by
      -- And likewise for the target `γlog`.
      calc
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
            ∫⁻ z, ⨆ M, γlogN M z ∂MeasureTheory.volume := by
              congr with z
              simpa [γlogN] using (iSup_supportTrunc_apply γlog z).symm
        _ = ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hγlogN_measurable hγlogN_mono
    have hαlog_int_mono :
        Monotone (fun M => ∫⁻ x, αlogN M x ∂MeasureTheory.volume) := by
      intro M L hML
      -- Integral monotonicity follows from pointwise monotonicity of the truncations.
      exact MeasureTheory.lintegral_mono (fun x => hαlogN_mono hML x)
    have hβlog_int_mono :
        Monotone (fun M => ∫⁻ y, βlogN M y ∂MeasureTheory.volume) := by
      intro M L hML
      -- The same integral monotonicity statement holds for `βlog`.
      exact MeasureTheory.lintegral_mono (fun y => hβlogN_mono hML y)
    have hlog_diag_sup :
        (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) ≤
          ⨆ M,
            (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- A single large truncation index dominates any pair of compact log truncations.
      have hA_rpow :
          (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ =
            ⨆ M, (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ :=
        (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
      have hB_rpow :
          (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) =
            ⨆ M, (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) :=
        (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
      rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
      refine iSup_le ?_
      intro m
      rw [ENNReal.mul_iSup]
      refine iSup_le ?_
      intro n
      refine le_iSup_of_le (max m n) ?_
      exact mul_le_mul'
        (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (hαlog_int_mono (Nat.le_max_left m n)))
        (ENNReal.monotone_rpow_of_nonneg
          (sub_nonneg.mpr hθ_mem.2.le) (hβlog_int_mono (Nat.le_max_right m n)))
    have hlog_sup_le :
        (⨆ M,
          (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
          ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := by
      refine iSup_le ?_
      intro M
      exact le_iSup_of_le M (htrunc M)
    -- Route correction: once the bounded log-truncation step is isolated as `htrunc`, the rest of
    -- the argument is the deterministic monotone-convergence passage back to the full line.
    calc
      ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume = ∫⁻ z, γlog z ∂MeasureTheory.volume := by
        symm
        exact hγ_log
      _ = ⨆ M, ∫⁻ z, γlogN M z ∂MeasureTheory.volume := hγlog_lintegral
      _ ≥
          ⨆ M,
            (∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_sup_le
      _ ≥
          (⨆ M, ∫⁻ x, αlogN M x ∂MeasureTheory.volume) ^ θ *
            (⨆ M, ∫⁻ y, βlogN M y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_diag_sup
      _ =
          (∫⁻ x, αlog x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlog y ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [hαlog_lintegral, hβlog_lintegral]
      _ =
          (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
            (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [hα_log, hβ_log]
  calc
    ∫⁻ z, h z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := hγ_profile
    _ ≥
        (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := h_profile
    _ =
        (∫⁻ x, f x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, g y ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [← hα_profile, ← hβ_profile]

/-- The unresolved compactly supported logarithmic-truncation step in the one-dimensional proof. -/
private lemma prekopaLeindler_real_log_trunc_step
    {a b c : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (ha_measurable : Measurable a)
    (hb_measurable : Measurable b)
    (hc_measurable : Measurable c)
    (K : ℕ)
    (ha_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(K : ℝ)) K → a x = 0)
    (hb_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(K : ℝ)) K → b x = 0)
    (hc_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(K : ℝ)) K → c x = 0)
    (h_kernel :
      ∀ u v : ℝ,
        c (θ * u + (1 - θ) * v) ≥ a u ^ θ * b v ^ (1 - θ)) :
    let α : ℝ → ENNReal := fun s => MeasureTheory.volume {u : ℝ | ENNReal.ofReal s < a u}
    let β : ℝ → ENNReal := fun t => MeasureTheory.volume {v : ℝ | ENNReal.ofReal t < b v}
    let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < c z}
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    let αlogN : ℕ → ℝ → ENNReal := fun N => supportTrunc αlog N
    let βlogN : ℕ → ℝ → ENNReal := fun N => supportTrunc βlog N
    let γlogN : ℕ → ℝ → ENNReal := fun N => supportTrunc γlog N
    ∀ N : ℕ,
      ∫⁻ z, γlogN N z ∂MeasureTheory.volume ≥
        (∫⁻ x, αlogN N x ∂MeasureTheory.volume) ^ θ *
          (∫⁻ y, βlogN N y ∂MeasureTheory.volume) ^ (1 - θ) := by
  -- Route correction: the missing work is no longer the whole log-profile argument. The target
  -- now follows from an explicit profile-kernel construction plus the single compact-support base
  -- case isolated above.
  dsimp
  intro N
  let α : ℝ → ENNReal := fun s => MeasureTheory.volume {u : ℝ | ENNReal.ofReal s < a u}
  let β : ℝ → ENNReal := fun t => MeasureTheory.volume {v : ℝ | ENNReal.ofReal t < b v}
  let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < c z}
  let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
  let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
  let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
  let αlogN : ℕ → ℝ → ENNReal := fun N => supportTrunc αlog N
  let βlogN : ℕ → ℝ → ENNReal := fun N => supportTrunc βlog N
  let γlogN : ℕ → ℝ → ENNReal := fun N => supportTrunc γlog N
  have hα_measurableSet : ∀ s : ℝ, MeasurableSet {u : ℝ | ENNReal.ofReal s < a u} := by
    intro s
    -- Strict superlevel sets of a measurable ENNReal-valued function are measurable.
    exact measurableSet_lt measurable_const ha_measurable
  have hβ_measurableSet : ∀ t : ℝ, MeasurableSet {v : ℝ | ENNReal.ofReal t < b v} := by
    intro t
    -- The same measurability statement holds for `b`.
    exact measurableSet_lt measurable_const hb_measurable
  have hγ_measurableSet : ∀ r : ℝ, MeasurableSet {z : ℝ | ENNReal.ofReal r < c z} := by
    intro r
    -- And likewise for `c`.
    exact measurableSet_lt measurable_const hc_measurable
  have hα_subset : ∀ ⦃s : ℝ⦄, 0 < s →
      {u : ℝ | ENNReal.ofReal s < a u} ⊆ Set.Icc (-(K : ℝ)) K := by
    intro s hs
    -- Positive strict superlevel sets cannot escape the bounded support of `a`.
    exact strictSuperlevel_subset_support ha_support hs
  have hβ_subset : ∀ ⦃t : ℝ⦄, 0 < t →
      {v : ℝ | ENNReal.ofReal t < b v} ⊆ Set.Icc (-(K : ℝ)) K := by
    intro t ht
    -- The same bounded-support reduction applies to `b`.
    exact strictSuperlevel_subset_support hb_support ht
  have hγ_subset : ∀ ⦃r : ℝ⦄, 0 < r →
      {z : ℝ | ENNReal.ofReal r < c z} ⊆ Set.Icc (-(K : ℝ)) K := by
    intro r hr
    -- And again for the target function `c`.
    exact strictSuperlevel_subset_support hc_support hr
  have h_superlevel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
          ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z}
          ⊆ {z : ℝ | ENNReal.ofReal (s ^ θ * t ^ (1 - θ)) < c z} := by
    intro s t hs ht
    -- The pointwise kernel sends positive superlevel pairs into the target superlevel set.
    exact real_superlevel_affine_subset hθ_mem h_kernel hs ht
  have hα_antitone : Antitone α := by
    -- The `a`-profile is exactly a strict-superlevel volume profile.
    simpa [α] using strictSuperlevelProfile_antitone a
  have hβ_antitone : Antitone β := by
    -- The same monotonicity statement holds for `b`.
    simpa [β] using strictSuperlevelProfile_antitone b
  have hγ_antitone : Antitone γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using strictSuperlevelProfile_antitone c
  have hα_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → α s < ⊤ := by
    intro s hs
    -- Positive `a`-superlevel sets lie inside the bounded support interval.
    exact volume_lt_top_of_subset_supportInterval (hα_subset hs)
  have hβ_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → β t < ⊤ := by
    intro t ht
    -- The same finite-volume reduction applies to `β`.
    exact volume_lt_top_of_subset_supportInterval (hβ_subset ht)
  have h_source_le_target :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        MeasureTheory.volume {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
          ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z} ≤
            γ (s ^ θ * t ^ (1 - θ)) := by
    intro s t hs ht
    -- The superlevel-set inclusion upgrades immediately to a volume bound.
    simpa [γ] using MeasureTheory.measure_mono (h_superlevel hs ht)
  have h_pointwise_from_arith :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        ENNReal.ofReal (θ * (α s).toReal + (1 - θ) * (β t).toReal) ≤
          MeasureTheory.volume {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
            ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z} →
          α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    intro s t hs ht h_arith
    -- First use weighted AM-GM on the finite profile values, then pass through the affine-image
    -- volume lower bound and the superlevel-set inclusion.
    exact le_trans
      (le_trans
        (ennreal_geomMean_le_ofReal_weighted_toReal_sum hθ_mem (hα_lt_top hs) (hβ_lt_top ht))
        h_arith)
      (h_source_le_target hs ht)
  have h_source_eq_scaled_sumset :
      ∀ ⦃s t : ℝ⦄,
        {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
          ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z} =
            Set.image2 (fun x y : ℝ => x + y)
              ((fun u : ℝ => θ * u) '' {u : ℝ | ENNReal.ofReal s < a u})
              ((fun v : ℝ => (1 - θ) * v) '' {v : ℝ | ENNReal.ofReal t < b v}) := by
    intro s t
    -- Rewrite the affine source set as an additive scaled sumset.
    simpa using
      (real_affine_image_eq_image2_add
        (S := {u : ℝ | ENNReal.ofReal s < a u})
        (T := {v : ℝ | ENNReal.ofReal t < b v})
        (θ := θ))
  have hkernel_profile :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
    intro s t hs ht
    by_cases hS_nonempty : ({u : ℝ | ENNReal.ofReal s < a u} : Set ℝ).Nonempty
    · by_cases hT_nonempty : ({v : ℝ | ENNReal.ofReal t < b v} : Set ℝ).Nonempty
      · have h_arith :
          ENNReal.ofReal (θ * (α s).toReal + (1 - θ) * (β t).toReal) ≤
            MeasureTheory.volume {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
              ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z} := by
          -- Apply the one-dimensional scaled-sumset bound to the two positive strict superlevel
          -- sets and then rewrite the resulting source set back to the affine image.
          simpa [α, β, h_source_eq_scaled_sumset] using
            (real_scaled_sumset_volume_lower_bound_of_nonempty
              (S := {u : ℝ | ENNReal.ofReal s < a u})
              (T := {v : ℝ | ENNReal.ofReal t < b v})
              (K := K) (θ := θ)
              (hS_meas := hα_measurableSet s)
              (hT_meas := hβ_measurableSet t)
              (hS_sub := hα_subset hs)
              (hT_sub := hβ_subset ht)
              (hS_nonempty := hS_nonempty)
              (hT_nonempty := hT_nonempty)
              hθ_mem)
        exact h_pointwise_from_arith hs ht h_arith
      · have hT_empty : ({v : ℝ | ENNReal.ofReal t < b v} : Set ℝ) = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hT_nonempty
        have hβ_zero : β t = 0 := by
          simp [β, hT_empty]
        -- If the second positive superlevel set is empty, the geometric-mean side vanishes.
        rw [hβ_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hS_empty : ({u : ℝ | ENNReal.ofReal s < a u} : Set ℝ) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hS_nonempty
      have hα_zero : α s = 0 := by
        simp [α, hS_empty]
      -- Symmetrically, an empty first superlevel set forces the profile kernel to be trivial.
      rw [hα_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  have hα_measurable : Measurable α := by
    -- Antitone real profiles are measurable.
    simpa [α] using (Antitone.measurable hα_antitone)
  have hβ_measurable : Measurable β := by
    -- The same monotonicity-to-measurability argument applies to `β`.
    simpa [β] using (Antitone.measurable hβ_antitone)
  have hγ_measurable : Measurable γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using (Antitone.measurable hγ_antitone)
  have hαlog_measurable : Measurable αlog := by
    -- The logarithmic transport is measurable because both `exp` and the profile are measurable.
    simpa [αlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hα_measurable.comp Real.measurable_exp))
  have hβlog_measurable : Measurable βlog := by
    -- The same change-of-variables measurability statement holds for `βlog`.
    simpa [βlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hβ_measurable.comp Real.measurable_exp))
  have hγlog_measurable : Measurable γlog := by
    -- And again for `γlog`.
    simpa [γlog] using
      ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
        (hγ_measurable.comp Real.measurable_exp))
  have hlog_kernel :
      ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
    intro x y
    -- Transport the multiplicative profile kernel through the logarithmic change of variables.
    simpa [αlog, βlog, γlog] using
      (log_profile_kernel_transport (α := α) (β := β) (γ := γ) hθ_mem hkernel_profile x y)
  have hlog_trunc_kernel :
      ∀ N x y,
        γlogN N (θ * x + (1 - θ) * y) ≥
          αlogN N x ^ θ * βlogN N y ^ (1 - θ) := by
    intro M x y
    by_cases hx : x ∈ Set.Icc (-(M : ℝ)) M
    · by_cases hy : y ∈ Set.Icc (-(M : ℝ)) M
      · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(M : ℝ)) M := by
          rcases hx with ⟨hx_left, hx_right⟩
          rcases hy with ⟨hy_left, hy_right⟩
          -- The affine combination of two points in the truncation interval stays in the interval.
          constructor <;> nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
        -- On the common truncation interval, the support cutoffs disappear.
        simpa [αlogN, βlogN, γlogN, supportTrunc, hx, hy, hz] using hlog_kernel x y
      · have hy_zero : βlogN M y = 0 := by
          simp [βlogN, supportTrunc, hy]
        -- If `y` lies outside the truncation window, the right-hand side already vanishes.
        rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · have hx_zero : αlogN M x = 0 := by
        simp [αlogN, supportTrunc, hx]
      -- Symmetrically, the first truncated factor vanishes outside its support.
      rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  have hαlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → αlogN N x = 0 := by
    intro x hx
    -- Outside `[-N, N]`, the truncation of `αlog` vanishes by construction.
    simpa [αlogN] using (supportTrunc_eq_zero_of_not_mem (f := αlog) (N := N) (x := x) hx)
  have hβlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → βlogN N x = 0 := by
    intro x hx
    -- The same support cutoff description holds for `βlog`.
    simpa [βlogN] using (supportTrunc_eq_zero_of_not_mem (f := βlog) (N := N) (x := x) hx)
  have hγlogN_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → γlogN N x = 0 := by
    intro x hx
    -- And likewise for `γlog`.
    simpa [γlogN] using (supportTrunc_eq_zero_of_not_mem (f := γlog) (N := N) (x := x) hx)
  -- The target is now exactly the compact-support base case applied to the truncated log profiles.
  simpa [α, β, γ, αlog, βlog, γlog, αlogN, βlogN, γlogN] using
    (prekopaLeindler_real_compact_support_aux
      (f := αlogN N) (g := βlogN N) (h := γlogN N)
      hθ_mem (supportTrunc_measurable hαlog_measurable N)
      (supportTrunc_measurable hβlog_measurable N)
      (supportTrunc_measurable hγlog_measurable N)
      N hαlogN_support hβlogN_support hγlogN_support (hlog_trunc_kernel N))

/-- The bounded-support one-dimensional strict core is the remaining localized analytic input. -/
private lemma prekopaLeindler_real_strict_lintegral_core_bounded
    {a b c : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (ha_measurable : Measurable a)
    (hb_measurable : Measurable b)
    (hc_measurable : Measurable c)
    (N : ℕ)
    (ha_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → a x = 0)
    (hb_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → b x = 0)
    (hc_support : ∀ ⦃x : ℝ⦄, x ∉ Set.Icc (-(N : ℝ)) N → c x = 0)
    (h_kernel :
      ∀ u v : ℝ,
        c (θ * u + (1 - θ) * v) ≥ a u ^ θ * b v ^ (1 - θ)) :
    ∫⁻ z, c z ∂MeasureTheory.volume ≥
      (∫⁻ u, a u ∂MeasureTheory.volume) ^ θ *
        (∫⁻ v, b v ∂MeasureTheory.volume) ^ (1 - θ) := by
  let α : ℝ → ENNReal := fun s => MeasureTheory.volume {u : ℝ | ENNReal.ofReal s < a u}
  let β : ℝ → ENNReal := fun t => MeasureTheory.volume {v : ℝ | ENNReal.ofReal t < b v}
  let γ : ℝ → ENNReal := fun r => MeasureTheory.volume {z : ℝ | ENNReal.ofReal r < c z}
  have hα_measurableSet : ∀ s : ℝ, MeasurableSet {u : ℝ | ENNReal.ofReal s < a u} := by
    intro s
    -- Strict superlevel sets of a measurable ENNReal-valued function are measurable.
    exact measurableSet_lt measurable_const ha_measurable
  have hβ_measurableSet : ∀ t : ℝ, MeasurableSet {v : ℝ | ENNReal.ofReal t < b v} := by
    intro t
    -- The same measurability statement holds for `b`.
    exact measurableSet_lt measurable_const hb_measurable
  have hγ_measurableSet : ∀ r : ℝ, MeasurableSet {z : ℝ | ENNReal.ofReal r < c z} := by
    intro r
    -- And likewise for `c`.
    exact measurableSet_lt measurable_const hc_measurable
  have hα_subset : ∀ ⦃s : ℝ⦄, 0 < s →
      {u : ℝ | ENNReal.ofReal s < a u} ⊆ Set.Icc (-(N : ℝ)) N := by
    intro s hs
    -- Positive strict superlevel sets cannot escape the bounded support of `a`.
    exact strictSuperlevel_subset_support ha_support hs
  have hβ_subset : ∀ ⦃t : ℝ⦄, 0 < t →
      {v : ℝ | ENNReal.ofReal t < b v} ⊆ Set.Icc (-(N : ℝ)) N := by
    intro t ht
    -- The same bounded-support reduction applies to `b`.
    exact strictSuperlevel_subset_support hb_support ht
  have hγ_subset : ∀ ⦃r : ℝ⦄, 0 < r →
      {z : ℝ | ENNReal.ofReal r < c z} ⊆ Set.Icc (-(N : ℝ)) N := by
    intro r hr
    -- And again for the target function `c`.
    exact strictSuperlevel_subset_support hc_support hr
  have h_superlevel :
      ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
        {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
          ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z}
          ⊆ {z : ℝ | ENNReal.ofReal (s ^ θ * t ^ (1 - θ)) < c z} := by
    intro s t hs ht
    -- Route correction: instead of searching for a ready-made Brunn-Minkowski theorem first,
    -- extract the exact strict superlevel-set inclusion directly from the pointwise kernel.
    exact real_superlevel_affine_subset hθ_mem h_kernel hs ht
  have hα_antitone : Antitone α := by
    -- The `a`-profile is exactly a strict-superlevel volume profile.
    simpa [α] using strictSuperlevelProfile_antitone a
  have hβ_antitone : Antitone β := by
    -- The same monotonicity statement holds for `b`.
    simpa [β] using strictSuperlevelProfile_antitone b
  have hγ_antitone : Antitone γ := by
    -- And likewise for the target profile `γ`.
    simpa [γ] using strictSuperlevelProfile_antitone c
  have hα_lt_top : ∀ ⦃s : ℝ⦄, 0 < s → α s < ⊤ := by
    intro s hs
    -- Positive `a`-superlevel sets sit inside the bounded support interval, hence have finite
    -- volume.
    exact volume_lt_top_of_subset_supportInterval (hα_subset hs)
  have hβ_lt_top : ∀ ⦃t : ℝ⦄, 0 < t → β t < ⊤ := by
    intro t ht
    -- The same finite-volume reduction applies to `β`.
    exact volume_lt_top_of_subset_supportInterval (hβ_subset ht)
  have hγ_lt_top : ∀ ⦃r : ℝ⦄, 0 < r → γ r < ⊤ := by
    intro r hr
    -- And again for the target profile `γ`.
    exact volume_lt_top_of_subset_supportInterval (hγ_subset hr)
  have hα_trunc :
      ∀ n : ℕ,
        ∫⁻ u, min (n : ENNReal) (a u) ∂MeasureTheory.volume =
          ∫⁻ s, Set.indicator (Set.Ioo (0 : ℝ) n) α s ∂MeasureTheory.volume := by
    intro n
    -- The truncated layer-cake identity rewrites the `a`-integral as its strict-superlevel
    -- profile on the positive half-line up to level `n`.
    simpa [α] using ennreal_lintegral_trunc_eq_profile_trunc ha_measurable n
  have hβ_trunc :
      ∀ n : ℕ,
        ∫⁻ v, min (n : ENNReal) (b v) ∂MeasureTheory.volume =
          ∫⁻ t, Set.indicator (Set.Ioo (0 : ℝ) n) β t ∂MeasureTheory.volume := by
    intro n
    -- The same truncation rewrite applies to `b`.
    simpa [β] using ennreal_lintegral_trunc_eq_profile_trunc hb_measurable n
  have hγ_trunc :
      ∀ n : ℕ,
        ∫⁻ z, min (n : ENNReal) (c z) ∂MeasureTheory.volume =
          ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) n) γ r ∂MeasureTheory.volume := by
    intro n
    -- And likewise for the target profile `γ`.
    simpa [γ] using ennreal_lintegral_trunc_eq_profile_trunc hc_measurable n
  have hα_profile :
      ∫⁻ u, a u ∂MeasureTheory.volume =
        ∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume := by
    -- Collapse the truncation identities into the full strict-superlevel profile formula.
    simpa [α] using ennreal_lintegral_eq_strictSuperlevelProfile ha_measurable (f := a)
  have hβ_profile :
      ∫⁻ v, b v ∂MeasureTheory.volume =
        ∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume := by
    -- The same layer-cake reduction applies to `b`.
    simpa [β] using ennreal_lintegral_eq_strictSuperlevelProfile hb_measurable (f := b)
  have hγ_profile :
      ∫⁻ z, c z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := by
    -- And likewise for the target function `c`.
    simpa [γ] using ennreal_lintegral_eq_strictSuperlevelProfile hc_measurable (f := c)
  have h_profile :
      ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume ≥
        (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := by
    have h_source_le_target :
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          MeasureTheory.volume {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
            ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z} ≤
              γ (s ^ θ * t ^ (1 - θ)) := by
      intro s t hs ht
      -- The superlevel-set inclusion from the kernel immediately upgrades to a volume bound.
      simpa [γ] using MeasureTheory.measure_mono (h_superlevel hs ht)
    have h_pointwise_from_arith :
        ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          ENNReal.ofReal (θ * (α s).toReal + (1 - θ) * (β t).toReal) ≤
            MeasureTheory.volume {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
              ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z} →
            α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ)) := by
      intro s t hs ht h_arith
      -- First use weighted AM-GM on the finite profile values, then pass through the affine-image
      -- volume lower bound and finally the superlevel-set inclusion.
      exact le_trans
        (le_trans
          (ennreal_geomMean_le_ofReal_weighted_toReal_sum hθ_mem (hα_lt_top hs) (hβ_lt_top ht))
          h_arith)
        (h_source_le_target hs ht)
    have h_source_eq_scaled_sumset :
        ∀ ⦃s t : ℝ⦄,
          {z : ℝ | ∃ u, ENNReal.ofReal s < a u ∧
            ∃ v, ENNReal.ofReal t < b v ∧ θ * u + (1 - θ) * v = z} =
              Set.image2 (fun x y : ℝ => x + y)
                ((fun u : ℝ => θ * u) '' {u : ℝ | ENNReal.ofReal s < a u})
                ((fun v : ℝ => (1 - θ) * v) '' {v : ℝ | ENNReal.ofReal t < b v}) := by
      intro s t
      -- Rewrite the source set as the genuine additive sumset of the two scaled strict
      -- superlevel sets.
      simpa using
        (real_affine_image_eq_image2_add
          (S := {u : ℝ | ENNReal.ofReal s < a u})
          (T := {v : ℝ | ENNReal.ofReal t < b v})
          (θ := θ))
    let αlog : ℝ → ENNReal := fun x => ENNReal.ofReal (Real.exp x) * α (Real.exp x)
    let βlog : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp y) * β (Real.exp y)
    let γlog : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp z) * γ (Real.exp z)
    have hα_log :
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
          ∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume := by
      -- The `a`-profile over `Set.Ioi 0` is exactly the full-line integral of its log transport.
      simpa [αlog] using (log_profile_lintegral_eq (phi := α)).symm
    have hβ_log :
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
          ∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume := by
      -- The same logarithmic change of variables applies to `β`.
      simpa [βlog] using (log_profile_lintegral_eq (phi := β)).symm
    have hγ_log :
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
          ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := by
      -- And likewise for the target profile `γ`.
      simpa [γlog] using (log_profile_lintegral_eq (phi := γ)).symm
    have hlog_kernel_from_pointwise :
        (∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ))) →
        ∀ x y : ℝ, γlog (θ * x + (1 - θ) * y) ≥ αlog x ^ θ * βlog y ^ (1 - θ) := by
      intro hkernel_profile x y
      -- Route correction: the positive-half-line profile step is not a second missing theorem;
      -- it is just the explicit logarithmic transport of the multiplicative kernel.
      simpa [αlog, βlog, γlog] using
        (log_profile_kernel_transport (α := α) (β := β) (γ := γ) hθ_mem hkernel_profile x y)
    let αlogN : ℕ → ℝ → ENNReal := fun N => supportTrunc αlog N
    let βlogN : ℕ → ℝ → ENNReal := fun N => supportTrunc βlog N
    let γlogN : ℕ → ℝ → ENNReal := fun N => supportTrunc γlog N
    have hα_measurable : Measurable α := by
      -- Antitone real profiles are measurable.
      simpa [α] using (Antitone.measurable hα_antitone)
    have hβ_measurable : Measurable β := by
      -- The same monotonicity-to-measurability argument applies to `β`.
      simpa [β] using (Antitone.measurable hβ_antitone)
    have hγ_measurable : Measurable γ := by
      -- And likewise for the target profile `γ`.
      simpa [γ] using (Antitone.measurable hγ_antitone)
    have hαlog_measurable : Measurable αlog := by
      -- The logarithmic transport is measurable because both `exp` and the profile are measurable.
      simpa [αlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hα_measurable.comp Real.measurable_exp))
    have hβlog_measurable : Measurable βlog := by
      -- The same change-of-variables measurability statement holds for `βlog`.
      simpa [βlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hβ_measurable.comp Real.measurable_exp))
    have hγlog_measurable : Measurable γlog := by
      -- And again for `γlog`.
      simpa [γlog] using
        ((ENNReal.continuous_ofReal.measurable.comp Real.measurable_exp).mul
          (hγ_measurable.comp Real.measurable_exp))
    have hαlogN_measurable : ∀ N, Measurable (αlogN N) := by
      intro N
      -- Compact support truncation preserves measurability for the transported `a`-profile.
      simpa [αlogN] using supportTrunc_measurable hαlog_measurable N
    have hβlogN_measurable : ∀ N, Measurable (βlogN N) := by
      intro N
      -- The same support truncation argument applies to `βlog`.
      simpa [βlogN] using supportTrunc_measurable hβlog_measurable N
    have hγlogN_measurable : ∀ N, Measurable (γlogN N) := by
      intro N
      -- And likewise for `γlog`.
      simpa [γlogN] using supportTrunc_measurable hγlog_measurable N
    have hαlogN_mono : Monotone αlogN := by
      intro N M hNM x
      -- Enlarging the compact truncation interval only increases the truncated log profile.
      simpa [αlogN] using supportTrunc_mono (f := αlog) hNM x
    have hβlogN_mono : Monotone βlogN := by
      intro N M hNM x
      -- The same pointwise monotonicity holds for the `β` log truncations.
      simpa [βlogN] using supportTrunc_mono (f := βlog) hNM x
    have hγlogN_mono : Monotone γlogN := by
      intro N M hNM x
      -- And again for the target log truncations.
      simpa [γlogN] using supportTrunc_mono (f := γlog) hNM x
    have hlog_trunc_kernel :
        (∀ ⦃s t : ℝ⦄, 0 < s → 0 < t →
          α s ^ θ * β t ^ (1 - θ) ≤ γ (s ^ θ * t ^ (1 - θ))) →
        ∀ N x y,
          γlogN N (θ * x + (1 - θ) * y) ≥
            αlogN N x ^ θ * βlogN N y ^ (1 - θ) := by
      intro hkernel_profile N x y
      by_cases hx : x ∈ Set.Icc (-(N : ℝ)) N
      · by_cases hy : y ∈ Set.Icc (-(N : ℝ)) N
        · have hz : θ * x + (1 - θ) * y ∈ Set.Icc (-(N : ℝ)) N := by
            rcases hx with ⟨hx_left, hx_right⟩
            rcases hy with ⟨hy_left, hy_right⟩
            -- The affine combination of two points in `[-N, N]` stays in `[-N, N]`.
            constructor <;>
              nlinarith [hθ_mem.1, hθ_mem.2, hx_left, hx_right, hy_left, hy_right]
          -- On the common compact support interval, the truncations are transparent.
          simpa [αlogN, βlogN, γlogN, supportTrunc, hx, hy, hz] using
            hlog_kernel_from_pointwise hkernel_profile x y
        · have hy_zero : βlogN N y = 0 := by
            simp [βlogN, supportTrunc, hy]
          -- If `y` is outside the compact support window, the right-hand side already vanishes.
          rw [hy_zero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
          exact bot_le
      · have hx_zero : αlogN N x = 0 := by
          simp [αlogN, supportTrunc, hx]
        -- And symmetrically when `x` leaves the compact support window.
        rw [hx_zero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
        exact bot_le
    have htrunc :
        ∀ N : ℕ,
          ∫⁻ z, γlogN N z ∂MeasureTheory.volume ≥
            (∫⁻ x, αlogN N x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN N y ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- Route correction: the whole unresolved branch is now packaged as a single theorem whose
      -- conclusion is exactly the compactly supported log-truncation estimate needed here.
      simpa [α, β, γ, αlog, βlog, γlog, αlogN, βlogN, γlogN] using
        (prekopaLeindler_real_log_trunc_step hθ_mem ha_measurable hb_measurable hc_measurable N
          ha_support hb_support hc_support h_kernel)
    have hαlog_lintegral :
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
          ⨆ N, ∫⁻ x, αlogN N x ∂MeasureTheory.volume := by
      -- Monotone convergence sends the compact log truncations back to the full `αlog` integral.
      calc
        ∫⁻ x, αlog x ∂MeasureTheory.volume =
            ∫⁻ x, ⨆ N, αlogN N x ∂MeasureTheory.volume := by
              congr with x
              simpa [αlogN] using (iSup_supportTrunc_apply αlog x).symm
        _ = ⨆ N, ∫⁻ x, αlogN N x ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hαlogN_measurable hαlogN_mono
    have hβlog_lintegral :
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
          ⨆ N, ∫⁻ y, βlogN N y ∂MeasureTheory.volume := by
      -- The same monotone-convergence rewrite applies to `βlog`.
      calc
        ∫⁻ y, βlog y ∂MeasureTheory.volume =
            ∫⁻ y, ⨆ N, βlogN N y ∂MeasureTheory.volume := by
              congr with y
              simpa [βlogN] using (iSup_supportTrunc_apply βlog y).symm
        _ = ⨆ N, ∫⁻ y, βlogN N y ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hβlogN_measurable hβlogN_mono
    have hγlog_lintegral :
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
          ⨆ N, ∫⁻ z, γlogN N z ∂MeasureTheory.volume := by
      -- And likewise for the target log profile.
      calc
        ∫⁻ z, γlog z ∂MeasureTheory.volume =
            ∫⁻ z, ⨆ N, γlogN N z ∂MeasureTheory.volume := by
              congr with z
              simpa [γlogN] using (iSup_supportTrunc_apply γlog z).symm
        _ = ⨆ N, ∫⁻ z, γlogN N z ∂MeasureTheory.volume :=
            MeasureTheory.lintegral_iSup hγlogN_measurable hγlogN_mono
    have hαlog_int_mono :
        Monotone (fun N => ∫⁻ x, αlogN N x ∂MeasureTheory.volume) := by
      intro N M hNM
      -- Integral monotonicity follows from pointwise monotonicity of the truncations.
      exact MeasureTheory.lintegral_mono (fun x => hαlogN_mono hNM x)
    have hβlog_int_mono :
        Monotone (fun N => ∫⁻ y, βlogN N y ∂MeasureTheory.volume) := by
      intro N M hNM
      -- The same integral monotonicity statement holds for `βlog`.
      exact MeasureTheory.lintegral_mono (fun y => hβlogN_mono hNM y)
    have hlog_diag_sup :
        (⨆ N, ∫⁻ x, αlogN N x ∂MeasureTheory.volume) ^ θ *
            (⨆ N, ∫⁻ y, βlogN N y ∂MeasureTheory.volume) ^ (1 - θ) ≤
          ⨆ N,
            (∫⁻ x, αlogN N x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN N y ∂MeasureTheory.volume) ^ (1 - θ) := by
      -- A single large truncation index dominates any pair of compact log truncations.
      have hA_rpow :
          (⨆ N, ∫⁻ x, αlogN N x ∂MeasureTheory.volume) ^ θ =
            ⨆ N, (∫⁻ x, αlogN N x ∂MeasureTheory.volume) ^ θ :=
        (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
      have hB_rpow :
          (⨆ N, ∫⁻ y, βlogN N y ∂MeasureTheory.volume) ^ (1 - θ) =
            ⨆ N, (∫⁻ y, βlogN N y ∂MeasureTheory.volume) ^ (1 - θ) :=
        (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
      rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
      refine iSup_le ?_
      intro n
      rw [ENNReal.mul_iSup]
      refine iSup_le ?_
      intro m
      refine le_iSup_of_le (max n m) ?_
      exact mul_le_mul'
        (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (hαlog_int_mono (Nat.le_max_left n m)))
        (ENNReal.monotone_rpow_of_nonneg
          (sub_nonneg.mpr hθ_mem.2.le) (hβlog_int_mono (Nat.le_max_right n m)))
    have hlog_sup_le :
        (⨆ N,
          (∫⁻ x, αlogN N x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlogN N y ∂MeasureTheory.volume) ^ (1 - θ)) ≤
          ⨆ N, ∫⁻ z, γlogN N z ∂MeasureTheory.volume := by
      refine iSup_le ?_
      intro N
      exact le_iSup_of_le N (htrunc N)
    -- Route correction: after isolating the compact-support inequality `htrunc`, the remaining
    -- passage to the full line is just the same monotone-convergence diagonal argument used later
    -- for support truncations of `a`, `b`, and `c`.
    calc
      ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume = ∫⁻ z, γlog z ∂MeasureTheory.volume := by
        symm
        exact hγ_log
      _ = ⨆ N, ∫⁻ z, γlogN N z ∂MeasureTheory.volume := hγlog_lintegral
      _ ≥
          ⨆ N,
            (∫⁻ x, αlogN N x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ y, βlogN N y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_sup_le
      _ ≥
          (⨆ N, ∫⁻ x, αlogN N x ∂MeasureTheory.volume) ^ θ *
            (⨆ N, ∫⁻ y, βlogN N y ∂MeasureTheory.volume) ^ (1 - θ) := hlog_diag_sup
      _ =
          (∫⁻ x, αlog x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ y, βlog y ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [hαlog_lintegral, hβlog_lintegral]
      _ =
          (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
            (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := by
              rw [hα_log, hβ_log]
  calc
    ∫⁻ z, c z ∂MeasureTheory.volume =
        ∫⁻ r in Set.Ioi 0, γ r ∂MeasureTheory.volume := hγ_profile
    _ ≥
        (∫⁻ s in Set.Ioi 0, α s ∂MeasureTheory.volume) ^ θ *
          (∫⁻ t in Set.Ioi 0, β t ∂MeasureTheory.volume) ^ (1 - θ) := h_profile
    _ =
        (∫⁻ u, a u ∂MeasureTheory.volume) ^ θ *
          (∫⁻ v, b v ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [← hα_profile, ← hβ_profile]

/-- The one-dimensional ENNReal-valued strict Prékopa-Leindler inequality on `ℝ`. -/
private lemma prekopaLeindler_real_strict_lintegral_core
    {a b c : ℝ → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (ha_measurable : Measurable a)
    (hb_measurable : Measurable b)
    (hc_measurable : Measurable c)
    (h_kernel :
      ∀ u v : ℝ,
        c (θ * u + (1 - θ) * v) ≥ a u ^ θ * b v ^ (1 - θ)) :
    ∫⁻ z, c z ∂MeasureTheory.volume ≥
      (∫⁻ u, a u ∂MeasureTheory.volume) ^ θ *
        (∫⁻ v, b v ∂MeasureTheory.volume) ^ (1 - θ) := by
  -- Route correction: instead of treating the full unbounded line at once, first localize to
  -- symmetric compact intervals and postpone only the bounded-support core.
  let aN : ℕ → ℝ → ENNReal := fun N => supportTrunc a N
  let bN : ℕ → ℝ → ENNReal := fun N => supportTrunc b N
  let cN : ℕ → ℝ → ENNReal := fun N => supportTrunc c N
  have haN_measurable : ∀ N, Measurable (aN N) := by
    intro N
    -- Each truncation inherits measurability from the original function.
    simpa [aN] using supportTrunc_measurable ha_measurable N
  have hbN_measurable : ∀ N, Measurable (bN N) := by
    intro N
    -- The same support cutoff preserves measurability for `b`.
    simpa [bN] using supportTrunc_measurable hb_measurable N
  have hcN_measurable : ∀ N, Measurable (cN N) := by
    intro N
    -- And likewise for `c`.
    simpa [cN] using supportTrunc_measurable hc_measurable N
  have haN_mono : Monotone aN := by
    intro N M hNM x
    -- Enlarging the support interval can only increase the truncation.
    simpa [aN] using supportTrunc_mono (f := a) hNM x
  have hbN_mono : Monotone bN := by
    intro N M hNM x
    -- The same monotonicity argument applies to `b`.
    simpa [bN] using supportTrunc_mono (f := b) hNM x
  have hcN_mono : Monotone cN := by
    intro N M hNM x
    -- And again for `c`.
    simpa [cN] using supportTrunc_mono (f := c) hNM x
  have h_kernelN :
      ∀ N : ℕ, ∀ u v : ℝ,
        cN N (θ * u + (1 - θ) * v) ≥ aN N u ^ θ * bN N v ^ (1 - θ) := by
    intro N u v
    by_cases hu : u ∈ Set.Icc (-(N : ℝ)) N
    · by_cases hv : v ∈ Set.Icc (-(N : ℝ)) N
      · -- On the common support interval, the original kernel inequality survives unchanged.
        have hz : θ * u + (1 - θ) * v ∈ Set.Icc (-(N : ℝ)) N := by
          rcases hu with ⟨hu_left, hu_right⟩
          rcases hv with ⟨hv_left, hv_right⟩
          constructor <;> nlinarith [hθ_mem.1, hθ_mem.2, hu_left, hu_right, hv_left, hv_right]
        simpa [aN, bN, cN, supportTrunc, hu, hv, hz] using h_kernel u v
      · -- If `v` leaves the support interval, the right-hand side vanishes.
        have hzero : bN N v = 0 := by
          simp [bN, supportTrunc, hv]
        rw [hzero, ENNReal.zero_rpow_of_pos (sub_pos.mpr hθ_mem.2), mul_zero]
        exact bot_le
    · -- The symmetric argument handles the case where `u` leaves the support interval.
      have hzero : aN N u = 0 := by
        simp [aN, supportTrunc, hu]
      rw [hzero, ENNReal.zero_rpow_of_pos hθ_mem.1, zero_mul]
      exact bot_le
  have htrunc :
      ∀ N : ℕ,
        ∫⁻ z, cN N z ∂MeasureTheory.volume ≥
          (∫⁻ u, aN N u ∂MeasureTheory.volume) ^ θ *
            (∫⁻ v, bN N v ∂MeasureTheory.volume) ^ (1 - θ) := by
    intro N
    -- This is the only remaining one-dimensional input once all level sets are bounded.
    refine prekopaLeindler_real_strict_lintegral_core_bounded
      hθ_mem (haN_measurable N) (hbN_measurable N) (hcN_measurable N) N ?_ ?_ ?_ (h_kernelN N)
    · intro x hx
      simp [aN, supportTrunc, hx]
    · intro x hx
      simp [bN, supportTrunc, hx]
    · intro x hx
      simp [cN, supportTrunc, hx]
  have h_a_lintegral :
      ∫⁻ x, a x ∂MeasureTheory.volume =
        ⨆ N, ∫⁻ x, aN N x ∂MeasureTheory.volume := by
    -- Monotone convergence sends the support truncations of `a` back to the original integral.
    calc
      ∫⁻ x, a x ∂MeasureTheory.volume = ∫⁻ x, ⨆ N, aN N x ∂MeasureTheory.volume := by
        congr with x
        simpa [aN] using (iSup_supportTrunc_apply a x).symm
      _ = ⨆ N, ∫⁻ x, aN N x ∂MeasureTheory.volume :=
        MeasureTheory.lintegral_iSup haN_measurable haN_mono
  have h_b_lintegral :
      ∫⁻ x, b x ∂MeasureTheory.volume =
        ⨆ N, ∫⁻ x, bN N x ∂MeasureTheory.volume := by
    -- The same monotone-convergence rewrite handles `b`.
    calc
      ∫⁻ x, b x ∂MeasureTheory.volume = ∫⁻ x, ⨆ N, bN N x ∂MeasureTheory.volume := by
        congr with x
        simpa [bN] using (iSup_supportTrunc_apply b x).symm
      _ = ⨆ N, ∫⁻ x, bN N x ∂MeasureTheory.volume :=
        MeasureTheory.lintegral_iSup hbN_measurable hbN_mono
  have h_c_lintegral :
      ∫⁻ x, c x ∂MeasureTheory.volume =
        ⨆ N, ∫⁻ x, cN N x ∂MeasureTheory.volume := by
    -- And likewise for the target integral of `c`.
    calc
      ∫⁻ x, c x ∂MeasureTheory.volume = ∫⁻ x, ⨆ N, cN N x ∂MeasureTheory.volume := by
        congr with x
        simpa [cN] using (iSup_supportTrunc_apply c x).symm
      _ = ⨆ N, ∫⁻ x, cN N x ∂MeasureTheory.volume :=
        MeasureTheory.lintegral_iSup hcN_measurable hcN_mono
  have hA_int_mono :
      Monotone (fun N => ∫⁻ x, aN N x ∂MeasureTheory.volume) := by
    intro N M hNM
    -- Integral monotonicity follows from pointwise monotonicity of the truncations.
    exact MeasureTheory.lintegral_mono (fun x => haN_mono hNM x)
  have hB_int_mono :
      Monotone (fun N => ∫⁻ x, bN N x ∂MeasureTheory.volume) := by
    intro N M hNM
    -- The same integral monotonicity statement holds for `b`.
    exact MeasureTheory.lintegral_mono (fun x => hbN_mono hNM x)
  have h_diag_sup :
      (⨆ N, ∫⁻ x, aN N x ∂MeasureTheory.volume) ^ θ *
          (⨆ N, ∫⁻ x, bN N x ∂MeasureTheory.volume) ^ (1 - θ) ≤
        ⨆ N,
          (∫⁻ x, aN N x ∂MeasureTheory.volume) ^ θ *
            (∫⁻ x, bN N x ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- A single large truncation index dominates any pair of truncation indices.
    have hA_rpow :
        (⨆ N, ∫⁻ x, aN N x ∂MeasureTheory.volume) ^ θ =
          ⨆ N, (∫⁻ x, aN N x ∂MeasureTheory.volume) ^ θ :=
      (ENNReal.orderIsoRpow θ hθ_mem.1).map_iSup _
    have hB_rpow :
        (⨆ N, ∫⁻ x, bN N x ∂MeasureTheory.volume) ^ (1 - θ) =
          ⨆ N, (∫⁻ x, bN N x ∂MeasureTheory.volume) ^ (1 - θ) :=
      (ENNReal.orderIsoRpow (1 - θ) (sub_pos.mpr hθ_mem.2)).map_iSup _
    rw [hA_rpow, hB_rpow, ENNReal.iSup_mul]
    refine iSup_le ?_
    intro n
    rw [ENNReal.mul_iSup]
    refine iSup_le ?_
    intro m
    refine le_iSup_of_le (max n m) ?_
    exact mul_le_mul'
      (ENNReal.monotone_rpow_of_nonneg hθ_mem.1.le (hA_int_mono (Nat.le_max_left n m)))
      (ENNReal.monotone_rpow_of_nonneg
        (sub_nonneg.mpr hθ_mem.2.le) (hB_int_mono (Nat.le_max_right n m)))
  have h_rhs_le :
      (∫⁻ u, a u ∂MeasureTheory.volume) ^ θ *
          (∫⁻ v, b v ∂MeasureTheory.volume) ^ (1 - θ) ≤
        ∫⁻ z, c z ∂MeasureTheory.volume := by
    -- First pass to bounded truncations, then send the truncation radius to infinity.
    calc
      (∫⁻ u, a u ∂MeasureTheory.volume) ^ θ *
          (∫⁻ v, b v ∂MeasureTheory.volume) ^ (1 - θ) =
        (⨆ N, ∫⁻ x, aN N x ∂MeasureTheory.volume) ^ θ *
          (⨆ N, ∫⁻ x, bN N x ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [← h_a_lintegral, ← h_b_lintegral]
      _ ≤
          ⨆ N,
            (∫⁻ x, aN N x ∂MeasureTheory.volume) ^ θ *
              (∫⁻ x, bN N x ∂MeasureTheory.volume) ^ (1 - θ) := h_diag_sup
      _ ≤ ⨆ N, ∫⁻ z, cN N z ∂MeasureTheory.volume := by
          refine iSup_le ?_
          intro N
          exact le_iSup_of_le N (htrunc N)
      _ = ∫⁻ z, c z ∂MeasureTheory.volume := by
          rw [← h_c_lintegral]
  exact h_rhs_le

/-- Dimension induction for the core ENNReal-valued strict Prékopa-Leindler inequality. -/
private lemma prekopaLeindler_fin_strict_lintegral_core_induction
    {n : ℕ}
    {A B C : (Fin n → ℝ) → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_measurable : Measurable A)
    (hB_measurable : Measurable B)
    (hC_measurable : Measurable C)
    (h_kernel :
      ∀ u v : Fin n → ℝ,
        C (θ • u + (1 - θ) • v) ≥ A u ^ θ * B v ^ (1 - θ)) :
    ∫⁻ z, C z ∂MeasureTheory.volume ≥
      (∫⁻ u, A u ∂MeasureTheory.volume) ^ θ *
        (∫⁻ v, B v ∂MeasureTheory.volume) ^ (1 - θ) := by
  induction n with
  | zero =>
      -- The base case is the singleton ambient space handled above.
      exact prekopaLeindler_fin_strict_lintegral_core_zero h_kernel
  | succ m hm =>
      let IA : ENNReal := ∫⁻ u, A u ∂MeasureTheory.volume
      let IB : ENNReal := ∫⁻ v, B v ∂MeasureTheory.volume
      let IC : ENNReal := ∫⁻ z, C z ∂MeasureTheory.volume
      by_cases hC_top : IC = (⊤ : ENNReal)
      · -- If the target integral is already infinite, the lower bound is automatic.
        simp [IC, hC_top]
      by_cases hA_zero : IA = 0
      · -- If `A` has zero mass then the right-hand side vanishes because `θ > 0`.
        simpa [IA, hA_zero, ENNReal.zero_rpow_of_pos hθ_mem.1] using
          (zero_le (∫⁻ z, C z ∂MeasureTheory.volume))
      by_cases hB_zero : IB = 0
      · -- The same zero-mass reduction applies to `B`, using `1 - θ > 0`.
        have h_one_sub_pos : 0 < 1 - θ := sub_pos.mpr hθ_mem.2
        simpa [IB, hB_zero, ENNReal.zero_rpow_of_pos h_one_sub_pos] using
          (zero_le (∫⁻ z, C z ∂MeasureTheory.volume))
      let e : ((Fin (m + 1)) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
      let Aprod : ℝ × (Fin m → ℝ) → ENNReal := fun p => A (e.symm p)
      let Bprod : ℝ × (Fin m → ℝ) → ENNReal := fun p => B (e.symm p)
      let Cprod : ℝ × (Fin m → ℝ) → ENNReal := fun p => C (e.symm p)
      have hpres :
          MeasureTheory.MeasurePreserving (⇑e.symm) MeasureTheory.volume MeasureTheory.volume :=
        MeasureTheory.MeasurePreserving.symm e
          (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0)
      have hAprod_measurable : Measurable Aprod := by
        -- Measurability transports along the coordinate equivalence `e.symm`.
        simpa [Aprod] using hA_measurable.comp e.symm.measurable
      have hBprod_measurable : Measurable Bprod := by
        -- The same reindexing argument applies to `B`.
        simpa [Bprod] using hB_measurable.comp e.symm.measurable
      have hCprod_measurable : Measurable Cprod := by
        -- And likewise for `C`.
        simpa [Cprod] using hC_measurable.comp e.symm.measurable
      have hA_transport :
          ∫⁻ p, Aprod p ∂MeasureTheory.volume =
            ∫⁻ u, A u ∂MeasureTheory.volume := by
        -- The coordinate split preserves Lebesgue measure.
        simpa [Aprod, e] using hpres.lintegral_comp_emb e.symm.measurableEmbedding A
      have hB_transport :
          ∫⁻ p, Bprod p ∂MeasureTheory.volume =
            ∫⁻ v, B v ∂MeasureTheory.volume := by
        -- The same change of variables handles `B`.
        simpa [Bprod, e] using hpres.lintegral_comp_emb e.symm.measurableEmbedding B
      have hC_transport :
          ∫⁻ p, Cprod p ∂MeasureTheory.volume =
            ∫⁻ z, C z ∂MeasureTheory.volume := by
        -- And it also transports the target integral of `C`.
        simpa [Cprod, e] using hpres.lintegral_comp_emb e.symm.measurableEmbedding C
      have h_kernel_prod :
          ∀ u v : ℝ × (Fin m → ℝ),
            Cprod (θ • u + (1 - θ) • v) ≥ Aprod u ^ θ * Bprod v ^ (1 - θ) := by
        intro u v
        have h_symm_affine :
            e.symm (θ • u + (1 - θ) • v) = θ • e.symm u + (1 - θ) • e.symm v := by
          -- The inverse coordinate split is `Fin.cons`, so it preserves affine combinations
          -- coordinatewise.
          ext i
          refine Fin.cases ?_ ?_ i
          · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Pi.add_apply, Pi.smul_apply]
          · intro j
            simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Pi.add_apply, Pi.smul_apply]
        -- Rewrite the original kernel inequality in the product coordinates.
        simpa [Aprod, Bprod, Cprod, h_symm_affine] using h_kernel (e.symm u) (e.symm v)
      let Ahat : (Fin m → ℝ) → ENNReal := fun x => ∫⁻ t, Aprod (t, x) ∂MeasureTheory.volume
      let Bhat : (Fin m → ℝ) → ENNReal := fun y => ∫⁻ t, Bprod (t, y) ∂MeasureTheory.volume
      let Chat : (Fin m → ℝ) → ENNReal := fun z => ∫⁻ t, Cprod (t, z) ∂MeasureTheory.volume
      have hAhat_measurable : Measurable Ahat := by
        -- The slice integral of a measurable kernel is measurable in the tail coordinate.
        simpa [Ahat] using
          (hAprod_measurable.lintegral_prod_left'
            (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)))
      have hBhat_measurable : Measurable Bhat := by
        -- The same Fubini measurability statement applies to `B`.
        simpa [Bhat] using
          (hBprod_measurable.lintegral_prod_left'
            (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)))
      have hChat_measurable : Measurable Chat := by
        -- And likewise for the target slice kernel `C`.
        simpa [Chat] using
          (hCprod_measurable.lintegral_prod_left'
            (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)))
      have hAprod_fubini :
          ∫⁻ p, Aprod p ∂MeasureTheory.volume = ∫⁻ x, Ahat x ∂MeasureTheory.volume := by
        -- Rewrite the full product integral of `A` as the iterated integral over the split
        -- coordinates.
        simpa [Ahat] using
          (MeasureTheory.lintegral_prod_symm'
            (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
            (ν := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
            (f := Aprod) hAprod_measurable)
      have hBprod_fubini :
          ∫⁻ p, Bprod p ∂MeasureTheory.volume = ∫⁻ y, Bhat y ∂MeasureTheory.volume := by
        -- The same Fubini identity holds for `B`.
        simpa [Bhat] using
          (MeasureTheory.lintegral_prod_symm'
            (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
            (ν := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
            (f := Bprod) hBprod_measurable)
      have hCprod_fubini :
          ∫⁻ p, Cprod p ∂MeasureTheory.volume = ∫⁻ z, Chat z ∂MeasureTheory.volume := by
        -- And likewise for the target kernel `C`.
        simpa [Chat] using
          (MeasureTheory.lintegral_prod_symm'
            (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
            (ν := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
            (f := Cprod) hCprod_measurable)
      have h_tail_kernel :
          ∀ x y : Fin m → ℝ,
            Chat (θ • x + (1 - θ) • y) ≥ Ahat x ^ θ * Bhat y ^ (1 - θ) := by
        intro x y
        let a : ℝ → ENNReal := fun u => Aprod (u, x)
        let b : ℝ → ENNReal := fun v => Bprod (v, y)
        let c : ℝ → ENNReal := fun z => Cprod (z, θ • x + (1 - θ) • y)
        have ha_measurable : Measurable a := by
          -- Freeze the tail variable `x` and restrict to the first coordinate.
          simpa [a] using hAprod_measurable.comp (by fun_prop)
        have hb_measurable : Measurable b := by
          -- Freeze the tail variable `y` in the same way.
          simpa [b] using hBprod_measurable.comp (by fun_prop)
        have hc_measurable : Measurable c := by
          -- The target slice is measurable after fixing the affine tail coordinate.
          simpa [c] using hCprod_measurable.comp (by fun_prop)
        have h_line_kernel :
            ∀ u v : ℝ,
              c (θ * u + (1 - θ) * v) ≥ a u ^ θ * b v ^ (1 - θ) := by
          intro u v
          -- Specialize the product-space kernel to the current pair of tail coordinates.
          simpa [a, b, c, Pi.add_apply, Pi.smul_apply] using h_kernel_prod (u, x) (v, y)
        -- Apply the one-dimensional strict inequality to the current family of slices.
        simpa [Ahat, Bhat, Chat, a, b, c] using
          prekopaLeindler_real_strict_lintegral_core hθ_mem
            ha_measurable hb_measurable hc_measurable h_line_kernel
      have h_tail :
          ∫⁻ z, Chat z ∂MeasureTheory.volume ≥
            (∫⁻ u, Ahat u ∂MeasureTheory.volume) ^ θ *
              (∫⁻ v, Bhat v ∂MeasureTheory.volume) ^ (1 - θ) := by
        -- Route correction: the higher-dimensional step is now reduced to the one-dimensional
        -- slice theorem plus the induction hypothesis on the tail space.
        exact hm hAhat_measurable hBhat_measurable hChat_measurable h_tail_kernel
      -- Combine the coordinate transport, Fubini rewrites, and the induction hypothesis on the
      -- tail slices.
      calc
        ∫⁻ z, C z ∂MeasureTheory.volume = ∫⁻ p, Cprod p ∂MeasureTheory.volume := by
          rw [hC_transport]
        _ = ∫⁻ z, Chat z ∂MeasureTheory.volume := hCprod_fubini
        _ ≥
            (∫⁻ u, Ahat u ∂MeasureTheory.volume) ^ θ *
              (∫⁻ v, Bhat v ∂MeasureTheory.volume) ^ (1 - θ) := h_tail
        _ =
            (∫⁻ p, Aprod p ∂MeasureTheory.volume) ^ θ *
              (∫⁻ p, Bprod p ∂MeasureTheory.volume) ^ (1 - θ) := by
                rw [← hAprod_fubini, ← hBprod_fubini]
        _ =
            (∫⁻ u, A u ∂MeasureTheory.volume) ^ θ *
              (∫⁻ v, B v ∂MeasureTheory.volume) ^ (1 - θ) := by
                rw [hA_transport, hB_transport]

/-- Core ENNReal-valued strict Prékopa-Leindler inequality on `Fin n → ℝ`. -/
private lemma prekopaLeindler_fin_strict_lintegral_core
    {n : ℕ}
    {A B C : (Fin n → ℝ) → ENNReal}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_measurable : Measurable A)
    (hB_measurable : Measurable B)
    (hC_measurable : Measurable C)
    (h_kernel :
      ∀ u v : Fin n → ℝ,
        C (θ • u + (1 - θ) • v) ≥ A u ^ θ * B v ^ (1 - θ)) :
    ∫⁻ z, C z ∂MeasureTheory.volume ≥
      (∫⁻ u, A u ∂MeasureTheory.volume) ^ θ *
        (∫⁻ v, B v ∂MeasureTheory.volume) ^ (1 - θ) := by
  -- Route correction: the dimension induction is now factored out explicitly, so the only
  -- remaining analytic blocker is the isolated one-dimensional lemma on `ℝ`.
  exact prekopaLeindler_fin_strict_lintegral_core_induction hθ_mem
    hA_measurable hB_measurable hC_measurable h_kernel

/-- Strict Prékopa-Leindler step after separating one distinguished `ℝ` coordinate. -/
private lemma prekopaLeindler_prod_strict_external_lintegral
    {m : ℕ}
    {A B C : ℝ × (Fin m → ℝ) → ℝ}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_measurable : Measurable A)
    (hB_measurable : Measurable B)
    (hC_measurable : Measurable C)
    (hA_nonneg : ∀ u : ℝ × (Fin m → ℝ), 0 ≤ A u)
    (hB_nonneg : ∀ v : ℝ × (Fin m → ℝ), 0 ≤ B v)
    (hC_nonneg : ∀ z : ℝ × (Fin m → ℝ), 0 ≤ C z)
    (hA_integrable : MeasureTheory.Integrable A MeasureTheory.volume)
    (hB_integrable : MeasureTheory.Integrable B MeasureTheory.volume)
    (hC_integrable : MeasureTheory.Integrable C MeasureTheory.volume)
    (h_kernel :
      ∀ u v : ℝ × (Fin m → ℝ),
        ENNReal.ofReal (C (θ • u + (1 - θ) • v)) ≥
          ENNReal.ofReal (A u) ^ θ * ENNReal.ofReal (B v) ^ (1 - θ)) :
    ∫⁻ p, ENNReal.ofReal (C p) ∂MeasureTheory.volume ≥
      (∫⁻ p, ENNReal.ofReal (A p) ∂MeasureTheory.volume) ^ θ *
        (∫⁻ p, ENNReal.ofReal (B p) ∂MeasureTheory.volume) ^ (1 - θ) := by
  let e : ((Fin (m + 1)) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  let Acore : (Fin (m + 1) → ℝ) → ENNReal := fun x => ENNReal.ofReal (A (e x))
  let Bcore : (Fin (m + 1) → ℝ) → ENNReal := fun x => ENNReal.ofReal (B (e x))
  let Ccore : (Fin (m + 1) → ℝ) → ENNReal := fun x => ENNReal.ofReal (C (e x))
  have hpres :
      MeasureTheory.MeasurePreserving (⇑e) MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hAcore_measurable : Measurable Acore := by
    -- Measurability survives the coordinate split and the `ofReal` coercion.
    simpa [Acore] using hA_measurable.ennreal_ofReal.comp e.measurable
  have hBcore_measurable : Measurable Bcore := by
    -- The same transported measurability argument applies to `B`.
    simpa [Bcore] using hB_measurable.ennreal_ofReal.comp e.measurable
  have hCcore_measurable : Measurable Ccore := by
    -- And likewise for `C`.
    simpa [Ccore] using hC_measurable.ennreal_ofReal.comp e.measurable
  have h_kernel_core :
      ∀ u v : Fin (m + 1) → ℝ,
        Ccore (θ • u + (1 - θ) • v) ≥ Acore u ^ θ * Bcore v ^ (1 - θ) := by
    intro u v
    have h_affine :
        e (θ • u + (1 - θ) • v) = θ • e u + (1 - θ) • e v := by
      -- The product-coordinate equivalence acts coordinatewise, so it preserves affine
      -- combinations.
      ext i <;> simp [e, Fin.tail, Pi.add_apply, Pi.smul_apply]
    -- After rewriting the domain through `e`, the target pointwise hypothesis is exactly the
    -- original product-space assumption.
    simpa [Acore, Bcore, Ccore, h_affine] using h_kernel (e u) (e v)
  have hA_lintegral :
      ∫⁻ x, Acore x ∂MeasureTheory.volume =
        ∫⁻ p, ENNReal.ofReal (A p) ∂MeasureTheory.volume := by
    -- Lebesgue measure is preserved by the coordinate split `e`.
    simpa [Acore, e] using
      hpres.lintegral_comp_emb e.measurableEmbedding (fun p => ENNReal.ofReal (A p))
  have hB_lintegral :
      ∫⁻ x, Bcore x ∂MeasureTheory.volume =
        ∫⁻ p, ENNReal.ofReal (B p) ∂MeasureTheory.volume := by
    -- The same change-of-variables identity holds for `B`.
    simpa [Bcore, e] using
      hpres.lintegral_comp_emb e.measurableEmbedding (fun p => ENNReal.ofReal (B p))
  have hC_lintegral :
      ∫⁻ x, Ccore x ∂MeasureTheory.volume =
        ∫⁻ p, ENNReal.ofReal (C p) ∂MeasureTheory.volume := by
    -- And likewise for the target kernel `C`.
    simpa [Ccore, e] using
      hpres.lintegral_comp_emb e.measurableEmbedding (fun p => ENNReal.ofReal (C p))
  have h_core :
      ∫⁻ x, Ccore x ∂MeasureTheory.volume ≥
        (∫⁻ u, Acore u ∂MeasureTheory.volume) ^ θ *
          (∫⁻ v, Bcore v ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- Route correction: the wrapper lemma is now fully reduced to the finite-dimensional ENNReal
    -- core theorem, which is the only remaining analytic prerequisite.
    exact prekopaLeindler_fin_strict_lintegral_core hθ_mem
      hAcore_measurable hBcore_measurable hCcore_measurable
      h_kernel_core
  -- After transporting the domain to `Fin (m + 1) → ℝ`, the original product-space claim is
  -- exactly the core finite-dimensional inequality.
  calc
    ∫⁻ p, ENNReal.ofReal (C p) ∂MeasureTheory.volume =
        ∫⁻ x, Ccore x ∂MeasureTheory.volume := by
          rw [hC_lintegral]
    _ ≥
        (∫⁻ u, Acore u ∂MeasureTheory.volume) ^ θ *
          (∫⁻ v, Bcore v ∂MeasureTheory.volume) ^ (1 - θ) := h_core
    _ =
        (∫⁻ p, ENNReal.ofReal (A p) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ p, ENNReal.ofReal (B p) ∂MeasureTheory.volume) ^ (1 - θ) := by
            rw [hA_lintegral, hB_lintegral]

/-- Strict Prékopa-Leindler step after separating one distinguished `ℝ` coordinate. -/
private lemma prekopaLeindler_prod_strict_external
    {m : ℕ}
    {A B C : ℝ × (Fin m → ℝ) → ℝ}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_measurable : Measurable A)
    (hB_measurable : Measurable B)
    (hC_measurable : Measurable C)
    (hA_nonneg : ∀ u : ℝ × (Fin m → ℝ), 0 ≤ A u)
    (hB_nonneg : ∀ v : ℝ × (Fin m → ℝ), 0 ≤ B v)
    (hC_nonneg : ∀ z : ℝ × (Fin m → ℝ), 0 ≤ C z)
    (hA_integrable : MeasureTheory.Integrable A MeasureTheory.volume)
    (hB_integrable : MeasureTheory.Integrable B MeasureTheory.volume)
    (hC_integrable : MeasureTheory.Integrable C MeasureTheory.volume)
    (h_kernel :
      ∀ u v : ℝ × (Fin m → ℝ),
        C (θ • u + (1 - θ) • v) ≥
          Real.rpow (A u) θ * Real.rpow (B v) (1 - θ)) :
    ∫ p, C p ∂MeasureTheory.volume ≥
      Real.rpow (∫ p, A p ∂MeasureTheory.volume) θ *
        Real.rpow (∫ p, B p ∂MeasureTheory.volume) (1 - θ) := by
  have hA_integral_nonneg : 0 ≤ ∫ p, A p ∂MeasureTheory.volume := by
    -- The real-valued integrals stay nonnegative because the kernels are pointwise nonnegative.
    exact MeasureTheory.integral_nonneg hA_nonneg
  have hB_integral_nonneg : 0 ≤ ∫ p, B p ∂MeasureTheory.volume := by
    -- The same nonnegativity argument applies to `B`.
    exact MeasureTheory.integral_nonneg hB_nonneg
  have hC_integral_nonneg : 0 ≤ ∫ p, C p ∂MeasureTheory.volume := by
    -- And likewise for the target integral of `C`.
    exact MeasureTheory.integral_nonneg hC_nonneg
  have h_kernel_ennreal :
      ∀ u v : ℝ × (Fin m → ℝ),
        ENNReal.ofReal (C (θ • u + (1 - θ) • v)) ≥
          ENNReal.ofReal (A u) ^ θ * ENNReal.ofReal (B v) ^ (1 - θ) := by
    intro u v
    -- Lift the pointwise real inequality into `ℝ≥0∞`; this isolates the missing analytic step.
    calc
      ENNReal.ofReal (C (θ • u + (1 - θ) • v)) ≥
          ENNReal.ofReal (Real.rpow (A u) θ * Real.rpow (B v) (1 - θ)) := by
            exact ENNReal.ofReal_le_ofReal (h_kernel u v)
      _ = ENNReal.ofReal (A u) ^ θ * ENNReal.ofReal (B v) ^ (1 - θ) := by
        have h_mul :
            ENNReal.ofReal (Real.rpow (A u) θ * Real.rpow (B v) (1 - θ)) =
              ENNReal.ofReal (Real.rpow (A u) θ) *
                ENNReal.ofReal (Real.rpow (B v) (1 - θ)) := by
          simpa using
            (ENNReal.ofReal_mul (p := Real.rpow (A u) θ)
              (q := Real.rpow (B v) (1 - θ))
              (Real.rpow_nonneg (hA_nonneg u) θ))
        have hA_rpow :
            ENNReal.ofReal (A u) ^ θ = ENNReal.ofReal (Real.rpow (A u) θ) := by
          simpa using
            (ENNReal.ofReal_rpow_of_nonneg (x := A u) (p := θ)
              (hA_nonneg u) hθ_mem.1.le)
        have hB_rpow :
            ENNReal.ofReal (B v) ^ (1 - θ) = ENNReal.ofReal (Real.rpow (B v) (1 - θ)) := by
          simpa using
            (ENNReal.ofReal_rpow_of_nonneg (x := B v) (p := 1 - θ)
              (hB_nonneg v) (sub_nonneg.mpr hθ_mem.2.le))
        calc
          ENNReal.ofReal (Real.rpow (A u) θ * Real.rpow (B v) (1 - θ)) =
              ENNReal.ofReal (Real.rpow (A u) θ) *
                ENNReal.ofReal (Real.rpow (B v) (1 - θ)) := h_mul
          _ = ENNReal.ofReal (A u) ^ θ * ENNReal.ofReal (B v) ^ (1 - θ) := by
            rw [← hA_rpow, ← hB_rpow]
  have h_lintegral :
      ∫⁻ p, ENNReal.ofReal (C p) ∂MeasureTheory.volume ≥
        (∫⁻ p, ENNReal.ofReal (A p) ∂MeasureTheory.volume) ^ θ *
          (∫⁻ p, ENNReal.ofReal (B p) ∂MeasureTheory.volume) ^ (1 - θ) := by
    -- Route correction: all real-valued bookkeeping is now discharged locally, so only the
    -- ENNReal product-space inequality remains as the missing prerequisite.
    exact prekopaLeindler_prod_strict_external_lintegral hθ_mem
      hA_measurable hB_measurable hC_measurable
      hA_nonneg hB_nonneg hC_nonneg
      hA_integrable hB_integrable hC_integrable
      h_kernel_ennreal
  have hA_integral_ofReal :
      ENNReal.ofReal (∫ p, A p ∂MeasureTheory.volume) =
        ∫⁻ p, ENNReal.ofReal (A p) ∂MeasureTheory.volume := by
    -- Convert the nonnegative real integral of `A` into the corresponding `lintegral`.
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hA_integrable
      (Filter.Eventually.of_forall hA_nonneg)
  have hB_integral_ofReal :
      ENNReal.ofReal (∫ p, B p ∂MeasureTheory.volume) =
        ∫⁻ p, ENNReal.ofReal (B p) ∂MeasureTheory.volume := by
    -- The same conversion applies to `B`.
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hB_integrable
      (Filter.Eventually.of_forall hB_nonneg)
  have hC_integral_ofReal :
      ENNReal.ofReal (∫ p, C p ∂MeasureTheory.volume) =
        ∫⁻ p, ENNReal.ofReal (C p) ∂MeasureTheory.volume := by
    -- And likewise for the target kernel `C`.
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hC_integrable
      (Filter.Eventually.of_forall hC_nonneg)
  have h_ofReal_goal :
      ENNReal.ofReal
          (Real.rpow (∫ p, A p ∂MeasureTheory.volume) θ *
            Real.rpow (∫ p, B p ∂MeasureTheory.volume) (1 - θ)) ≤
        ENNReal.ofReal (∫ p, C p ∂MeasureTheory.volume) := by
    -- Rewrite the `lintegral` inequality entirely in terms of the original real integrals.
    rw [← hC_integral_ofReal, ← hA_integral_ofReal, ← hB_integral_ofReal] at h_lintegral
    calc
      ENNReal.ofReal
          (Real.rpow (∫ p, A p ∂MeasureTheory.volume) θ *
            Real.rpow (∫ p, B p ∂MeasureTheory.volume) (1 - θ)) =
          ENNReal.ofReal (∫ p, A p ∂MeasureTheory.volume) ^ θ *
            ENNReal.ofReal (∫ p, B p ∂MeasureTheory.volume) ^ (1 - θ) := by
              have h_mul :
                  ENNReal.ofReal
                      (Real.rpow (∫ p, A p ∂MeasureTheory.volume) θ *
                        Real.rpow (∫ p, B p ∂MeasureTheory.volume) (1 - θ)) =
                    ENNReal.ofReal (Real.rpow (∫ p, A p ∂MeasureTheory.volume) θ) *
                      ENNReal.ofReal (Real.rpow (∫ p, B p ∂MeasureTheory.volume) (1 - θ)) := by
                simpa using
                  (ENNReal.ofReal_mul
                    (p := Real.rpow (∫ p, A p ∂MeasureTheory.volume) θ)
                    (q := Real.rpow (∫ p, B p ∂MeasureTheory.volume) (1 - θ))
                    (Real.rpow_nonneg hA_integral_nonneg θ))
              have hA_rpow :
                  ENNReal.ofReal (∫ p, A p ∂MeasureTheory.volume) ^ θ =
                    ENNReal.ofReal (Real.rpow (∫ p, A p ∂MeasureTheory.volume) θ) := by
                simpa using
                  (ENNReal.ofReal_rpow_of_nonneg
                    (x := ∫ p, A p ∂MeasureTheory.volume) (p := θ)
                    hA_integral_nonneg hθ_mem.1.le)
              have hB_rpow :
                  ENNReal.ofReal (∫ p, B p ∂MeasureTheory.volume) ^ (1 - θ) =
                    ENNReal.ofReal (Real.rpow (∫ p, B p ∂MeasureTheory.volume) (1 - θ)) := by
                simpa using
                  (ENNReal.ofReal_rpow_of_nonneg
                    (x := ∫ p, B p ∂MeasureTheory.volume) (p := 1 - θ)
                    hB_integral_nonneg (sub_nonneg.mpr hθ_mem.2.le))
              calc
                ENNReal.ofReal
                    (Real.rpow (∫ p, A p ∂MeasureTheory.volume) θ *
                      Real.rpow (∫ p, B p ∂MeasureTheory.volume) (1 - θ)) =
                    ENNReal.ofReal (Real.rpow (∫ p, A p ∂MeasureTheory.volume) θ) *
                      ENNReal.ofReal (Real.rpow (∫ p, B p ∂MeasureTheory.volume) (1 - θ)) := h_mul
                _ = ENNReal.ofReal (∫ p, A p ∂MeasureTheory.volume) ^ θ *
                      ENNReal.ofReal (∫ p, B p ∂MeasureTheory.volume) ^ (1 - θ) := by
                  rw [← hA_rpow, ← hB_rpow]
      _ ≤ ENNReal.ofReal (∫ p, C p ∂MeasureTheory.volume) := by
        simpa [ge_iff_le] using h_lintegral
  -- Drop back to real-valued integrals after the ENNReal reformulation has been normalized.
  exact (ENNReal.ofReal_le_ofReal_iff hC_integral_nonneg).mp h_ofReal_goal

/-- Strict Prékopa-Leindler step after separating one distinguished `ℝ` coordinate. -/
private lemma prekopaLeindler_prod_strict
    {m : ℕ}
    {A B C : ℝ × (Fin m → ℝ) → ℝ}
    {θ : ℝ}
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hA_measurable : Measurable A)
    (hB_measurable : Measurable B)
    (hC_measurable : Measurable C)
    (hA_nonneg : ∀ u : ℝ × (Fin m → ℝ), 0 ≤ A u)
    (hB_nonneg : ∀ v : ℝ × (Fin m → ℝ), 0 ≤ B v)
    (hC_nonneg : ∀ z : ℝ × (Fin m → ℝ), 0 ≤ C z)
    (hA_integrable : MeasureTheory.Integrable A MeasureTheory.volume)
    (hB_integrable : MeasureTheory.Integrable B MeasureTheory.volume)
    (hC_integrable : MeasureTheory.Integrable C MeasureTheory.volume)
    (h_kernel :
      ∀ u v : ℝ × (Fin m → ℝ),
        C (θ • u + (1 - θ) • v) ≥
          Real.rpow (A u) θ * Real.rpow (B v) (1 - θ)) :
    ∫ p, C p ∂MeasureTheory.volume ≥
      Real.rpow (∫ p, A p ∂MeasureTheory.volume) θ *
        Real.rpow (∫ p, B p ∂MeasureTheory.volume) (1 - θ) := by
  -- Route correction: the coordinate transport is already complete, so the local role of this lemma
  -- is only to invoke the isolated strict product-space prerequisite.
  exact prekopaLeindler_prod_strict_external hθ_mem
    hA_measurable hB_measurable hC_measurable
    hA_nonneg hB_nonneg hC_nonneg
    hA_integrable hB_integrable hC_integrable
    h_kernel

/-- Strict-interior finite-dimensional Prékopa-Leindler step on `Fin n → ℝ`. -/
private lemma prekopaLeindler_fin_strict
    {n : ℕ}
    {A B C : (Fin n → ℝ) → ℝ}
    {θ : ℝ}
    (hn_pos : 0 < n)
    (hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1)
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
  -- Reindexing `Fin (n + 1) → ℝ` by one distinguished coordinate preserves Lebesgue integrals.
  have integral_comp_piFinSuccAbove :
      ∀ {m : ℕ} (i : Fin (m + 1)) (g : (Fin (m + 1) → ℝ) → ℝ),
        ∫ x, g x ∂MeasureTheory.volume =
          ∫ p : ℝ × (Fin m → ℝ),
            g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm p)
              ∂MeasureTheory.volume := by
    intro m i g
    let e : ((j : Fin (m + 1)) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
    -- Transport Lebesgue measure along the measurable equivalence separating one coordinate.
    have hpres :
        MeasureTheory.MeasurePreserving (⇑e.symm) MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.MeasurePreserving.symm e
        (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i)
    simpa [e] using (hpres.integral_comp' g).symm
  rcases Nat.exists_eq_succ_of_ne_zero hn_pos.ne' with ⟨m, rfl⟩
  let e : ((Fin (m + 1)) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  let Aprod : ℝ × (Fin m → ℝ) → ℝ := fun p => A (e.symm p)
  let Bprod : ℝ × (Fin m → ℝ) → ℝ := fun p => B (e.symm p)
  let Cprod : ℝ × (Fin m → ℝ) → ℝ := fun p => C (e.symm p)
  have hpres :
      MeasureTheory.MeasurePreserving (⇑e.symm) MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.MeasurePreserving.symm e
      (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0)
  have hA_integral :
      ∫ u, A u ∂MeasureTheory.volume = ∫ p, Aprod p ∂MeasureTheory.volume := by
    -- Rewrite the `A`-integral in the product coordinates needed for the induction route.
    simpa [Aprod, e] using integral_comp_piFinSuccAbove (i := (0 : Fin (m + 1))) A
  have hB_integral :
      ∫ v, B v ∂MeasureTheory.volume = ∫ p, Bprod p ∂MeasureTheory.volume := by
    -- The same coordinate split applies to the `B`-integral.
    simpa [Bprod, e] using integral_comp_piFinSuccAbove (i := (0 : Fin (m + 1))) B
  have hC_integral :
      ∫ z, C z ∂MeasureTheory.volume = ∫ p, Cprod p ∂MeasureTheory.volume := by
    -- The target integral is likewise rewritten into the product-space form.
    simpa [Cprod, e] using integral_comp_piFinSuccAbove (i := (0 : Fin (m + 1))) C
  have hAprod_measurable : Measurable Aprod := by
    -- Measurability transports along the coordinate equivalence `e.symm`.
    simpa [Aprod] using hA_measurable.comp e.symm.measurable
  have hBprod_measurable : Measurable Bprod := by
    -- The same measurable-coordinate change applies to `B`.
    simpa [Bprod] using hB_measurable.comp e.symm.measurable
  have hCprod_measurable : Measurable Cprod := by
    -- And likewise for the target kernel `C`.
    simpa [Cprod] using hC_measurable.comp e.symm.measurable
  have hAprod_nonneg : ∀ u : ℝ × (Fin m → ℝ), 0 ≤ Aprod u := by
    intro u
    -- Pointwise nonnegativity is preserved by reindexing the domain.
    exact hA_nonneg (e.symm u)
  have hBprod_nonneg : ∀ v : ℝ × (Fin m → ℝ), 0 ≤ Bprod v := by
    intro v
    -- This is the corresponding transported nonnegativity for `B`.
    exact hB_nonneg (e.symm v)
  have hCprod_nonneg : ∀ z : ℝ × (Fin m → ℝ), 0 ≤ Cprod z := by
    intro z
    -- The same reindexing argument preserves nonnegativity of `C`.
    exact hC_nonneg (e.symm z)
  have hAprod_integrable : MeasureTheory.Integrable Aprod MeasureTheory.volume := by
    -- Integrability transports along a measure-preserving measurable equivalence.
    simpa [Aprod] using
      (hpres.integrable_comp hA_measurable.aestronglyMeasurable).2 hA_integrable
  have hBprod_integrable : MeasureTheory.Integrable Bprod MeasureTheory.volume := by
    -- The same measure-preserving change of variables handles `B`.
    simpa [Bprod] using
      (hpres.integrable_comp hB_measurable.aestronglyMeasurable).2 hB_integrable
  have hCprod_integrable : MeasureTheory.Integrable Cprod MeasureTheory.volume := by
    -- And it also transports integrability of `C`.
    simpa [Cprod] using
      (hpres.integrable_comp hC_measurable.aestronglyMeasurable).2 hC_integrable
  have h_kernel_prod :
      ∀ u v : ℝ × (Fin m → ℝ),
        Cprod (θ • u + (1 - θ) • v) ≥
          Real.rpow (Aprod u) θ * Real.rpow (Bprod v) (1 - θ) := by
    intro u v
    have h_symm_affine :
        e.symm (θ • u + (1 - θ) • v) = θ • e.symm u + (1 - θ) • e.symm v := by
      -- The inverse coordinate split is `Fin.cons`, so it preserves affine combinations
      -- coordinatewise.
      ext i
      refine Fin.cases ?_ ?_ i
      · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Pi.add_apply, Pi.smul_apply]
      · intro j
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Pi.add_apply, Pi.smul_apply]
    -- Rewrite the original kernel inequality in the product coordinates.
    simpa [Aprod, Bprod, Cprod, h_symm_affine] using h_kernel (e.symm u) (e.symm v)
  -- Route correction: instead of searching for a hidden ready-made theorem, reduce the remaining
  -- branch to the product-space formulation used by the standard induction-on-dimension proof.
  have h_product_goal :
      ∫ p, Cprod p ∂MeasureTheory.volume ≥
        Real.rpow (∫ p, Aprod p ∂MeasureTheory.volume) θ *
          Real.rpow (∫ p, Bprod p ∂MeasureTheory.volume) (1 - θ) := by
    -- All transported hypotheses are now explicit, so the only remaining blocker is the isolated
    -- product-space strict theorem.
    exact prekopaLeindler_prod_strict hθ_mem
      hAprod_measurable hBprod_measurable hCprod_measurable
      hAprod_nonneg hBprod_nonneg hCprod_nonneg
      hAprod_integrable hBprod_integrable hCprod_integrable
      h_kernel_prod
  -- After the coordinate transport, the original claim is exactly the product-space goal above.
  simpa [hA_integral, hB_integral, hC_integral] using h_product_goal

/-- Finite-dimensional Prékopa-Leindler bridge for kernels on `Fin n → ℝ`. -/
private lemma prekopaLeindler_fin
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
  by_cases hθ_zero : θ = 0
  · subst θ
    -- At the left endpoint the kernel inequality collapses to the pointwise domination `B ≤ C`.
    have h_pointwise : ∀ z : Fin n → ℝ, B z ≤ C z := by
      intro z
      simpa using h_kernel 0 z
    -- Integrating the pointwise bound proves the endpoint inequality.
    have h_integral :
        ∫ z, B z ∂MeasureTheory.volume ≤ ∫ z, C z ∂MeasureTheory.volume :=
      MeasureTheory.integral_mono hB_integrable hC_integrable h_pointwise
    simpa using h_integral
  by_cases hθ_one : θ = 1
  · subst θ
    -- At the right endpoint the kernel inequality similarly collapses to `A ≤ C`.
    have h_pointwise : ∀ z : Fin n → ℝ, A z ≤ C z := by
      intro z
      simpa using h_kernel z 0
    -- Integrating this pointwise comparison gives the desired bound.
    have h_integral :
        ∫ z, A z ∂MeasureTheory.volume ≤ ∫ z, C z ∂MeasureTheory.volume :=
      MeasureTheory.integral_mono hA_integrable hC_integrable h_pointwise
    simpa using h_integral
  by_cases hn : n = 0
  · subst hn
    -- In dimension zero the ambient space is a singleton, so all three integrals reduce to the
    -- kernel values at the unique point.
    have hdirac :
        (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) =
          MeasureTheory.Measure.dirac 0 := by
      -- Rewrite zero-dimensional Lebesgue measure as the Dirac mass on the unique point.
      simpa [MeasureTheory.volume_pi] using
        (MeasureTheory.Measure.pi_of_empty
          (μ := fun _ : Fin 0 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          (x := (0 : Fin 0 → ℝ)))
    rw [hdirac]
    -- After reducing the three integrals to Dirac integrals, the claim is exactly the kernel
    -- inequality at the unique pair of points.
    simp only [MeasureTheory.integral_dirac]
    simpa using h_kernel 0 0
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hθ_pos : 0 < θ := lt_of_le_of_ne hθ0 fun h => hθ_zero h.symm
  have hθ_lt_one : θ < 1 := lt_of_le_of_ne hθ1 hθ_one
  -- TODO: the only remaining branch is the genuinely positive-dimensional case `0 < n` and
  -- `0 < θ < 1`; discharge it by importing or proving a finite-dimensional Prékopa-Leindler
  -- theorem specialized to Lebesgue measure on `Fin n → ℝ`.
  have hθ_mem : θ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hθ_pos, hθ_lt_one⟩
  -- Keeping the outer proof flat makes the missing ingredient explicit: only the strict
  -- positive-dimensional Prékopa-Leindler step remains.
  exact prekopaLeindler_fin_strict hn_pos hθ_mem
    hA_measurable hB_measurable hC_measurable
    hA_nonneg hB_nonneg hC_nonneg
    hA_integrable hB_integrable hC_integrable
    h_kernel

theorem convolution_logConcave
    {n : ℕ}
    (f g h : (Fin n → ℝ) → ℝ)
    (hf_density : ProbabilityDensity MeasureTheory.volume f)
    (hg_density : ProbabilityDensity MeasureTheory.volume g)
    (hf_logConcave : LogConcave f)
    (hg_logConcave : LogConcave g)
    (h_integrable :
      ∀ z : Fin n → ℝ,
        MeasureTheory.Integrable
          (fun t : Fin n → ℝ => f (z - t) * g t)
          MeasureTheory.volume)
    (hh_conv : ∀ z : Fin n → ℝ,
      h z = ∫ t, f (z - t) * g t ∂(MeasureTheory.volume)) :
    ProbabilityDensity MeasureTheory.volume h ∧ LogConcave h := by
  rcases hf_density with ⟨hf_meas, hf_nonneg, hf_integrable, hf_integral⟩
  rcases hg_density with ⟨hg_meas, hg_nonneg, hg_integrable, hg_integral⟩
  constructor
  · -- Rewrite `ENNReal.ofReal ∘ h` as the additive convolution of the two density measures.
    have h_ofReal_eq_lconvolution :
        ∀ z : Fin n → ℝ,
          ENNReal.ofReal (h z) =
            MeasureTheory.lconvolution
              (fun t : Fin n → ℝ => ENNReal.ofReal (g t))
              (fun t : Fin n → ℝ => ENNReal.ofReal (f t))
              MeasureTheory.volume z := by
      intro z
      rw [hh_conv z, MeasureTheory.lconvolution_def]
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (h_integrable z)]
      · refine MeasureTheory.lintegral_congr_ae <| Filter.Eventually.of_forall ?_
        intro t
        have hz : z - t = -t + z := by
          ext i
          simp [sub_eq_add_neg, add_comm]
        change ENNReal.ofReal (f (z - t) * g t) = ENNReal.ofReal (g t) * ENNReal.ofReal (f (-t + z))
        rw [ENNReal.ofReal_mul (hf_nonneg _), hz]
        simp [mul_comm]
      · exact Filter.Eventually.of_forall fun t => mul_nonneg (hf_nonneg _) (hg_nonneg _)
    have h_ofReal_eq_lconvolution_fun :
        (fun z : Fin n → ℝ => ENNReal.ofReal (h z)) =
          MeasureTheory.lconvolution
            (fun t : Fin n → ℝ => ENNReal.ofReal (g t))
            (fun t : Fin n → ℝ => ENNReal.ofReal (f t))
            MeasureTheory.volume := by
      funext z
      exact h_ofReal_eq_lconvolution z
    -- The convolution formula makes `h` measurable after converting back from `ENNReal`.
    have h_meas_ofReal :
        Measurable fun z : Fin n → ℝ => ENNReal.ofReal (h z) := by
      simpa [h_ofReal_eq_lconvolution_fun] using
        (MeasureTheory.measurable_lconvolution MeasureTheory.volume
          hg_meas.ennreal_ofReal hf_meas.ennreal_ofReal)
    have h_nonneg : ∀ z : Fin n → ℝ, 0 ≤ h z := by
      intro z
      rw [hh_conv z]
      exact MeasureTheory.integral_nonneg fun t => mul_nonneg (hf_nonneg _) (hg_nonneg _)
    have h_toReal_eq :
        (fun z : Fin n → ℝ => (ENNReal.ofReal (h z)).toReal) = h := by
      funext z
      simp [h_nonneg z]
    have h_meas : Measurable h := by
      simpa [h_toReal_eq] using Measurable.ennreal_toReal h_meas_ofReal
    let μg : MeasureTheory.Measure (Fin n → ℝ) :=
      MeasureTheory.volume.withDensity (fun t : Fin n → ℝ => ENNReal.ofReal (g t))
    let μf : MeasureTheory.Measure (Fin n → ℝ) :=
      MeasureTheory.volume.withDensity (fun t : Fin n → ℝ => ENNReal.ofReal (f t))
    -- Convert the convolution identity into a probability-measure statement to control mass.
    have h_withDensity_eq :
        MeasureTheory.volume.withDensity (fun z : Fin n → ℝ => ENNReal.ofReal (h z)) =
          μg.conv μf := by
      simpa [μg, μf, h_ofReal_eq_lconvolution_fun] using
        (MeasureTheory.conv_withDensity_eq_lconvolution
          hg_meas.ennreal_ofReal hf_meas.ennreal_ofReal).symm
    have hg_lintegral :
        ∫⁻ t : Fin n → ℝ, ENNReal.ofReal (g t) ∂MeasureTheory.volume = 1 := by
      calc
        ∫⁻ t : Fin n → ℝ, ENNReal.ofReal (g t) ∂MeasureTheory.volume =
            ENNReal.ofReal (∫ t : Fin n → ℝ, g t ∂MeasureTheory.volume) := by
              symm
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_integrable
                (Filter.Eventually.of_forall hg_nonneg)
        _ = 1 := by simp [hg_integral]
    have hf_lintegral :
        ∫⁻ t : Fin n → ℝ, ENNReal.ofReal (f t) ∂MeasureTheory.volume = 1 := by
      calc
        ∫⁻ t : Fin n → ℝ, ENNReal.ofReal (f t) ∂MeasureTheory.volume =
            ENNReal.ofReal (∫ t : Fin n → ℝ, f t ∂MeasureTheory.volume) := by
              symm
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_integrable
                (Filter.Eventually.of_forall hf_nonneg)
        _ = 1 := by simp [hf_integral]
    have hg_univ : μg Set.univ = 1 := by
      simp [μg, hg_lintegral]
    have hf_univ : μf Set.univ = 1 := by
      simp [μf, hf_lintegral]
    have hg_prob : MeasureTheory.IsProbabilityMeasure μg :=
      (MeasureTheory.isProbabilityMeasure_iff).2 hg_univ
    have hf_prob : MeasureTheory.IsProbabilityMeasure μf :=
      (MeasureTheory.isProbabilityMeasure_iff).2 hf_univ
    have h_lintegral :
        ∫⁻ z : Fin n → ℝ, ENNReal.ofReal (h z) ∂MeasureTheory.volume = 1 := by
      letI : MeasureTheory.IsProbabilityMeasure μg := hg_prob
      letI : MeasureTheory.IsProbabilityMeasure μf := hf_prob
      calc
        ∫⁻ z : Fin n → ℝ, ENNReal.ofReal (h z) ∂MeasureTheory.volume =
            (MeasureTheory.volume.withDensity
              (fun z : Fin n → ℝ => ENNReal.ofReal (h z))) Set.univ := by
                symm
                simp
        _ = (μg.conv μf) Set.univ := by rw [h_withDensity_eq]
        _ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
    have h_integrable_toReal :
        MeasureTheory.Integrable
          (fun z : Fin n → ℝ => (ENNReal.ofReal (h z)).toReal)
          MeasureTheory.volume :=
      MeasureTheory.integrable_toReal_of_lintegral_ne_top
        (Measurable.aemeasurable h_meas_ofReal)
        (by simp [h_lintegral])
    have h_integrable' : MeasureTheory.Integrable h MeasureTheory.volume := by
      refine h_integrable_toReal.congr ?_
      exact Filter.Eventually.of_forall fun z => by simp [h_nonneg z]
    -- The total mass of the convolution is the product of the masses of the two densities.
    have h_integral_ofReal :
        ENNReal.ofReal (∫ z, h z ∂MeasureTheory.volume) = 1 := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_integrable']
      · exact h_lintegral
      · exact Filter.Eventually.of_forall h_nonneg
    refine ⟨h_meas, h_nonneg, h_integrable', ?_⟩
    exact ENNReal.ofReal_eq_one.mp h_integral_ofReal
  · -- Route correction: the density bookkeeping closes through the convolution API, but the
    -- remaining goal is exactly the missing Prékopa-style statement that log-concavity survives
    -- taking the marginal `z ↦ ∫ t, f (z - t) * g t`.
    constructor
    · intro z
      -- The convolution integrand is pointwise nonnegative, so its integral is nonnegative as well.
      rw [hh_conv z]
      exact MeasureTheory.integral_nonneg fun t => mul_nonneg (hf_nonneg _) (hg_nonneg _)
    · intro x y θ hθ0 hθ1
      -- Rewrite the three target values as convolution integrals so the pointwise kernel inequality is visible.
      rw [hh_conv (θ • x + (1 - θ) • y), hh_conv x, hh_conv y]
      let A : (Fin n → ℝ) → ℝ := fun u => f (x - u) * g u
      let B : (Fin n → ℝ) → ℝ := fun v => f (y - v) * g v
      let C : (Fin n → ℝ) → ℝ := fun z => f ((θ • x + (1 - θ) • y) - z) * g z
      have h_kernel :
          ∀ u v : Fin n → ℝ,
            C (θ • u + (1 - θ) • v) ≥
              Real.rpow (A u) θ * Real.rpow (B v) (1 - θ) := by
        intro u v
        -- This is the local part of the proof: the kernel itself is log-concave in the Prékopa sense.
        simpa [A, B, C] using
          convolution_kernel_logConcave_pointwise hf_logConcave hg_logConcave
            (x := x) (y := y) (u := u) (v := v) hθ0 hθ1
      have hA_measurable : Measurable A := by
        -- The first kernel is measurable because it is a product of the translated `f` and `g`.
        simp only [A]
        fun_prop
      have hB_measurable : Measurable B := by
        -- The second kernel has the same structure, centered at `y`.
        simp only [B]
        fun_prop
      have hC_measurable : Measurable C := by
        -- The target kernel is again a translated copy of `f` times `g`.
        simp only [C]
        fun_prop
      have hA_nonneg : ∀ u : Fin n → ℝ, 0 ≤ A u := by
        intro u
        -- Both factors are nonnegative pointwise, so their product is as well.
        exact mul_nonneg (hf_nonneg _) (hg_nonneg _)
      have hB_nonneg : ∀ v : Fin n → ℝ, 0 ≤ B v := by
        intro v
        -- This is the analogous pointwise nonnegativity for the `y`-kernel.
        exact mul_nonneg (hf_nonneg _) (hg_nonneg _)
      have hC_nonneg : ∀ z : Fin n → ℝ, 0 ≤ C z := by
        intro z
        -- The kernel at the affine-combination point is also pointwise nonnegative.
        exact mul_nonneg (hf_nonneg _) (hg_nonneg _)
      have hA_integrable : MeasureTheory.Integrable A MeasureTheory.volume := by
        -- This is exactly the supplied convolution-integrability hypothesis at `x`.
        simpa only [A] using h_integrable x
      have hB_integrable : MeasureTheory.Integrable B MeasureTheory.volume := by
        -- This is the corresponding supplied integrability hypothesis at `y`.
        simpa only [B] using h_integrable y
      have hC_integrable : MeasureTheory.Integrable C MeasureTheory.volume := by
        -- This is the supplied integrability hypothesis at the affine combination of `x` and `y`.
        simpa only [C] using h_integrable (θ • x + (1 - θ) • y)
      -- Apply the finite-dimensional Prékopa-Leindler bridge to the three convolution kernels.
      simpa only [A, B, C] using
        prekopaLeindler_fin hθ0 hθ1
          hA_measurable hB_measurable hC_measurable
          hA_nonneg hB_nonneg hC_nonneg
          hA_integrable hB_integrable hC_integrable
          h_kernel

end «problem-197»
