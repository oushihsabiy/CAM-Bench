import Mathlib
import problems.«problem-11»

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-79»
/-
For a statistical model with observed data z and parameter x, the log - likelihood is the function
ell(x) = log p(z| x), where p(z| x) is the likelihood of the observation under parameter x.
-/
def logLikelihood (p : α → β → ℝ) (z : β) : α → ℝ :=
  fun x => Real.log (p x z)

/-
Maximum - likelihood estimation is the problem of choosing a parameter x that maximizes the
log - likelihood, equivalently the likelihood, of the observed data: x* ∈ operatorname*{argmax}_x
ell(x).
-/
def maximumLikelihoodEstimators (p : α → β → ℝ) (z : β) : Set α :=
  {x | ∀ y, logLikelihood p z y ≤ logLikelihood p z x}

/-- A concave log-likelihood has a convex set of maximizers. -/
lemma convex_maximumLikelihoodEstimators_of_concaveOn
    {α β : Type*} [AddCommGroup α] [Module ℝ α]
    {p : α → β → ℝ} {z : β}
    (hconc : ConcaveOn ℝ (Set.univ : Set α) (logLikelihood p z)) :
    Convex ℝ (maximumLikelihoodEstimators p z) := by
  -- The maximizer set is the intersection of the superlevel sets indexed by the comparison point.
  rw [maximumLikelihoodEstimators]
  simpa [Set.setOf_forall] using
    (convex_iInter fun y => hconc.convex_ge (logLikelihood p z y))

/-- The standard Gaussian upper tail from the problem statement. -/
def standardGaussianUpperTail (t : ℝ) : ℝ :=
  (((1 / Real.sqrt (2 * Real.pi)) : ℝ) *
    ∫ u in Set.Ici t, Real.exp (-(u ^ 2) / 2))

/-- The standard one-dimensional Gaussian density, viewed on `Fin 1 → ℝ`. -/
private def standardGaussianDensityFin1 (x : Fin 1 → ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) (x 0)

/-- The pushed-forward standard Gaussian on `ℝ` is a probability density on `Fin 1 → ℝ`. -/
private lemma standardGaussianDensityFin1_isProbabilityDensity :
    «problem-11».IsProbabilityDensity
      (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0))
      ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm)
      (fun x => ENNReal.ofReal (standardGaussianDensityFin1 x)) := by
  -- Route correction: use the measurable equivalence `Fin 1 → ℝ ≃ ℝ` instead of rebuilding the
  -- one-dimensional density from scratch on the ambient `Fin 1` space.
  refine ⟨(MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurable, ?_, ?_, ?_⟩
  · -- The transported density is measurable because it is the Gaussian pdf composed with evaluation.
    simpa [standardGaussianDensityFin1] using
      ((ProbabilityTheory.measurable_gaussianPDFReal 0 (1 : ℝ≥0)).comp measurable_apply)
        .ennreal_ofReal
  · intro A hA
    let e : ℝ ≃ᵐ (Fin 1 → ℝ) := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
    -- Rewrite the Gaussian law on `ℝ` as the `withDensity` measure, then transport the set
    -- integral across the measurable equivalence.
    rw [ProbabilityTheory.gaussianReal_apply 0 (by norm_num) (e ⁻¹' A)]
    simpa [e, standardGaussianDensityFin1, ProbabilityTheory.gaussianPDF] using
      (((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _)
        .setLIntegral_comp_preimage_emb e.measurableEmbedding
        (fun x : Fin 1 → ℝ => ENNReal.ofReal (standardGaussianDensityFin1 x)) A)
  · -- The same transport reduces the total mass to the standard one-dimensional Gaussian integral.
    simpa [standardGaussianDensityFin1] using
      (((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ)
        .lintegral_comp_emb (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
          (fun u : ℝ => ENNReal.ofReal (ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) u))))
        .trans (ProbabilityTheory.lintegral_gaussianPDFReal_eq_one 0 (by norm_num))

/-- The standard Gaussian density is log-concave when viewed on `Fin 1 → ℝ`. -/
private lemma standardGaussianDensityFin1_logConcave :
    «problem-11».LogConcave standardGaussianDensityFin1 := by
  refine ⟨fun x => ⟨standardGaussianDensityFin1 x,
    ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : ℝ≥0) (x 0)⟩, rfl, ?_⟩
  intro x y lam hlam0 hlam1
  have hxpos : 0 < standardGaussianDensityFin1 x :=
    ProbabilityTheory.gaussianPDFReal_pos 0 (1 : ℝ≥0) (x 0) (by norm_num)
  have hypos : 0 < standardGaussianDensityFin1 y :=
    ProbabilityTheory.gaussianPDFReal_pos 0 (1 : ℝ≥0) (y 0) (by norm_num)
  have hsqconv : ConvexOn ℝ (Set.univ : Set ℝ) (fun t : ℝ => t ^ 2) :=
    Even.convexOn_pow (𝕜 := ℝ) (show Even 2 by decide)
  have hsq :
      (lam * x 0 + (1 - lam) * y 0) ^ 2 ≤ lam * (x 0) ^ 2 + (1 - lam) * (y 0) ^ 2 := by
    -- The Gaussian exponent is affine in `-x^2 / 2`, so log-concavity reduces to convexity of
    -- the square function on `ℝ`.
    simpa [smul_eq_mul] using
      hsqconv.2 (by simp) (by simp) hlam0 (sub_nonneg.mpr hlam1) (by ring)
  have hreal :
      standardGaussianDensityFin1 (lam • x + (1 - lam) • y) ≥
        Real.rpow (standardGaussianDensityFin1 x) lam *
          Real.rpow (standardGaussianDensityFin1 y) (1 - lam) := by
    have hconst :
        (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ =
          (1 / Real.sqrt (2 * Real.pi)) := by
      field_simp
      ring_nf
    rw [standardGaussianDensityFin1, standardGaussianDensityFin1, standardGaussianDensityFin1,
      ProbabilityTheory.gaussianPDFReal, ProbabilityTheory.gaussianPDFReal,
      ProbabilityTheory.gaussianPDFReal]
    have hxnonneg : 0 ≤ (1 / Real.sqrt (2 * Real.pi) : ℝ) * Real.exp (-(x 0 ^ 2) / 2) := by
      positivity
    have hynonneg : 0 ≤ (1 / Real.sqrt (2 * Real.pi) : ℝ) * Real.exp (-(y 0 ^ 2) / 2) := by
      positivity
    have hmnonneg :
        0 ≤ (1 / Real.sqrt (2 * Real.pi) : ℝ) *
          Real.exp (-((lam * x 0 + (1 - lam) * y 0) ^ 2) / 2) := by
      positivity
    rw [show (x 0 - 0) ^ 2 = x 0 ^ 2 by ring,
      show (y 0 - 0) ^ 2 = y 0 ^ 2 by ring,
      show ((lam • x + (1 - lam) • y) 0 - 0) ^ 2 = (lam * x 0 + (1 - lam) * y 0) ^ 2 by
        simp [smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc]]
    rw [show (2 * Real.pi * ((1 : ℝ≥0) : ℝ)) = 2 * Real.pi by norm_num,
      hconst]
    have hpowConst :
        Real.rpow (1 / Real.sqrt (2 * Real.pi)) lam *
            Real.rpow (1 / Real.sqrt (2 * Real.pi)) (1 - lam) =
          (1 / Real.sqrt (2 * Real.pi) : ℝ) := by
      rw [← Real.rpow_add (by positivity) (by positivity), add_sub_cancel_right]
      simp
    have hexp :
        Real.exp (-((lam * x 0 + (1 - lam) * y 0) ^ 2) / 2) ≥
          Real.exp (-(lam * (x 0) ^ 2 + (1 - lam) * (y 0) ^ 2) / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hsplit :
        Real.exp (-(lam * (x 0) ^ 2 + (1 - lam) * (y 0) ^ 2) / 2) =
          Real.rpow (Real.exp (-(x 0 ^ 2) / 2)) lam *
            Real.rpow (Real.exp (-(y 0 ^ 2) / 2)) (1 - lam) := by
      rw [Real.rpow_natCast, Real.rpow_natCast]
      rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
      ring_nf
    calc
      (1 / Real.sqrt (2 * Real.pi) : ℝ) *
          Real.exp (-((lam * x 0 + (1 - lam) * y 0) ^ 2) / 2)
          ≥ (1 / Real.sqrt (2 * Real.pi) : ℝ) *
              Real.exp (-(lam * (x 0) ^ 2 + (1 - lam) * (y 0) ^ 2) / 2) := by
            gcongr
      _ = (Real.rpow (1 / Real.sqrt (2 * Real.pi)) lam *
            Real.rpow (1 / Real.sqrt (2 * Real.pi)) (1 - lam)) *
            (Real.rpow (Real.exp (-(x 0 ^ 2) / 2)) lam *
              Real.rpow (Real.exp (-(y 0 ^ 2) / 2)) (1 - lam)) := by
            rw [hpowConst, hsplit]
      _ = Real.rpow ((1 / Real.sqrt (2 * Real.pi) : ℝ) * Real.exp (-(x 0 ^ 2) / 2)) lam *
            Real.rpow ((1 / Real.sqrt (2 * Real.pi) : ℝ) * Real.exp (-(y 0 ^ 2) / 2)) (1 - lam) := by
            rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
            ring
  have hxne : (show (⟨standardGaussianDensityFin1 x,
      ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : ℝ≥0) (x 0)⟩ : NNReal) from rfl) ≠ 0 := by
    exact NNReal.coe_ne_zero.2 hxpos.ne'
  have hyne : (show (⟨standardGaussianDensityFin1 y,
      ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : ℝ≥0) (y 0)⟩ : NNReal) from rfl) ≠ 0 := by
    exact NNReal.coe_ne_zero.2 hypos.ne'
  -- Positivity removes the zero-aware branches in the `problem-11` encoding of log-concavity.
  simp [standardGaussianDensityFin1, hxne, hyne]
  exact_mod_cast hreal

/-- The upper-tail integral equals the standard Gaussian probability of `[t, ∞)`. -/
private lemma standardGaussianUpperTail_eq_toReal (t : ℝ) :
    standardGaussianUpperTail t =
      ((ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)) (Set.Ici t)).toReal := by
  -- Rewrite the Gaussian measure as its density integral and simplify the explicit pdf formula.
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0 (by norm_num) (Set.Ici t),
    ENNReal.toReal_ofReal]
  · simp [standardGaussianUpperTail, ProbabilityTheory.gaussianPDFReal, integral_const_mul]
  · exact integral_nonneg fun _ => ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : ℝ≥0) _

/-- Every Gaussian upper tail is strictly positive. -/
private lemma standardGaussianUpperTail_pos (t : ℝ) :
    0 < standardGaussianUpperTail t := by
  let μ : MeasureTheory.Measure ℝ := ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)
  have hIoi_ne_zero : μ (Set.Ioi t) ≠ 0 := by
    -- Absolute continuity in the reverse direction transfers positivity of Lebesgue-open sets to
    -- the Gaussian measure.
    intro hzero
    have hvol_zero : (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Ioi t) = 0 :=
      (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)) hzero
    exact (isOpen_Ioi.measure_pos (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) t
      Set.nonempty_Ioi).ne' hvol_zero
  have hIci_ne_zero : μ (Set.Ici t) ≠ 0 := by
    intro hzero
    have hle : μ (Set.Ioi t) ≤ μ (Set.Ici t) := MeasureTheory.measure_mono Set.Ioi_subset_Ici_self
    have hsmall : μ (Set.Ioi t) = 0 := le_antisymm (by simpa [hzero] using hle) (zero_le _)
    exact hIoi_ne_zero hsmall
  -- Convert the nonzero Gaussian mass of `[t, ∞)` into positivity of its real value.
  rw [standardGaussianUpperTail_eq_toReal]
  exact ENNReal.toReal_pos hIci_ne_zero (MeasureTheory.measure_ne_top _ _)

/-- The Gaussian upper tail is log-concave in the multiplicative sense. -/
private lemma standardGaussianUpperTail_geometric_mean
    (a b lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    standardGaussianUpperTail (lam * a + (1 - lam) * b) ≥
      standardGaussianUpperTail a ^ lam * standardGaussianUpperTail b ^ (1 - lam) := by
  let X : ℝ → Fin 1 → ℝ := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
  let g : (Fin 1 → ℝ) → ℝ := fun x => -x 0
  let gLin : (Fin 1 → ℝ) →ₗ[ℝ] ℝ := -LinearMap.proj 0
  have hg_meas : Measurable g := by
    -- The scalar observable is just the negated coordinate map.
    simpa [g, gLin] using gLin.continuous.measurable
  have hgX_meas : Measurable fun ω => g (X ω) := by
    simpa [X, g] using (measurable_id.neg : Measurable fun ω : ℝ => -ω)
  have hg_convex : ConvexOn ℝ (Set.univ : Set (Fin 1 → ℝ)) g := by
    -- Linear functions are convex on every convex set.
    simpa [g, gLin] using gLin.convexOn (𝕜 := ℝ) (s := (Set.univ : Set (Fin 1 → ℝ))) convex_univ
  have hmain :=
    «problem-11».sublevel_distribution_logConcave
      (P := ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0))
      (X := X) (f := standardGaussianDensityFin1) (g := g)
      ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurable)
      hg_meas hgX_meas hg_convex
      standardGaussianDensityFin1_logConcave
      standardGaussianDensityFin1_isProbabilityDensity
      (-a) (-b) lam hlam0 hlam1
  have hset_mix : {ω : ℝ | g (X ω) ≤ -(lam * a + (1 - lam) * b)} = Set.Ici (lam * a + (1 - lam) * b) := by
    ext ω
    simp [X, g]
    linarith
  have hset_a : {ω : ℝ | g (X ω) ≤ -a} = Set.Ici a := by
    ext ω
    simp [X, g]
    linarith
  have hset_b : {ω : ℝ | g (X ω) ≤ -b} = Set.Ici b := by
    ext ω
    simp [X, g]
    linarith
  -- Rewrite the sublevel probabilities back into the explicit Gaussian tail appearing in the file.
  rw [hset_mix, hset_a, hset_b, ← standardGaussianUpperTail_eq_toReal,
    ← standardGaussianUpperTail_eq_toReal, ← standardGaussianUpperTail_eq_toReal] at hmain
  simpa using hmain

/-- Reflecting the Gaussian tail across the origin swaps upper and lower tails. -/
private lemma standardGaussianUpperTail_reflect (t : ℝ) :
    1 - standardGaussianUpperTail t = standardGaussianUpperTail (-t) := by
  let μ : MeasureTheory.Measure ℝ := ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)
  have hcompl : μ.real (Set.Ici t) + μ.real (Set.Iio t) = 1 := by
    simpa [μ] using
      (MeasureTheory.probReal_add_probReal_compl (μ := μ) measurableSet_Ici)
  have hsymm_measure :
      μ (Set.Iio t) = μ (Set.Ioi (-t)) := by
    -- Symmetry of the centered Gaussian identifies the lower tail at `t` with the reflected upper
    -- open tail at `-t`.
    have hmap :
        μ.map (fun x : ℝ => -x) = μ := by
      simpa [μ] using ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := (1 : ℝ≥0))
    have happly := congrArg (fun ν : MeasureTheory.Measure ℝ => ν (Set.Ioi (-t))) hmap
    rw [MeasureTheory.Measure.map_apply (by fun_prop) measurableSet_Ioi] at happly
    simpa [μ, Set.preimage, Set.mem_Ioi] using happly
  have hsymm_real : μ.real (Set.Iio t) = μ.real (Set.Ici (-t)) := by
    have hopen_closed : μ (Set.Ioi (-t)) = μ (Set.Ici (-t)) := by
      simpa [μ] using
        (MeasureTheory.measure_congr (μ := μ) (MeasureTheory.Ioi_ae_eq_Ici (μ := μ) (a := -t)))
    rw [MeasureTheory.Measure.real, hsymm_measure, hopen_closed]
  -- Combine complementarity with symmetry to identify `1 - G(t)` with `G(-t)`.
  rw [standardGaussianUpperTail_eq_toReal, standardGaussianUpperTail_eq_toReal,
    MeasureTheory.Measure.real] at hcompl hsymm_real ⊢
  linarith

/-- The logarithm of the standard Gaussian upper tail is concave on `ℝ`. -/
private lemma concaveOn_log_standardGaussianUpperTail :
    ConcaveOn ℝ (Set.univ : Set ℝ) (fun t => Real.log (standardGaussianUpperTail t)) := by
  refine (concaveOn_iff_forall_pos).2 ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hab1 : b = 1 - a := by linarith
  have ha_le : a ≤ 1 := by linarith
  have hgeom :=
    standardGaussianUpperTail_geometric_mean x y a ha.le ha_le
  have hxpos : 0 < standardGaussianUpperTail x := standardGaussianUpperTail_pos x
  have hypos : 0 < standardGaussianUpperTail y := standardGaussianUpperTail_pos y
  have hprod_pos :
      0 < standardGaussianUpperTail x ^ a * standardGaussianUpperTail y ^ (1 - a) := by
    positivity
  have hlog :
      Real.log (standardGaussianUpperTail x ^ a * standardGaussianUpperTail y ^ (1 - a)) ≤
        Real.log (standardGaussianUpperTail (a • x + b • y)) := by
    -- Apply `log` to the multiplicative log-concavity inequality using positivity of both sides.
    apply Real.log_le_log hprod_pos
    simpa [smul_eq_mul, hab1] using hgeom
  -- Expand the logarithm of the product back into the affine combination of scalar logs.
  calc
    a • Real.log (standardGaussianUpperTail x) + b • Real.log (standardGaussianUpperTail y)
        = Real.log (standardGaussianUpperTail x ^ a) +
            Real.log (standardGaussianUpperTail y ^ (1 - a)) := by
              rw [smul_eq_mul, smul_eq_mul, Real.log_rpow hxpos.le, Real.log_rpow hypos.le]
              ring_nf
    _ = Real.log (standardGaussianUpperTail x ^ a * standardGaussianUpperTail y ^ (1 - a)) := by
          rw [← Real.log_mul (by positivity) (by positivity)]
    _ ≤ Real.log (standardGaussianUpperTail (a • x + b • y)) := hlog
    _ = Real.log (standardGaussianUpperTail (a • x + b • y)) := rfl

/-- The affine threshold `bᵢ - aᵢᵀx` appearing in each observation term. -/
def observationThreshold {m n : ℕ} (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (i : Fin m)
    (x : Fin n → ℝ) : ℝ :=
  b i - ∑ j : Fin n, a i j * x j

/-
Let m, n ∈ ℕ, let x ∈ ℝ^n be the optimization variable, and for each i = 1, ..., m, let aᵢ ∈ ℝ^n and
bᵢ ∈ ℝ be given. Let v₁, ..., vₘ be independent N(0, 1) random variables. For each i = 1, ..., m,
define yᵢ = sign(a_iᵀ x + vᵢ - bᵢ) = cases 1, & a_iᵀ x + vᵢ ≥ bᵢ,; - 1, & a_iᵀ x + vᵢ < bᵢ. cases
Assume an
observed vector bar y = (bar y₁, ..., bar yₘ) is given, where bar yᵢ ∈ {- 1, 1} for all i. For each
i,
define Pᵢ(x) = prob(yᵢ = 1) = 1{2π}int_{bᵢ - a_iᵀ x}^{∞} e^{- t^2/2}dt. Then prob(yᵢ = - 1) = 1 -
Pᵢ(x),
and the log - likelihood of the observation bar y is l(x) = \sum_{bar yᵢ = 1}log Pᵢ(x) + \sum_{bar
yᵢ =
- 1}log(1 - Pᵢ(x)). Show that the maximum - likelihood estimation problem maximize l(x) is a convex
optimization problem. The variable is x; the measured vector bar y and the parameters aᵢ and bᵢ are
given.
-/
theorem maximumLikelihoodEstimation_is_convex_optimization
    {m n : ℕ} (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (ybar : Fin m → ℤ)
    (hybar : ∀ i, ybar i = 1 ∨ ybar i = -1) :
    let p : (Fin n → ℝ) → Unit → ℝ :=
      fun x _ =>
        Real.exp
          (∑ i : Fin m,
            if ybar i = 1 then
              Real.log
                ((((1 / Real.sqrt (2 * Real.pi)) : ℝ) *
                  (∫ t in Set.Ici ((b i) - ∑ j : Fin n, a i j * x j),
                    Real.exp (-(t ^ 2) / 2))))
            else
              Real.log
                (1 -
                  (((1 / Real.sqrt (2 * Real.pi)) : ℝ) *
                    (∫ t in Set.Ici ((b i) - ∑ j : Fin n, a i j * x j),
                      Real.exp (-(t ^ 2) / 2)))))
    -- l(x) is concave, so maximizing it is a convex optimization problem
    ConcaveOn ℝ (Set.univ : Set (Fin n → ℝ)) (logLikelihood p ()) ∧
    -- the optimal solution set is convex (follows from concavity of l)
    Convex ℝ (maximumLikelihoodEstimators p ()) := by
  dsimp
  set p : (Fin n → ℝ) → Unit → ℝ := fun x _ =>
    Real.exp
      (∑ i : Fin m,
        if ybar i = 1 then
          Real.log
            (standardGaussianUpperTail (observationThreshold a b i x))
        else
          Real.log
            (1 - standardGaussianUpperTail (observationThreshold a b i x)))
  -- Route correction: the next step should isolate the single scalar theorem
  -- `ConcaveOn ℝ Set.univ (fun t => Real.log (standardGaussianUpperTail t))`,
  -- then rewrite the `ybar i = -1` branch via `1 - G(t) = G(-t)` and sum the affine pullbacks.
  have hconc : ConcaveOn ℝ (Set.univ : Set (Fin n → ℝ)) (logLikelihood p ()) := by
    -- Rewrite the outer `log` first so the goal is the finite sum of scalar observation terms.
    have hlog :
        logLikelihood p () =
          fun x =>
            ∑ i : Fin m,
              if ybar i = 1 then
                Real.log (standardGaussianUpperTail (observationThreshold a b i x))
              else
                Real.log (1 - standardGaussianUpperTail (observationThreshold a b i x)) := by
      ext x
      simp [logLikelihood, p, Real.log_exp]
    let thresholdLinear : Fin m → (Fin n → ℝ) →ₗ[ℝ] ℝ := fun i =>
      ∑ j : Fin n, a i j • LinearMap.proj j
    -- Package each threshold `x ↦ b i - ∑ j, a i j * x j` as an affine map.
    let thresholdAffine : Fin m → (Fin n → ℝ) →ᵃ[ℝ] ℝ := fun i =>
      AffineMap.const ℝ (Fin n → ℝ) (b i) - (thresholdLinear i).toAffineMap
    have hthresholdLinear :
        ∀ i : Fin m, ∀ x : Fin n → ℝ, thresholdLinear i x = ∑ j : Fin n, a i j * x j := by
      intro i x
      simp [thresholdLinear, LinearMap.proj_apply]
    have hthreshold :
        ∀ i : Fin m, ∀ x : Fin n → ℝ, thresholdAffine i x = observationThreshold a b i x := by
      intro i x
      simpa [thresholdAffine, observationThreshold] using
        congrArg (fun t : ℝ => b i - t) (hthresholdLinear i x)
    -- Each summand is the pullback of the corresponding scalar branch along that affine map.
    have hbranch :
        ∀ i : Fin m,
          ConcaveOn ℝ (Set.univ : Set (Fin n → ℝ))
            (fun x =>
              if ybar i = 1 then
                Real.log (standardGaussianUpperTail (observationThreshold a b i x))
              else
                Real.log (1 - standardGaussianUpperTail (observationThreshold a b i x))) := by
      intro i
      -- Route correction: the algebraic part is routine, so the only remaining blocker is the
      -- scalar concavity of the Gaussian-tail branch on `ℝ`.
      have hscalar :
          ConcaveOn ℝ (Set.univ : Set ℝ)
            (fun t =>
              if ybar i = 1 then
                Real.log (standardGaussianUpperTail t)
              else
                Real.log (1 - standardGaussianUpperTail t)) := by
        -- Route correction: avoid the heavy derivative route. The imported Prékopa-style theorem
        -- already gives log-concavity of the Gaussian upper tail, and reflection handles the
        -- `ybar i = -1` branch.
        rcases hybar i with h1 | hneg
        · -- The positive observation branch is exactly the scalar concavity lemma.
          simpa [h1] using concaveOn_log_standardGaussianUpperTail
        · -- Reflect the negative branch through `t ↦ -t` so it reuses the same concave kernel.
          have hnegMap :
              ConcaveOn ℝ (Set.univ : Set ℝ)
                (fun t => Real.log (standardGaussianUpperTail (-t))) := by
            simpa [Function.comp] using
              (concaveOn_log_standardGaussianUpperTail.comp_affineMap
                ((-(LinearMap.id : ℝ →ₗ[ℝ] ℝ)).toAffineMap))
          have hfun :
              (fun t =>
                if ybar i = 1 then
                  Real.log (standardGaussianUpperTail t)
                else
                  Real.log (1 - standardGaussianUpperTail t)) =
                fun t => Real.log (standardGaussianUpperTail (-t)) := by
            ext t
            rw [if_neg]
            · rw [standardGaussianUpperTail_reflect]
            · norm_num [hneg]
          rw [hfun]
          exact hnegMap
      refine (ConcaveOn.comp_affineMap (g := thresholdAffine i) hscalar).congr ?_
      intro x hx
      simp [Function.comp, hthreshold i x]
    -- Sum the concave observation terms by finite induction over `Finset.univ`.
    let term : Fin m → (Fin n → ℝ) → ℝ := fun i x =>
      if ybar i = 1 then
        Real.log (standardGaussianUpperTail (observationThreshold a b i x))
      else
        Real.log (1 - standardGaussianUpperTail (observationThreshold a b i x))
    have hsum :
        ∀ s : Finset (Fin m),
          ConcaveOn ℝ (Set.univ : Set (Fin n → ℝ)) (fun x => Finset.sum s fun i => term i x) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simpa [term] using
            (concaveOn_const (𝕜 := ℝ) (s := (Set.univ : Set (Fin n → ℝ))) (c := (0 : ℝ))
              convex_univ)
      | @insert i s hi hs =>
          -- Add one more concave summand to the induction hypothesis.
          simpa [term, Finset.sum_insert, hi] using (hbranch i).add hs
    rw [hlog]
    simpa [term] using hsum Finset.univ
  -- Once concavity is available, convexity of the maximizer set is a generic consequence.
  change
    ConcaveOn ℝ (Set.univ : Set (Fin n → ℝ)) (logLikelihood p ()) ∧
      Convex ℝ (maximumLikelihoodEstimators p ())
  exact ⟨hconc, convex_maximumLikelihoodEstimators_of_concaveOn hconc⟩


end «problem-79»
