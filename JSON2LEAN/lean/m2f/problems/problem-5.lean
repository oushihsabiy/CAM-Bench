import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-5»

/- [BLOCK Exercise 6.3-(a) | 14 | thm]
Let n ∈ ℕ. For θ ∈ ℝ^n, define p_{θ}(x)=a(θ)exp(θ^{T}x), x ∈ ℝ_{+}^{n}, where
a(θ)=≤ft(∈t_{ℝ_{+}^{n}} exp(θ^{T}x)dx)^{-1} whenever the integral is finite. Here dx is Lebesgue
measure, θ^{T}x=sum_{i=1}^{n}θ_i xᵢ, and ℝ_{+}^{n}={x=(x₁,dots,xₙ)∈ ℝ^{n}: xᵢ ≥ 0 for i=1,dots,n}.
Prove that ∈t_{ℝ_{+}^{n}} exp(θ^{T}x)dx < ∞ quad if and only if quad θ_i < 0 for all i=1,dots,n,
and, in this case, a(θ)=prod_{i=1}^{n}(-θ_i), p_{θ}(x)=≤ft(prod_{i=1}^{n}(-θ_i))exp(θ^{T}x) quad for
all x∈ ℝ_{+}^{n}.
-/
theorem exp_integral_on_nonnegative_orthant_finite_iff
    (n : ℕ) (θ : Fin n → ℝ) :
    let orthant : Set (Fin n → ℝ) := {x | ∀ i, 0 ≤ x i}
    let kernel : (Fin n → ℝ) → ℝ :=
      fun x => Real.exp (∑ i, θ i * x i)
    let integral : ℝ := ∫ x : Fin n → ℝ in orthant, kernel x
    let normalizer : ℝ := integral⁻¹
    -- Finiteness iff all components are negative
    -- `IntegrableOn` uses the norm, but `kernel x = exp _` is positive, so
    -- this is the right formal version of finiteness of the nonnegative integral.
    ((MeasureTheory.IntegrableOn kernel orthant) ↔ (∀ i, θ i < 0)) ∧
    -- When all negative, the integral, normalizer a(θ), and density p_θ
    -- have the expected product forms. Empty products cover the n = 0 case.
    ((∀ i, θ i < 0) →
      integral = ∏ i : Fin n, (-θ i)⁻¹ ∧
      normalizer = ∏ i : Fin n, (-θ i) ∧
      ∀ x ∈ orthant,
        normalizer * kernel x = (∏ i : Fin n, (-θ i)) * kernel x) := by
  dsimp
  set orthant : Set (Fin n → ℝ) := {x | ∀ i, 0 ≤ x i}
  set kernel : (Fin n → ℝ) → ℝ := fun x => Real.exp (∑ i, θ i * x i)
  set integral : ℝ := ∫ x : Fin n → ℝ in orthant, kernel x
  change ((MeasureTheory.IntegrableOn kernel orthant) ↔ (∀ i, θ i < 0)) ∧
      ((∀ i, θ i < 0) →
        integral = ∏ i : Fin n, (-θ i)⁻¹ ∧
        integral⁻¹ = ∏ i : Fin n, (-θ i) ∧
        ∀ x ∈ orthant, integral⁻¹ * kernel x = (∏ i : Fin n, (-θ i)) * kernel x)

  -- Rewrite the orthant and the kernel in product form so Fubini applies directly.
  have horthant : orthant = Set.univ.pi (fun i : Fin n => Set.Ici (0 : ℝ)) := by
    ext x
    simp [orthant, Pi.le_def]
  have hkernel_prod :
      ∀ x : Fin n → ℝ, kernel x = ∏ i : Fin n, Real.exp (θ i * x i) := by
    intro x
    simp [kernel, Real.exp_sum]

  -- When every coordinate of `θ` is negative, the orthant integral factorizes into
  -- one-dimensional exponential tails.
  have hnegative_case :
      ∀ hneg : ∀ i, θ i < 0,
        MeasureTheory.IntegrableOn kernel orthant ∧
          integral = ∏ i : Fin n, (-θ i)⁻¹ := by
    intro hneg
    have h1d_integrable :
        ∀ i : Fin n,
          MeasureTheory.Integrable
            (fun x : ℝ => Real.exp (θ i * x))
            (MeasureTheory.volume.restrict (Set.Ici 0)) := by
      intro i
      -- Replace `Ici` with `Ioi` and invoke the standard one-dimensional theorem.
      rw [← MeasureTheory.integrableOn_univ, MeasureTheory.IntegrableOn,
        MeasureTheory.Measure.restrict_univ]
      exact (integrableOn_Ici_iff_integrableOn_Ioi).2 <|
        integrableOn_exp_mul_Ioi (hneg i) 0
    have hkernel_integrable : MeasureTheory.IntegrableOn kernel orthant := by
      rw [MeasureTheory.IntegrableOn, horthant, MeasureTheory.volume_pi,
        MeasureTheory.Measure.restrict_pi_pi]
      refine (MeasureTheory.Integrable.fintype_prod h1d_integrable).congr ?_
      exact Filter.Eventually.of_forall (fun x => (hkernel_prod x).symm)
    have hintegral_formula :
        ∫ x : Fin n → ℝ in orthant, kernel x = ∏ i : Fin n, (-θ i)⁻¹ := by
      rw [horthant, MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
      calc
        ∫ x : Fin n → ℝ,
            kernel x ∂MeasureTheory.Measure.pi
              (fun i => MeasureTheory.volume.restrict (Set.Ici 0)) =
            ∫ x : Fin n → ℝ,
              ∏ i : Fin n, Real.exp (θ i * x i) ∂MeasureTheory.Measure.pi
                (fun i => MeasureTheory.volume.restrict (Set.Ici 0)) := by
              refine MeasureTheory.integral_congr_ae ?_
              exact Filter.Eventually.of_forall hkernel_prod
        _ = ∏ i : Fin n,
              ∫ x : ℝ, Real.exp (θ i * x) ∂(MeasureTheory.volume.restrict (Set.Ici 0)) := by
              simpa using
                (MeasureTheory.integral_fintype_prod_eq_prod
                  (fun i : Fin n => fun x : ℝ => Real.exp (θ i * x))
                  (μ := fun i : Fin n => MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))))
        _ = ∏ i : Fin n, (-θ i)⁻¹ := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              calc
                ∫ x : ℝ, Real.exp (θ i * x) ∂(MeasureTheory.volume.restrict (Set.Ici 0))
                    = ∫ x : ℝ in Set.Ici 0, Real.exp (θ i * x) := by
                      rfl
                _ = ∫ x : ℝ in Set.Ioi 0, Real.exp (θ i * x) := by
                      simpa using
                        (MeasureTheory.setIntegral_congr_set
                          (μ := MeasureTheory.volume)
                          (f := fun x : ℝ => Real.exp (θ i * x))
                          (MeasureTheory.Ioi_ae_eq_Ici :
                            Set.Ioi (0 : ℝ) =ᵐ[MeasureTheory.volume] Set.Ici 0)).symm
                _ = -Real.exp (θ i * 0) / θ i := integral_exp_mul_Ioi (hneg i) 0
                _ = (-θ i)⁻¹ := by
                      simp [div_eq_mul_inv]
    exact ⟨hkernel_integrable, by simpa [integral] using hintegral_formula⟩

  -- If one coordinate is nonnegative, there is an infinite slab inside the orthant on
  -- which the kernel is bounded below by a positive constant, so integrability fails.
  have hnonnegative_coordinate :
      ∀ i : Fin n, 0 ≤ θ i → ¬ MeasureTheory.IntegrableOn kernel orthant := by
    intro i hθi hint
    let slab : Set (Fin n → ℝ) :=
      Set.univ.pi (fun j : Fin n => if j = i then Set.Ioi (0 : ℝ) else Set.Icc 0 1)
    have hslab_subset : slab ⊆ orthant := by
      intro x hx j
      by_cases hji : j = i
      · have hxi : x j ∈ Set.Ioi (0 : ℝ) := by
          simpa [slab, hji] using hx j (by simp)
        exact le_of_lt hxi
      · have hxj : x j ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [slab, hji] using hx j (by simp)
        exact hxj.1
    have hslab_meas : MeasurableSet slab := by
      refine MeasurableSet.univ_pi ?_
      intro j
      by_cases hji : j = i <;> simp [hji]
    have hkernel_slab : MeasureTheory.IntegrableOn kernel slab :=
      hint.mono_set hslab_subset
    let c : ℝ := Real.exp (∑ j : Fin n, min (θ j) 0)
    have hc_pos : 0 < c := by
      simpa [c] using Real.exp_pos (∑ j : Fin n, min (θ j) 0)
    have hbound : ∀ x ∈ slab, c ≤ kernel x := by
      intro x hx
      have hsum : (∑ j : Fin n, min (θ j) 0) ≤ ∑ j : Fin n, θ j * x j := by
        refine Finset.sum_le_sum ?_
        intro j hj
        by_cases hji : j = i
        · subst j
          have hxi : 0 < x i := by
            simpa [slab] using hx i (by simp)
          rw [min_eq_right hθi]
          nlinarith
        · have hxj : x j ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [slab, hji] using hx j (by simp)
          by_cases hθj : 0 ≤ θ j
          · rw [min_eq_right hθj]
            nlinarith [hxj.1, hθj]
          · have hθj' : θ j < 0 := lt_of_not_ge hθj
            rw [min_eq_left (le_of_lt hθj')]
            have hmul : θ j ≤ θ j * x j := by
              have hmul' := mul_le_mul_of_nonpos_left hxj.2 hθj'.le
              simpa [mul_comm] using hmul'
            simpa using hmul
      exact Real.exp_monotone <| by simpa [kernel, c] using hsum
    have hconst_integrable : MeasureTheory.IntegrableOn (fun _ : Fin n → ℝ => c) slab := by
      rw [MeasureTheory.IntegrableOn] at hkernel_slab ⊢
      refine MeasureTheory.Integrable.mono'
        hkernel_slab MeasureTheory.aestronglyMeasurable_const ?_
      rw [MeasureTheory.ae_restrict_iff' hslab_meas]
      exact Filter.Eventually.of_forall (fun x hx => by
        have hxbound := hbound x hx
        simpa [Real.norm_of_nonneg hc_pos.le, abs_of_nonneg (Real.exp_pos _).le] using hxbound)
    have hslab_volume : MeasureTheory.volume slab = ⊤ := by
      simpa [slab] using
        (show MeasureTheory.volume
            (Set.univ.pi (fun j : Fin n => if j = i then Set.Ioi (0 : ℝ) else Set.Icc 0 1)) = ⊤ from by
          rw [MeasureTheory.volume_pi_pi]
          rw [Finset.prod_eq_single i]
          · simp
          · intro j _ hji
            simp [hji, Real.volume_Icc]
          · simp)
    have hconst_not_integrable : ¬ MeasureTheory.IntegrableOn (fun _ : Fin n → ℝ => c) slab := by
      intro hconst
      rcases (MeasureTheory.integrableOn_const_iff (C := c)).1 hconst with hzero | hfinite
      · exact hc_pos.ne' (by simpa using hzero)
      · have hnotlt : ¬ MeasureTheory.volume slab < ⊤ := by
          simpa [hslab_volume]
        exact hnotlt hfinite
    exact hconst_not_integrable hconst_integrable

  refine ⟨?_, ?_⟩
  · constructor
    · intro hint i
      by_contra hθi
      have hθi_nonneg : 0 ≤ θ i := by
        linarith
      exact hnonnegative_coordinate i hθi_nonneg hint
    · intro hneg
      exact (hnegative_case hneg).1
  · intro hneg
    rcases hnegative_case hneg with ⟨_, hintegral⟩
    -- After the integral is known, the normalizer and the displayed density identity are
    -- just rewrites.
    have hnormalizer : integral⁻¹ = ∏ i : Fin n, (-θ i) := by
      calc
        integral⁻¹ = (∏ i : Fin n, (-θ i)⁻¹)⁻¹ := by
          rw [hintegral]
        _ = ∏ i : Fin n, ((-θ i)⁻¹)⁻¹ := by
          rw [← Finset.prod_inv_distrib]
        _ = ∏ i : Fin n, (-θ i) := by
          simp
    refine ⟨hintegral, hnormalizer, ?_⟩
    intro x hx
    rw [hnormalizer]

end «problem-5»
