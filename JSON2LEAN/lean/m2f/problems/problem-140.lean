import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-140»

-- Exercise_2_19

/- [BLOCK Exercise 2.19 | 12 | thm]
Let n be a natural number, and let λ_1, ..., λ_n be positive real numbers.
Define R_++^n = {x ∈ ℝ^n | xᵢ > 0 for all i = 1, ..., n}.
Define f : R_++^n → ℝ by
f(x) = product_{i=1}^n (1 - e^(-xᵢ))^(lambda_i), where x = (x₁, ..., xₙ).
Show that f is concave on
dom f = {x ∈ ℝ_++^n | sum_{i=1}^n lambda_i e^(-xᵢ) <= 1}.
-/
open scoped BigOperators

theorem concaveOn_prod_one_sub_exp_neg_rpow
    {n : ℕ} (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i) :
    ConcaveOn ℝ
      {x : Fin n → ℝ | (∀ i, 0 < x i) ∧ ∑ i, lam i * Real.exp (-x i) ≤ 1}
      (fun x => ∏ i, Real.rpow (1 - Real.exp (-x i)) (lam i)) := by
  classical
  let s : Set (Fin n → ℝ) :=
    {x : Fin n → ℝ | (∀ i, 0 < x i) ∧ ∑ i, lam i * Real.exp (-x i) ≤ 1}
  let f : (Fin n → ℝ) → ℝ :=
    fun x => ∏ i, Real.rpow (1 - Real.exp (-x i)) (lam i)
  have hs : Convex ℝ s := by
    intro x hx y hy a b ha hb hab
    constructor
    · intro i
      have hx' := hx.1 i
      have hy' := hy.1 i
      have hcoord : (a • x + b • y) i = a * x i + b * y i := by
        simp [smul_eq_mul]
      rw [hcoord]
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simp [ha0, hb1, hy']
      · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        exact add_pos_of_pos_of_nonneg (mul_pos ha' hx') (mul_nonneg hb hy'.le)
    · have hcoord_conv :
        ∀ i,
          Real.exp (-((a • x + b • y) i)) ≤
            a * Real.exp (-x i) + b * Real.exp (-y i) := by
        intro i
        simpa [smul_eq_mul, mul_add, add_mul, neg_add, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc, mul_comm, mul_left_comm, mul_assoc]
          using
            (convexOn_exp.2 (show (-x i : ℝ) ∈ Set.univ by simp)
              (show (-y i : ℝ) ∈ Set.univ by simp) ha hb hab)
      calc
        ∑ i, lam i * Real.exp (-((a • x + b • y) i))
            ≤ ∑ i, lam i * (a * Real.exp (-x i) + b * Real.exp (-y i)) := by
                exact Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_left (hcoord_conv i) (hlam i).le
        _ = ∑ i, (a * (lam i * Real.exp (-x i)) + b * (lam i * Real.exp (-y i))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = (∑ i, a * (lam i * Real.exp (-x i))) + ∑ i, b * (lam i * Real.exp (-y i)) := by
              rw [Finset.sum_add_distrib]
        _ = a * ∑ i, lam i * Real.exp (-x i) + b * ∑ i, lam i * Real.exp (-y i) := by
              rw [Finset.mul_sum, Finset.mul_sum]
        _ ≤ 1 := by
              nlinarith [hx.2, hy.2]
  refine ⟨hs, ?_⟩
  · intro x hx y hy a b ha hb hab
    -- Route correction: the remaining work is the one-variable calculus argument on the segment
    -- `t ↦ (1 - t) • x + t • y`, with the product rewritten as `exp (sum log ...)`.
    let z : ℝ → Fin n → ℝ := fun t => (1 - t) • x + t • y
    let Φ : ℝ → ℝ := fun t => ∑ i, lam i * Real.log (1 - Real.exp (-z t i))
    let G : ℝ → ℝ := fun t => Real.exp (Φ t)
    have hseg : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) 1 → z t ∈ s := by
      intro t ht
      -- Every point on the scalar segment stays in the convex domain `s`.
      have hsum : (1 - t) + t = 1 := by ring
      simpa [z] using hs hx hy (sub_nonneg.mpr ht.2) ht.1 hsum
    have hone_sub_exp_pos :
        ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) 1 → ∀ i, 0 < 1 - Real.exp (-z t i) := by
      intro t ht i
      -- Positivity of the segment coordinates forces the logarithm arguments to stay positive.
      have hz_pos : 0 < z t i := (hseg ht).1 i
      have hexp_lt : Real.exp (-z t i) < 1 := by
        rw [Real.exp_lt_one_iff]
        linarith
      linarith
    have hG_eq : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) 1 → f (z t) = G t := by
      intro t ht
      -- Rewrite the product through `rpow = exp ∘ (log * ·)` so only elementary calculus remains.
      have hpos : ∀ i, 0 < 1 - Real.exp (-z t i) := hone_sub_exp_pos ht
      calc
        f (z t) = ∏ i, Real.exp (Real.log (1 - Real.exp (-z t i)) * lam i) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          simpa using (Real.rpow_def_of_pos (hpos i) (lam i))
        _ = Real.exp (∑ i, Real.log (1 - Real.exp (-z t i)) * lam i) := by
          rw [← Real.exp_sum]
        _ = G t := by
          simp [G, Φ, mul_comm]
    have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    have hb_mem : b ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact hb
      · linarith [ha, hab]
    have hG0 : G 0 = f x := by
      -- The line restriction starts at the left endpoint.
      simpa [z] using (hG_eq h0_mem).symm
    have hG1 : G 1 = f y := by
      -- The line restriction ends at the right endpoint.
      simpa [z] using (hG_eq h1_mem).symm
    have hGb : G b = f (a • x + b • y) := by
      -- The interpolation parameter `b` corresponds to the original convex combination.
      have h_one_sub_b : 1 - b = a := by linarith
      simpa [z, h_one_sub_b] using (hG_eq hb_mem).symm
    let δ : Fin n → ℝ := fun i => y i - x i
    let Φ' : ℝ → ℝ :=
      fun t => ∑ i, lam i * (δ i * Real.exp (-z t i) / (1 - Real.exp (-z t i)))
    let Φ'' : ℝ → ℝ :=
      fun t => -∑ i, lam i * Real.exp (-z t i) * (δ i) ^ 2 / (1 - Real.exp (-z t i)) ^ 2
    let G' : ℝ → ℝ := fun t => G t * Φ' t
    let G'' : ℝ → ℝ := fun t => G t * (Φ'' t + (Φ' t) ^ 2)
    have hz_eq : ∀ t i, z t i = x i + t * δ i := by
      intro t i
      -- Rewrite the segment coordinate into affine form once so the scalar derivatives are one-dimensional.
      simp [z, δ, smul_eq_mul]
      ring
    have hcoord_log_hasDerivAt :
        ∀ i {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
          HasDerivAt (fun u => Real.log (1 - Real.exp (-z u i)))
            (δ i * Real.exp (-z t i) / (1 - Real.exp (-z t i))) t := by
      intro i t ht
      -- Differentiate the coordinate logarithm through `log ∘ (1 - exp ∘ (-affine))`.
      have h_aff : HasDerivAt (fun u : ℝ => x i + u * δ i) (δ i) t := by
        simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
          ((hasDerivAt_id' t).mul_const (δ i)).const_add (x i)
      have h_exp : HasDerivAt (fun u : ℝ => Real.exp (-(x i + u * δ i)))
          (-Real.exp (-(x i + t * δ i)) * δ i) t := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          HasDerivAt.exp (HasDerivAt.neg h_aff)
      have h_inner : HasDerivAt (fun u : ℝ => 1 - Real.exp (-(x i + u * δ i)))
          (Real.exp (-(x i + t * δ i)) * δ i) t := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc] using (HasDerivAt.const_sub (1 : ℝ) h_exp)
      have hlog := h_inner.log (by
        simpa [hz_eq] using (hone_sub_exp_pos ht i).ne')
      simpa [hz_eq, mul_comm, mul_left_comm, mul_assoc] using hlog
    have hcoord_logDeriv_hasDerivAt :
        ∀ i {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
          HasDerivAt (fun u => δ i * Real.exp (-z u i) / (1 - Real.exp (-z u i)))
            (-Real.exp (-z t i) * (δ i) ^ 2 / (1 - Real.exp (-z t i)) ^ 2) t := by
      intro i t ht
      -- Differentiate the explicit first-derivative formula using the quotient rule on the affine coordinate.
      have h_aff : HasDerivAt (fun u : ℝ => x i + u * δ i) (δ i) t := by
        simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
          ((hasDerivAt_id' t).mul_const (δ i)).const_add (x i)
      have h_exp : HasDerivAt (fun u : ℝ => Real.exp (-(x i + u * δ i)))
          (-Real.exp (-(x i + t * δ i)) * δ i) t := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          HasDerivAt.exp (HasDerivAt.neg h_aff)
      have h_den : HasDerivAt (fun u : ℝ => 1 - Real.exp (-(x i + u * δ i)))
          (Real.exp (-(x i + t * δ i)) * δ i) t := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc] using (HasDerivAt.const_sub (1 : ℝ) h_exp)
      have h_ratio :
          HasDerivAt
            (fun u : ℝ => Real.exp (-(x i + u * δ i)) / (1 - Real.exp (-(x i + u * δ i))))
            (-Real.exp (-(x i + t * δ i)) * δ i / (1 - Real.exp (-(x i + t * δ i))) ^ 2) t := by
        have h_div := h_exp.div h_den (by
          simpa [hz_eq] using (hone_sub_exp_pos ht i).ne')
        convert h_div using 1
        set e : ℝ := Real.exp (-(x i + t * δ i))
        set d : ℝ := 1 - e
        change -e * δ i / d ^ 2 = ((-e * δ i * d - e * (e * δ i)) / d ^ 2)
        subst d
        field_simp [(hone_sub_exp_pos ht i).ne']
        ring
      convert (HasDerivAt.const_mul (δ i) h_ratio) using 1
      · funext u
        simp [hz_eq, div_eq_mul_inv, mul_assoc]
      · rw [hz_eq]
        ring_nf
    have hPhi_cont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1) := by
      -- Continuity of the logarithmic sum on the closed interval follows from the coordinate derivatives.
      refine continuousOn_finset_sum Finset.univ ?_
      intro i hi
      have hcont_i : ContinuousOn (fun t => Real.log (1 - Real.exp (-z t i))) (Set.Icc (0 : ℝ) 1) := by
        intro t ht
        exact (hcoord_log_hasDerivAt i ht).continuousAt.continuousWithinAt
      simpa using (continuousOn_const.mul hcont_i)
    have hPhi_hasDerivAt :
        ∀ {t : ℝ}, t ∈ Set.Ioo (0 : ℝ) 1 → HasDerivAt Φ (Φ' t) t := by
      intro t ht
      -- Sum the coordinate derivatives to obtain `Φ'`.
      convert
        (HasDerivAt.sum (u := Finset.univ) fun i _ => HasDerivAt.const_mul (lam i)
          (hcoord_log_hasDerivAt i ⟨ht.1.le, ht.2.le⟩)) using 1
      funext u
      simp [Φ]
    have hPhi'_hasDerivAt :
        ∀ {t : ℝ}, t ∈ Set.Ioo (0 : ℝ) 1 → HasDerivAt Φ' (Φ'' t) t := by
      intro t ht
      -- Sum the differentiated quotient formulas to obtain `Φ''`.
      convert
        (HasDerivAt.sum (u := Finset.univ) fun i _ => HasDerivAt.const_mul (lam i)
          (hcoord_logDeriv_hasDerivAt i ⟨ht.1.le, ht.2.le⟩)) using 1
      · funext u
        simp [Φ']
      · simp [Φ'']
        have hterm :
            (∑ x, lam x * (-(Real.exp (-z t x) * δ x ^ 2) / (1 - Real.exp (-z t x)) ^ 2)) =
              ∑ x, -(lam x * Real.exp (-z t x) * δ x ^ 2 / (1 - Real.exp (-z t x)) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        rw [hterm]
        simpa using
          (Finset.sum_neg_distrib
            (fun i : Fin n => lam i * Real.exp (-z t i) * δ i ^ 2 / (1 - Real.exp (-z t i)) ^ 2)).symm
    have hG_cont : ContinuousOn G (Set.Icc (0 : ℝ) 1) := by
      -- Exponentiating the continuous logarithmic profile gives continuity of the segment restriction.
      simpa [G, Function.comp] using Real.continuous_exp.comp_continuousOn hPhi_cont
    have hG_hasDerivAt :
        ∀ {t : ℝ}, t ∈ Set.Ioo (0 : ℝ) 1 → HasDerivAt G (G' t) t := by
      intro t ht
      -- Differentiate `G = exp ∘ Φ`.
      simpa [G, G'] using HasDerivAt.exp (hPhi_hasDerivAt ht)
    have hG'_hasDerivAt :
        ∀ {t : ℝ}, t ∈ Set.Ioo (0 : ℝ) 1 → HasDerivAt G' (G'' t) t := by
      intro t ht
      -- Differentiate `G' = G * Φ'` and collect the two terms into `G''`.
      convert (hG_hasDerivAt ht).mul (hPhi'_hasDerivAt ht) using 1
      ring
    have hcurvature_nonpos :
        ∀ {t : ℝ}, t ∈ Set.Ioo (0 : ℝ) 1 → Φ'' t + (Φ' t) ^ 2 ≤ 0 := by
      intro t ht
      -- Apply the weighted Titu/Cauchy inequality to the first-derivative sum and compare with `-Φ''`.
      let w : Fin n → ℝ :=
        fun i => lam i * (δ i * Real.exp (-z t i) / (1 - Real.exp (-z t i)))
      let g : Fin n → ℝ := fun i => lam i * Real.exp (-z t i)
      have hg_pos : ∀ i, 0 < g i := by
        intro i
        exact mul_pos (hlam i) (Real.exp_pos _)
      have hden_pos : ∀ i, 0 < 1 - Real.exp (-z t i) := hone_sub_exp_pos ⟨ht.1.le, ht.2.le⟩
      by_cases huniv : (Finset.univ : Finset (Fin n)).Nonempty
      · have hsum_pos : 0 < ∑ i, g i := by
          simpa [g] using Finset.sum_pos (fun i hi => hg_pos i) huniv
        have hsum_le_one : ∑ i, g i ≤ 1 := by
          simpa [g] using (hseg ⟨ht.1.le, ht.2.le⟩).2
        have hsq_div :
            (∑ i, w i) ^ 2 / ∑ i, g i ≤ ∑ i, w i ^ 2 / g i := by
          simpa [w, g] using
            (Finset.sq_sum_div_le_sum_sq_div Finset.univ w (by
              intro i hi
              exact hg_pos i))
        have hsq_left :
            (∑ i, w i) ^ 2 ≤ (∑ i, w i) ^ 2 / ∑ i, g i := by
          calc
            (∑ i, w i) ^ 2 = (∑ i, w i) ^ 2 * 1 := by ring
            _ ≤ (∑ i, w i) ^ 2 * (∑ i, g i)⁻¹ := by
              gcongr
              exact (one_le_inv₀ hsum_pos).2 hsum_le_one
            _ = (∑ i, w i) ^ 2 / ∑ i, g i := by rw [div_eq_mul_inv]
        have hsq_right :
            ∑ i, w i ^ 2 / g i =
              ∑ i, lam i * Real.exp (-z t i) * (δ i) ^ 2 / (1 - Real.exp (-z t i)) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          dsimp [w, g]
          field_simp [(hg_pos i).ne', (hden_pos i).ne']
        have hphi'_eq : Φ' t = ∑ i, w i := by
          simp [Φ', w]
        have hphi''_eq :
            -Φ'' t = ∑ i, lam i * Real.exp (-z t i) * (δ i) ^ 2 / (1 - Real.exp (-z t i)) ^ 2 := by
          simp [Φ'']
        have hsquare : (Φ' t) ^ 2 ≤ -Φ'' t := by
          rw [hphi'_eq, hphi''_eq]
          exact le_trans hsq_left (hsq_div.trans_eq hsq_right)
        nlinarith
      · have huniv_empty : (Finset.univ : Finset (Fin n)) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp huniv
        simp [Φ', Φ'', huniv_empty]
    have hG''_nonpos :
        ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), G'' t ≤ 0 := by
      intro t ht
      rw [interior_Icc] at ht
      -- Since `G(t) > 0`, the sign of `G''` is the sign of `Φ'' + (Φ')²`.
      simpa [G''] using
        mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ G t by exact (Real.exp_pos _).le)
          (hcurvature_nonpos ht)
    have hconcG : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) G := by
      -- The one-variable second-derivative criterion closes the segment argument.
      apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (0 : ℝ) 1) hG_cont
      · intro t ht
        rw [interior_Icc] at ht ⊢
        exact (hG_hasDerivAt ht).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht ⊢
        exact (hG'_hasDerivAt ht).hasDerivWithinAt
      · exact hG''_nonpos
    have hsegment :
        a * G 0 + b * G 1 ≤ G (a • (0 : ℝ) + b • (1 : ℝ)) := by
      -- Concavity of `G` on `[0,1]` gives the desired midpoint inequality on the scalar segment.
      exact hconcG.2 h0_mem h1_mem ha hb hab
    have harg : a • (0 : ℝ) + b • (1 : ℝ) = b := by
      simp [smul_eq_mul]
    have hfinal : a * f x + b * f y ≤ f (a • x + b • y) := by
      simpa [harg, hG0, hG1, hGb] using hsegment
    simpa [f, smul_eq_mul] using hfinal

end «problem-140»
