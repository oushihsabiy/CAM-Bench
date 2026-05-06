import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-115»
/-
Let p > 1 and D = {(x, t)∈ℝ^n×ℝ: t > ‖x‖_p}. Define f(x, t) = ‖x‖_p^p / t^(p−1). Prove that f is
convex on D.
-/
theorem lp_power_over_t_convexOn
    {n : ℕ} {p : ℝ}
    (hp : 1 < p) :
    let pNormPow : (Fin n → ℝ) → ℝ := fun x => ∑ i : Fin n, Real.rpow (|x i|) p
    let pNorm : (Fin n → ℝ) → ℝ := fun x => Real.rpow (pNormPow x) (1 / p)
    ConvexOn ℝ
      {xt : (Fin n → ℝ) × ℝ | xt.2 > pNorm xt.1}
      (fun xt : (Fin n → ℝ) × ℝ => pNormPow xt.1 / Real.rpow xt.2 (p - 1)) := by
  dsimp
  set pNormPow : (Fin n → ℝ) → ℝ := fun x => ∑ i : Fin n, Real.rpow (|x i|) p
  set pNorm : (Fin n → ℝ) → ℝ := fun x => Real.rpow (pNormPow x) (1 / p)
  change ConvexOn ℝ {xt : (Fin n → ℝ) × ℝ | xt.2 > pNorm xt.1}
    (fun xt : (Fin n → ℝ) × ℝ => pNormPow xt.1 / Real.rpow xt.2 (p - 1))
  let q : ENNReal := ENNReal.ofReal p
  have hp_pos : 0 < p := by linarith
  have hq_toReal : q.toReal = p := by
    simp [q, ENNReal.toReal_ofReal, hp_pos.le]
  letI : Fact (1 ≤ q) := by
    rw [fact_iff]
    simpa [q, ENNReal.ofReal_one] using (ENNReal.ofReal_le_ofReal hp.le)
  -- We identify the local `pNorm` with the finite-dimensional `L^p` norm from mathlib.
  have h_pNorm_eq_norm (x : Fin n → ℝ) : pNorm x = ‖WithLp.toLp q x‖ := by
    simp [pNorm, pNormPow, PiLp.norm_eq_sum (f := WithLp.toLp q x)
      (by simpa [hq_toReal] using hp_pos), hq_toReal, Real.norm_eq_abs]
  -- The norm model immediately gives nonnegativity and scaling rules for `pNorm`.
  have h_pNorm_nonneg (x : Fin n → ℝ) : 0 ≤ pNorm x := by
    rw [h_pNorm_eq_norm]
    exact norm_nonneg _
  have h_pNormPow_eq (x : Fin n → ℝ) : pNormPow x = (pNorm x) ^ p := by
    have hsum_nonneg : 0 ≤ pNormPow x := by
      simp [pNormPow]
      positivity
    have hpow : ((pNormPow x) ^ (1 / p)) ^ p = pNormPow x := by
      rw [← Real.rpow_mul hsum_nonneg, one_div, inv_mul_cancel₀ hp_pos.ne', Real.rpow_one]
    simpa [pNorm] using hpow.symm
  have h_pNorm_smul (c : ℝ) (x : Fin n → ℝ) : pNorm (c • x) = |c| * pNorm x := by
    calc
      pNorm (c • x) = ‖WithLp.toLp q (c • x)‖ := h_pNorm_eq_norm _
      _ = ‖c • WithLp.toLp q x‖ := by simp
      _ = |c| * ‖WithLp.toLp q x‖ := by simpa [Real.norm_eq_abs] using norm_smul c (WithLp.toLp q x)
      _ = |c| * pNorm x := by rw [h_pNorm_eq_norm]
  -- This is the perspective rewrite: the original function equals `t * ‖x / t‖_p^p` for `t > 0`.
  have h_perspective (x : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
      pNormPow x / Real.rpow t (p - 1) = t * (pNorm ((1 / t) • x)) ^ p := by
    have ht_rpow_pos : 0 < t ^ p := Real.rpow_pos_of_pos ht _
    calc
      pNormPow x / Real.rpow t (p - 1)
          = (pNorm x) ^ p / Real.rpow t (p - 1) := by rw [h_pNormPow_eq]
      _ = t * ((pNorm x) / t) ^ p := by
        symm
        rw [Real.div_rpow (h_pNorm_nonneg x) ht.le]
        change t * (pNorm x ^ p / t ^ p) = pNorm x ^ p / (t ^ (p - 1))
        rw [Real.rpow_sub ht p 1, Real.rpow_one]
        field_simp [ht.ne', ht_rpow_pos.ne']
      _ = t * (pNorm ((1 / t) • x)) ^ p := by
        congr 1
        rw [h_pNorm_smul, abs_of_pos (one_div_pos.mpr ht)]
        field_simp [ht.ne']
  -- Convexity of `pNorm` is inherited from convexity of the norm on the `PiLp` space.
  have h_conv_pNorm : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) pNorm := by
    refine (convexOn_univ_norm.comp_linearMap
      ((PiLp.continuousLinearEquiv q ℝ (fun _ : Fin n => ℝ)).symm.toLinearMap)).congr ?_
    intro x _
    simpa [Function.comp] using (h_pNorm_eq_norm x).symm
  refine ⟨?_, ?_⟩
  · -- The domain is the strict epigraph of the convex function `pNorm`.
    simpa [gt_iff_lt] using h_conv_pNorm.convex_strict_epigraph
  · intro xt hxt yt hyt a b ha hb hab
    rcases xt with ⟨x, t⟩
    rcases yt with ⟨y, u⟩
    dsimp at hxt hyt ⊢
    have ht_pos : 0 < t := lt_of_le_of_lt (h_pNorm_nonneg x) hxt
    have hu_pos : 0 < u := lt_of_le_of_lt (h_pNorm_nonneg y) hyt
    set s : ℝ := a * t + b * u
    set α : ℝ := a * t / s
    set β : ℝ := b * u / s
    -- Route correction: instead of expanding coordinates, we switch to the standard perspective
    -- argument and normalize by the positive scalar `s = a * t + b * u`.
    have hs_pos : 0 < s := by
      rcases lt_or_eq_of_le ha with ha_pos | rfl
      · dsimp [s]
        linarith [mul_pos ha_pos ht_pos, mul_nonneg hb hu_pos.le]
      · have hb_eq : b = 1 := by linarith
        subst hb_eq
        dsimp [s]
        simpa using hu_pos
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      positivity
    have hβ_nonneg : 0 ≤ β := by
      dsimp [β]
      positivity
    have hsα : s * α = a * t := by
      dsimp [α]
      field_simp [hs_pos.ne']
    have hsβ : s * β = b * u := by
      dsimp [β]
      field_simp [hs_pos.ne']
    have hαβ : α + β = 1 := by
      calc
        α + β = (a * t + b * u) / s := by
          dsimp [α, β]
          ring
        _ = s / s := by rw [show a * t + b * u = s by rfl]
        _ = 1 := by field_simp [hs_pos.ne']
    -- The normalized midpoint is exactly the convex combination of the normalized points.
    have h_scale :
        (1 / s) • (a • x + b • y) = α • ((1 / t) • x) + β • ((1 / u) • y) := by
      ext i
      dsimp [α, β, s]
      field_simp [hs_pos.ne', ht_pos.ne', hu_pos.ne']
    have h_norm_combo :
        pNorm ((1 / s) • (a • x + b • y)) ≤
          α * pNorm ((1 / t) • x) + β * pNorm ((1 / u) • y) := by
      calc
        pNorm ((1 / s) • (a • x + b • y))
            = pNorm (α • ((1 / t) • x) + β • ((1 / u) • y)) := by rw [h_scale]
        _ ≤ α * pNorm ((1 / t) • x) + β * pNorm ((1 / u) • y) :=
          h_conv_pNorm.2 (by simp) (by simp) hα_nonneg hβ_nonneg hαβ
    -- Raising the norm inequality to the `p`th power and using convexity of `x ↦ x^p`
    -- yields the Jensen step for the perspective.
    have h_pow_combo :
        (pNorm ((1 / s) • (a • x + b • y))) ^ p ≤
          α * (pNorm ((1 / t) • x)) ^ p + β * (pNorm ((1 / u) • y)) ^ p := by
      have h_bound :
          (pNorm ((1 / s) • (a • x + b • y))) ^ p ≤
            (α * pNorm ((1 / t) • x) + β * pNorm ((1 / u) • y)) ^ p :=
        Real.rpow_le_rpow (h_pNorm_nonneg _) h_norm_combo (by linarith)
      refine h_bound.trans ?_
      exact (convexOn_rpow hp.le).2
        (by simpa using h_pNorm_nonneg ((1 / t) • x))
        (by simpa using h_pNorm_nonneg ((1 / u) • y))
        hα_nonneg hβ_nonneg hαβ
    calc
      pNormPow (a • x + b • y) / Real.rpow (a * t + b * u) (p - 1)
          = s * (pNorm ((1 / s) • (a • x + b • y))) ^ p := by
            simpa [s] using h_perspective (a • x + b • y) hs_pos
      _ ≤ s * (α * (pNorm ((1 / t) • x)) ^ p + β * (pNorm ((1 / u) • y)) ^ p) := by
            exact mul_le_mul_of_nonneg_left h_pow_combo hs_pos.le
      _ = (s * α) * (pNorm ((1 / t) • x)) ^ p + (s * β) * (pNorm ((1 / u) • y)) ^ p := by ring
      _ = a * (t * (pNorm ((1 / t) • x)) ^ p) + b * (u * (pNorm ((1 / u) • y)) ^ p) := by
            rw [hsα, hsβ]
            ring
      _ = a * (pNormPow x / Real.rpow t (p - 1)) + b * (pNormPow y / Real.rpow u (p - 1)) := by
            rw [← h_perspective x ht_pos, ← h_perspective y hu_pos]

end «problem-115»
