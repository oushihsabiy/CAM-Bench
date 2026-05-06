import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-113»
/-
Let p > 1 and q satisfy 1/p + 1/q = 1. Define ‖x‖_p = (∑_{i = 1}^n |xᵢ|^p)^(1/p), and define f(x, t)
=
−(t^p−‖x‖_p^p)^(1/p) on dom(f) = {(x, t)∈ℝ^n×ℝ: t ≥ ‖x‖_p}. Prove that f is convex on dom(f).
-/
open scoped BigOperators
theorem minkowski_gauge_neg_root_convexOn
    {n : ℕ} {p q : ℝ}
    (hp : 1 < p) (hq : 1 / p + 1 / q = 1) :
    let pNormPow : (Fin n → ℝ) → ℝ :=
      fun x => ∑ i : Fin n, Real.rpow (|x i|) p
    let pNorm : (Fin n → ℝ) → ℝ :=
      fun x => Real.rpow (pNormPow x) (1 / p)
    let dom : Set ((Fin n → ℝ) × ℝ) :=
      {xt | xt.2 ≥ pNorm xt.1}
    let f : ((Fin n → ℝ) × ℝ) → ℝ :=
      fun xt => -Real.rpow (Real.rpow xt.2 p - pNormPow xt.1) (1 / p)
    ConvexOn ℝ dom f := by
  dsimp
  let dom : Set ((Fin n → ℝ) × ℝ) :=
    {xt | (∑ i : Fin n, Real.rpow (|xt.1 i|) p) ^ (1 / p) ≤ xt.2}
  let g : ((Fin n → ℝ) × ℝ) → ℝ :=
    fun xt => Real.rpow (xt.2 ^ p - ∑ i : Fin n, Real.rpow (|xt.1 i|) p) (1 / p)
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  -- The `p`-power sums are always nonnegative, so every later `rpow` root has a legal radicand.
  have sum_rpow_abs_nonneg : ∀ x : Fin n → ℝ, 0 ≤ ∑ i : Fin n, Real.rpow (|x i|) p := by
    intro x
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (x i)) _
  -- Positive homogeneity of the finite `L^p` seminorm is the normalization used in both Minkowski steps.
  have weighted_Lp_eq :
      ∀ {ι : Type} [Fintype ι] (a : ℝ) (z : ι → ℝ), 0 ≤ a →
        (∑ i : ι, Real.rpow (|a * z i|) p) ^ (1 / p) =
          a * (∑ i : ι, Real.rpow (|z i|) p) ^ (1 / p) := by
    intro ι _ a z ha
    have hsum_nonneg : 0 ≤ ∑ i : ι, Real.rpow (|z i|) p := by
      exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (z i)) _
    calc
      (∑ i : ι, Real.rpow (|a * z i|) p) ^ (1 / p)
          = (∑ i : ι, Real.rpow (a * |z i|) p) ^ (1 / p) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [abs_mul, abs_of_nonneg ha]
      _ = (∑ i : ι, a ^ p * Real.rpow (|z i|) p) ^ (1 / p) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using (Real.mul_rpow ha (abs_nonneg (z i)) (z := p))
      _ = (a ^ p * ∑ i : ι, Real.rpow (|z i|) p) ^ (1 / p) := by
            congr 1
            symm
            exact Finset.mul_sum (s := Finset.univ) (f := fun i : ι => Real.rpow (|z i|) p) (a := a ^ p)
      _ = (a ^ p) ^ (1 / p) * (∑ i : ι, Real.rpow (|z i|) p) ^ (1 / p) := by
            rw [Real.mul_rpow (Real.rpow_nonneg ha _) hsum_nonneg]
      _ = a * (∑ i : ι, Real.rpow (|z i|) p) ^ (1 / p) := by
            rw [one_div, Real.rpow_rpow_inv ha hp_ne]
  -- Membership in the cone implies the second coordinate is nonnegative.
  have snd_nonneg : ∀ {xt : (Fin n → ℝ) × ℝ}, xt ∈ dom → 0 ≤ xt.2 := by
    intro xt hxt
    exact (Real.rpow_nonneg (sum_rpow_abs_nonneg xt.1) _).trans hxt
  -- The cone inequality also forces the root radicand to be nonnegative.
  have radicand_nonneg :
      ∀ {xt : (Fin n → ℝ) × ℝ}, xt ∈ dom →
        0 ≤ xt.2 ^ p - ∑ i : Fin n, Real.rpow (|xt.1 i|) p := by
    intro xt hxt
    have hroot_nonneg : 0 ≤ (∑ i : Fin n, Real.rpow (|xt.1 i|) p) ^ (1 / p) :=
      Real.rpow_nonneg (sum_rpow_abs_nonneg xt.1) _
    have hpow :
        ((∑ i : Fin n, Real.rpow (|xt.1 i|) p) ^ (1 / p)) ^ p ≤ xt.2 ^ p := by
      exact (Real.rpow_le_rpow_iff hroot_nonneg (snd_nonneg hxt) hp_pos).2 hxt
    rw [one_div, Real.rpow_inv_rpow (sum_rpow_abs_nonneg xt.1) hp_ne] at hpow
    exact sub_nonneg.mpr hpow
  -- Once the radicand is nonnegative, the auxiliary root itself is nonnegative and can be powered back.
  have g_nonneg : ∀ {xt : (Fin n → ℝ) × ℝ}, xt ∈ dom → 0 ≤ g xt := by
    intro xt hxt
    dsimp [g]
    exact Real.rpow_nonneg (radicand_nonneg hxt) _
  have g_rpow :
      ∀ {xt : (Fin n → ℝ) × ℝ}, xt ∈ dom →
        g xt ^ p = xt.2 ^ p - ∑ i : Fin n, Real.rpow (|xt.1 i|) p := by
    intro xt hxt
    simpa [g, one_div] using
      (Real.rpow_inv_rpow (radicand_nonneg hxt) hp_ne :
        ((xt.2 ^ p - ∑ i : Fin n, Real.rpow (|xt.1 i|) p) ^ p⁻¹) ^ p =
          xt.2 ^ p - ∑ i : Fin n, Real.rpow (|xt.1 i|) p)
  -- The cone itself is convex because Minkowski controls the mixed `L^p` norm.
  have dom_convex : Convex ℝ dom := by
    intro xt hxt yt hyt a b ha hb hab
    have hminkowski :
        (∑ i : Fin n, Real.rpow (|a * xt.1 i + b * yt.1 i|) p) ^ (1 / p) ≤
          (∑ i : Fin n, Real.rpow (|a * xt.1 i|) p) ^ (1 / p) +
            (∑ i : Fin n, Real.rpow (|b * yt.1 i|) p) ^ (1 / p) :=
      Real.Lp_add_le (s := Finset.univ) (f := fun i : Fin n => a * xt.1 i)
        (g := fun i : Fin n => b * yt.1 i) (p := p) hp.le
    have hbound :
        (∑ i : Fin n, Real.rpow (|a * xt.1 i + b * yt.1 i|) p) ^ (1 / p) ≤
          a * xt.2 + b * yt.2 := by
      have hscaled :
          (∑ i : Fin n, Real.rpow (|a * xt.1 i|) p) ^ (1 / p) +
              (∑ i : Fin n, Real.rpow (|b * yt.1 i|) p) ^ (1 / p) =
            a * (∑ i : Fin n, Real.rpow (|xt.1 i|) p) ^ (1 / p) +
              b * (∑ i : Fin n, Real.rpow (|yt.1 i|) p) ^ (1 / p) := by
        simpa using congrArg₂ (fun x y => x + y) (weighted_Lp_eq (ι := Fin n) a xt.1 ha)
          (weighted_Lp_eq (ι := Fin n) b yt.1 hb)
      calc
        (∑ i : Fin n, Real.rpow (|a * xt.1 i + b * yt.1 i|) p) ^ (1 / p)
            ≤ (∑ i : Fin n, Real.rpow (|a * xt.1 i|) p) ^ (1 / p) +
                (∑ i : Fin n, Real.rpow (|b * yt.1 i|) p) ^ (1 / p) := hminkowski
        _ = a * (∑ i : Fin n, Real.rpow (|xt.1 i|) p) ^ (1 / p) +
              b * (∑ i : Fin n, Real.rpow (|yt.1 i|) p) ^ (1 / p) := hscaled
        _ ≤ a * xt.2 + b * yt.2 := by
              exact add_le_add (mul_le_mul_of_nonneg_left hxt ha)
                (mul_le_mul_of_nonneg_left hyt hb)
    simpa [dom, smul_eq_mul, Prod.smul_mk, Pi.smul_apply, add_comm, add_left_comm, add_assoc,
      mul_add, add_mul] using hbound
  -- The `n+1` dimensional Minkowski inequality is the core Jensen step for the positive root.
  have extra_coordinate_minkowski :
      ∀ {xt yt : (Fin n → ℝ) × ℝ} {a b : ℝ},
        xt ∈ dom → yt ∈ dom → 0 ≤ a → 0 ≤ b → a + b = 1 →
        ((∑ i : Fin n, Real.rpow (|a * xt.1 i + b * yt.1 i|) p) +
            (a * g xt + b * g yt) ^ p) ^ (1 / p) ≤
          a * xt.2 + b * yt.2 := by
    intro xt yt a b hxt hyt ha hb hab
    have haux_nonneg : 0 ≤ a * g xt + b * g yt := by
      exact add_nonneg (mul_nonneg ha (g_nonneg hxt)) (mul_nonneg hb (g_nonneg hyt))
    have hminkowski :
        (∑ z : Fin n ⊕ Unit,
            Real.rpow
              (|a * Sum.elim xt.1 (fun _ : Unit => g xt) z +
                  b * Sum.elim yt.1 (fun _ : Unit => g yt) z|) p) ^ (1 / p) ≤
          (∑ z : Fin n ⊕ Unit,
              Real.rpow (|a * Sum.elim xt.1 (fun _ : Unit => g xt) z|) p) ^ (1 / p) +
            (∑ z : Fin n ⊕ Unit,
              Real.rpow (|b * Sum.elim yt.1 (fun _ : Unit => g yt) z|) p) ^ (1 / p) :=
      Real.Lp_add_le (s := Finset.univ)
        (f := fun z : Fin n ⊕ Unit => a * Sum.elim xt.1 (fun _ : Unit => g xt) z)
        (g := fun z : Fin n ⊕ Unit => b * Sum.elim yt.1 (fun _ : Unit => g yt) z)
        (p := p) hp.le
    have hxt_norm :
        (∑ z : Fin n ⊕ Unit,
            Real.rpow (|Sum.elim xt.1 (fun _ : Unit => g xt) z|) p) ^ (1 / p) = xt.2 := by
      calc
        (∑ z : Fin n ⊕ Unit,
            Real.rpow (|Sum.elim xt.1 (fun _ : Unit => g xt) z|) p) ^ (1 / p)
            = ((∑ i : Fin n, Real.rpow (|xt.1 i|) p) + g xt ^ p) ^ (1 / p) := by
                simp [Fintype.sum_sum_type, abs_of_nonneg (g_nonneg hxt)]
        _ = (xt.2 ^ p) ^ (1 / p) := by
              rw [g_rpow hxt]
              congr 1
              ring
        _ = xt.2 := by
              rw [one_div, Real.rpow_rpow_inv (snd_nonneg hxt) hp_ne]
    have hyt_norm :
        (∑ z : Fin n ⊕ Unit,
            Real.rpow (|Sum.elim yt.1 (fun _ : Unit => g yt) z|) p) ^ (1 / p) = yt.2 := by
      calc
        (∑ z : Fin n ⊕ Unit,
            Real.rpow (|Sum.elim yt.1 (fun _ : Unit => g yt) z|) p) ^ (1 / p)
            = ((∑ i : Fin n, Real.rpow (|yt.1 i|) p) + g yt ^ p) ^ (1 / p) := by
                simp [Fintype.sum_sum_type, abs_of_nonneg (g_nonneg hyt)]
        _ = (yt.2 ^ p) ^ (1 / p) := by
              rw [g_rpow hyt]
              congr 1
              ring
        _ = yt.2 := by
              rw [one_div, Real.rpow_rpow_inv (snd_nonneg hyt) hp_ne]
    calc
      ((∑ i : Fin n, Real.rpow (|a * xt.1 i + b * yt.1 i|) p) +
          (a * g xt + b * g yt) ^ p) ^ (1 / p)
          = (∑ z : Fin n ⊕ Unit,
              Real.rpow
                (|a * Sum.elim xt.1 (fun _ : Unit => g xt) z +
                    b * Sum.elim yt.1 (fun _ : Unit => g yt) z|) p) ^ (1 / p) := by
              simp [Fintype.sum_sum_type, abs_of_nonneg haux_nonneg]
      _ ≤ (∑ z : Fin n ⊕ Unit,
            Real.rpow (|a * Sum.elim xt.1 (fun _ : Unit => g xt) z|) p) ^ (1 / p) +
          (∑ z : Fin n ⊕ Unit,
            Real.rpow (|b * Sum.elim yt.1 (fun _ : Unit => g yt) z|) p) ^ (1 / p) := hminkowski
      _ = a * xt.2 + b * yt.2 := by
            have hscaled :
                (∑ z : Fin n ⊕ Unit,
                    Real.rpow (|a * Sum.elim xt.1 (fun _ : Unit => g xt) z|) p) ^ (1 / p) +
                    (∑ z : Fin n ⊕ Unit,
                      Real.rpow (|b * Sum.elim yt.1 (fun _ : Unit => g yt) z|) p) ^ (1 / p) =
                  a * (∑ z : Fin n ⊕ Unit,
                    Real.rpow (|Sum.elim xt.1 (fun _ : Unit => g xt) z|) p) ^ (1 / p) +
                    b * (∑ z : Fin n ⊕ Unit,
                      Real.rpow (|Sum.elim yt.1 (fun _ : Unit => g yt) z|) p) ^ (1 / p) := by
              simpa using congrArg₂ (fun x y => x + y)
                (weighted_Lp_eq (ι := Fin n ⊕ Unit) a
                  (fun z : Fin n ⊕ Unit => Sum.elim xt.1 (fun _ : Unit => g xt) z) ha)
                (weighted_Lp_eq (ι := Fin n ⊕ Unit) b
                  (fun z : Fin n ⊕ Unit => Sum.elim yt.1 (fun _ : Unit => g yt) z) hb)
            rw [hscaled, hxt_norm, hyt_norm]
  -- Turning the extended Minkowski bound back into a root inequality isolates the Jensen conclusion.
  have le_root_of_add_rpow_le :
      ∀ {A T w : ℝ}, 0 ≤ A → 0 ≤ T → 0 ≤ w →
        (A + w ^ p) ^ (1 / p) ≤ T → w ≤ Real.rpow (T ^ p - A) (1 / p) := by
    intro A T w hA hT hw hroot
    have hsum_nonneg : 0 ≤ A + w ^ p := add_nonneg hA (Real.rpow_nonneg hw _)
    have hpow : A + w ^ p ≤ T ^ p := by
      have hpow' := (Real.rpow_le_rpow_iff (Real.rpow_nonneg hsum_nonneg _) hT hp_pos).2 hroot
      simpa [one_div, Real.rpow_inv_rpow hsum_nonneg hp_ne] using hpow'
    have hsub : w ^ p ≤ T ^ p - A := by
      linarith
    have hsub_nonneg : 0 ≤ T ^ p - A := by
      exact le_trans (Real.rpow_nonneg hw _) hsub
    have hroot' :
        (w ^ p) ^ (1 / p) ≤ Real.rpow (T ^ p - A) (1 / p) := by
      exact Real.rpow_le_rpow (Real.rpow_nonneg hw _) hsub (one_div_nonneg.2 hp_nonneg)
    simpa [one_div, Real.rpow_rpow_inv hw hp_ne] using hroot'
  -- Jensen for the positive root now follows directly from the previous two lemmas.
  have g_concave : ConcaveOn ℝ dom g := by
    refine ⟨dom_convex, ?_⟩
    intro xt hxt yt hyt a b ha hb hab
    have hmix := extra_coordinate_minkowski hxt hyt ha hb hab
    have hA_nonneg :
        0 ≤ ∑ i : Fin n, Real.rpow (|a * xt.1 i + b * yt.1 i|) p := by
      exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
    have hw_nonneg : 0 ≤ a * g xt + b * g yt := by
      exact add_nonneg (mul_nonneg ha (g_nonneg hxt)) (mul_nonneg hb (g_nonneg hyt))
    have hT_nonneg : 0 ≤ a * xt.2 + b * yt.2 := by
      exact add_nonneg (mul_nonneg ha (snd_nonneg hxt)) (mul_nonneg hb (snd_nonneg hyt))
    have hroot :=
      le_root_of_add_rpow_le hA_nonneg hT_nonneg hw_nonneg hmix
    simpa [g, smul_eq_mul, Prod.smul_mk, Pi.smul_apply, add_comm, add_left_comm, add_assoc,
      mul_add, add_mul] using hroot
  -- Negating a concave function turns it into the required convex function.
  have hneg : ConcaveOn ℝ dom (fun xt => -(-g xt)) := by
    simpa using g_concave
  have hconv : ConvexOn ℝ dom (fun xt => -g xt) := by
    exact (neg_concaveOn_iff (𝕜 := ℝ) (s := dom) (f := fun xt => -g xt)).1 hneg
  simpa [dom, g] using hconv

end «problem-113»
