import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-105»
/-
Let p < 1 with p ≠ 0, and define f(x) = (∑_{i = 1}^n xᵢ^p)^(1/p) on ℝ_{+ +}^n. Prove that f is
concave on ℝ_{+ +}^n.
-/
theorem power_sum_root_concave_on_positive_orthant
    {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp_ne : p ≠ 0) (hp_lt : p < 1) :
    ConcaveOn ℝ
      {x : Fin n → ℝ | ∀ i, 0 < x i}
      (fun x => Real.rpow (∑ i : Fin n, Real.rpow (x i) p) (1 / p)) := by
  let F : (Fin n → ℝ) → ℝ := fun x => Real.rpow (∑ i : Fin n, Real.rpow (x i) p) (1 / p)
  -- Positive vectors have a strictly positive `p`-power sum because `Fin n` is nonempty.
  have hsum_pos : ∀ {x : Fin n → ℝ}, (∀ i, 0 < x i) → 0 < ∑ i : Fin n, Real.rpow (x i) p := by
    intro x hx
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hx i) p) Finset.univ_nonempty
  -- The power-sum root itself stays strictly positive on the positive orthant.
  have hF_pos : ∀ {x : Fin n → ℝ}, (∀ i, 0 < x i) → 0 < F x := by
    intro x hx
    dsimp [F]
    exact Real.rpow_pos_of_pos (hsum_pos hx) _
  -- Positive homogeneity lets us normalize vectors before applying scalar convexity/concavity.
  have hhom :
      ∀ {c : ℝ} {x : Fin n → ℝ}, 0 < c → (∀ i, 0 < x i) → F (c • x) = c * F x := by
    intro c x hc hx
    have hsum :
        ∑ i : Fin n, Real.rpow ((c • x) i) p = Real.rpow c p * ∑ i : Fin n, Real.rpow (x i) p := by
      calc
        ∑ i : Fin n, Real.rpow ((c • x) i) p = ∑ i : Fin n, Real.rpow c p * Real.rpow (x i) p := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [Pi.smul_apply, Real.mul_rpow (le_of_lt hc) (le_of_lt (hx i))]
        _ = Real.rpow c p * ∑ i : Fin n, Real.rpow (x i) p := by
          rw [Finset.mul_sum]
    have hcpow : Real.rpow (Real.rpow c p) (1 / p) = c := by
      simpa [one_div] using (Real.rpow_rpow_inv (le_of_lt hc) hp_ne)
    calc
      F (c • x)
          = Real.rpow (Real.rpow c p * ∑ i : Fin n, Real.rpow (x i) p) (1 / p) := by
              simpa [F] using congrArg (fun t => Real.rpow t (1 / p)) hsum
      _ = Real.rpow (Real.rpow c p) (1 / p) * Real.rpow (∑ i : Fin n, Real.rpow (x i) p) (1 / p) := by
              simpa using
                (Real.mul_rpow (Real.rpow_nonneg (le_of_lt hc) p)
                  (Finset.sum_nonneg fun i _ => (Real.rpow_pos_of_pos (hx i) p).le) (z := 1 / p))
      _ = c * Real.rpow (∑ i : Fin n, Real.rpow (x i) p) (1 / p) := by rw [hcpow]
      _ = c * F x := by rfl
  -- Superadditivity comes from normalizing to a convex combination and then using scalar
  -- concavity for `0 < p < 1` or scalar convexity for `p < 0`.
  have hsuper :
      ∀ {x y : Fin n → ℝ}, (∀ i, 0 < x i) → (∀ i, 0 < y i) → F x + F y ≤ F (x + y) := by
    intro x y hx hy
    let A : ℝ := F x
    let B : ℝ := F y
    let u : Fin n → ℝ := fun i => x i / A
    let v : Fin n → ℝ := fun i => y i / B
    let a : ℝ := A / (A + B)
    let b : ℝ := B / (A + B)
    let z : Fin n → ℝ := fun i => a * u i + b * v i
    have hA_pos : 0 < A := hF_pos hx
    have hB_pos : 0 < B := hF_pos hy
    have hAB_pos : 0 < A + B := add_pos hA_pos hB_pos
    have ha_pos : 0 < a := by
      dsimp [a]
      exact div_pos hA_pos hAB_pos
    have hb_pos : 0 < b := by
      dsimp [b]
      exact div_pos hB_pos hAB_pos
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp [hAB_pos.ne']
    have hu_pos : ∀ i, 0 < u i := by
      intro i
      dsimp [u]
      exact div_pos (hx i) hA_pos
    have hv_pos : ∀ i, 0 < v i := by
      intro i
      dsimp [v]
      exact div_pos (hy i) hB_pos
    have hz_pos : ∀ i, 0 < z i := by
      intro i
      dsimp [z]
      exact add_pos (mul_pos ha_pos (hu_pos i)) (mul_pos hb_pos (hv_pos i))
    -- The normalization rescales `x` and `y` so that their `F`-mass becomes exactly `1`.
    have huF : F u = 1 := by
      calc
        F u = F ((A⁻¹) • x) := by
          congr 1
          ext i
          simp [u, Pi.smul_apply, div_eq_mul_inv, mul_comm]
        _ = A⁻¹ * F x := hhom (inv_pos.mpr hA_pos) hx
        _ = 1 := by
          dsimp [A]
          exact inv_mul_cancel₀ hA_pos.ne'
    have hvF : F v = 1 := by
      calc
        F v = F ((B⁻¹) • y) := by
          congr 1
          ext i
          simp [v, Pi.smul_apply, div_eq_mul_inv, mul_comm]
        _ = B⁻¹ * F y := hhom (inv_pos.mpr hB_pos) hy
        _ = 1 := by
          dsimp [B]
          exact inv_mul_cancel₀ hB_pos.ne'
    have hu_sum_nonneg : 0 ≤ ∑ i : Fin n, Real.rpow (u i) p := by
      exact Finset.sum_nonneg fun i _ => (Real.rpow_pos_of_pos (hu_pos i) p).le
    have hv_sum_nonneg : 0 ≤ ∑ i : Fin n, Real.rpow (v i) p := by
      exact Finset.sum_nonneg fun i _ => (Real.rpow_pos_of_pos (hv_pos i) p).le
    have hu_sum : ∑ i : Fin n, Real.rpow (u i) p = 1 := by
      have h : (Real.rpow (∑ i : Fin n, Real.rpow (u i) p) (1 / p)) ^ p = 1 := by
        simpa [F] using congrArg (fun t => Real.rpow t p) huF
      have hpow : (Real.rpow (∑ i : Fin n, Real.rpow (u i) p) (1 / p)) ^ p =
          ∑ i : Fin n, Real.rpow (u i) p := by
        calc
          (Real.rpow (∑ i : Fin n, Real.rpow (u i) p) (1 / p)) ^ p
              = Real.rpow (∑ i : Fin n, Real.rpow (u i) p) ((1 / p) * p) := by
                  simpa using (Real.rpow_mul hu_sum_nonneg (1 / p) p).symm
          _ = ∑ i : Fin n, Real.rpow (u i) p := by
                have hmul : (1 / p) * p = 1 := by field_simp [hp_ne]
                rw [hmul]
                simp
      exact hpow ▸ h
    have hv_sum : ∑ i : Fin n, Real.rpow (v i) p = 1 := by
      have h : (Real.rpow (∑ i : Fin n, Real.rpow (v i) p) (1 / p)) ^ p = 1 := by
        simpa [F] using congrArg (fun t => Real.rpow t p) hvF
      have hpow : (Real.rpow (∑ i : Fin n, Real.rpow (v i) p) (1 / p)) ^ p =
          ∑ i : Fin n, Real.rpow (v i) p := by
        calc
          (Real.rpow (∑ i : Fin n, Real.rpow (v i) p) (1 / p)) ^ p
              = Real.rpow (∑ i : Fin n, Real.rpow (v i) p) ((1 / p) * p) := by
                  simpa using (Real.rpow_mul hv_sum_nonneg (1 / p) p).symm
          _ = ∑ i : Fin n, Real.rpow (v i) p := by
                have hmul : (1 / p) * p = 1 := by field_simp [hp_ne]
                rw [hmul]
                simp
      exact hpow ▸ h
    have hdecomp : x + y = (A + B) • z := by
      ext i
      dsimp [z, a, b, u, v]
      field_simp [hA_pos.ne', hB_pos.ne', hAB_pos.ne']
    rcases lt_or_gt_of_ne hp_ne with hp_neg | hp_pos
    · -- For negative exponents, convexity of `t ↦ t^p` on `(0, ∞)` gives the normalized estimate.
      have hconvex_rpow_neg : ConvexOn ℝ (Set.Ioi 0) (fun t : ℝ => Real.rpow t p) := by
        refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Ioi 0)
          (f' := fun x => p * x ^ (p - 1))
          (f'' := fun x => p * ((p - 1) * x ^ (p + (-1 + -1))))
          (convex_Ioi 0) ?_ ?_ ?_ ?_
        · intro t ht
          exact (Real.continuousAt_rpow_const t p (Or.inl (ne_of_gt ht))).continuousWithinAt
        · intro t ht
          exact (Real.hasDerivAt_rpow_const (x := t) (p := p)
            (Or.inl (ne_of_gt (by simpa using ht)))).hasDerivWithinAt
        · intro t ht
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
            mul_comm] using
            (HasDerivAt.const_mul p
              (Real.hasDerivAt_rpow_const (x := t) (p := p - 1)
                (Or.inl (ne_of_gt (by simpa using ht))))).hasDerivWithinAt
        · intro t ht
          have ht_pos : 0 < t := by simpa using ht
          have hcoef : 0 < p * (p - 1) := by nlinarith
          have hpow : 0 < t ^ (p + (-1 + -1)) := Real.rpow_pos_of_pos ht_pos _
          nlinarith [mul_pos hcoef hpow]
      have hconvex := (convexOn_iff_forall_pos.mp hconvex_rpow_neg).2
      have hz_sum_le : ∑ i : Fin n, Real.rpow (z i) p ≤ 1 := by
        calc
          ∑ i : Fin n, Real.rpow (z i) p
              ≤ ∑ i : Fin n, (a * Real.rpow (u i) p + b * Real.rpow (v i) p) := by
                refine Finset.sum_le_sum ?_
                intro i hi
                simpa [z, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc, mul_comm,
                  mul_left_comm, mul_assoc] using
                  hconvex (show u i ∈ Set.Ioi (0 : ℝ) by simpa using hu_pos i)
                    (show v i ∈ Set.Ioi (0 : ℝ) by simpa using hv_pos i)
                    ha_pos hb_pos hab
          _ = 1 := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hu_sum, hv_sum]
                linarith
      have hz_sum_pos : 0 < ∑ i : Fin n, Real.rpow (z i) p := hsum_pos hz_pos
      have hFz_ge_one : 1 ≤ F z := by
        dsimp [F]
        have hpinv_nonpos : 1 / p ≤ 0 := one_div_nonpos.mpr hp_neg.le
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz_sum_pos hz_sum_le hpinv_nonpos
      calc
        F x + F y = A + B := by rfl
        _ ≤ (A + B) * F z := by
          simpa [one_mul] using mul_le_mul_of_nonneg_left hFz_ge_one hAB_pos.le
        _ = F ((A + B) • z) := by
          symm
          exact hhom hAB_pos hz_pos
        _ = F (x + y) := by rw [hdecomp]
    · -- For positive exponents below `1`, scalar concavity gives the normalized estimate.
      have hconcave := (concaveOn_iff_forall_pos.mp (Real.concaveOn_rpow hp_pos.le hp_lt.le)).2
      have hz_sum_ge : 1 ≤ ∑ i : Fin n, Real.rpow (z i) p := by
        calc
          1 = ∑ i : Fin n, (a * Real.rpow (u i) p + b * Real.rpow (v i) p) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hu_sum, hv_sum]
                linarith
          _ ≤ ∑ i : Fin n, Real.rpow (z i) p := by
                refine Finset.sum_le_sum ?_
                intro i hi
                simpa [z, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc, mul_comm,
                  mul_left_comm, mul_assoc] using
                  hconcave (show u i ∈ Set.Ici (0 : ℝ) by exact (hu_pos i).le)
                    (show v i ∈ Set.Ici (0 : ℝ) by exact (hv_pos i).le)
                    ha_pos hb_pos hab
      have hFz_ge_one : 1 ≤ F z := by
        dsimp [F]
        have hpinv_nonneg : 0 ≤ 1 / p := one_div_nonneg.mpr hp_pos.le
        exact Real.one_le_rpow hz_sum_ge hpinv_nonneg
      calc
        F x + F y = A + B := by rfl
        _ ≤ (A + B) * F z := by
          simpa [one_mul] using mul_le_mul_of_nonneg_left hFz_ge_one hAB_pos.le
        _ = F ((A + B) • z) := by
          symm
          exact hhom hAB_pos hz_pos
        _ = F (x + y) := by rw [hdecomp]
  rw [concaveOn_iff_forall_pos]
  constructor
  · -- Strict convex combinations preserve positivity of every coordinate.
    rw [convex_iff_forall_pos]
    intro x hx y hy a b ha hb hab i
    simpa [Pi.smul_apply] using add_pos (mul_pos ha (hx i)) (mul_pos hb (hy i))
  · intro x hx y hy a b ha hb hab
    have hax : ∀ i, 0 < (a • x) i := by
      intro i
      simpa [Pi.smul_apply] using mul_pos ha (hx i)
    have hby : ∀ i, 0 < (b • y) i := by
      intro i
      simpa [Pi.smul_apply] using mul_pos hb (hy i)
    -- Apply superadditivity to the positively rescaled vectors `a • x` and `b • y`.
    change a * F x + b * F y ≤ F (a • x + b • y)
    calc
      a * F x + b * F y = F (a • x) + F (b • y) := by
        rw [← hhom ha hx, ← hhom hb hy]
      _ ≤ F (a • x + b • y) := hsuper hax hby

end «problem-105»
