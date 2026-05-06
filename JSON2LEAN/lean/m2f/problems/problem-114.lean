import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-114»
/-
Let p > 1 and define ‖x‖_p as usual. Define f(x, t) = −log(t^p−‖x‖_p^p) on dom(f) = {(x, t)∈ℝ^n×ℝ: t
> ‖x‖_p}. Prove that f is convex on dom(f).
-/
open scoped BigOperators

theorem lp_log_barrier_convexOn
    {n : ℕ} {p : ℝ} (hp : 1 < p) :
    let pNormPow : (Fin n → ℝ) → ℝ := fun x => ∑ i : Fin n, Real.rpow (|x i|) p
    let pNorm : (Fin n → ℝ) → ℝ := fun x => Real.rpow (pNormPow x) (1 / p)
    ConvexOn ℝ
      {xt : (Fin n → ℝ) × ℝ | pNorm xt.1 < xt.2}
      (fun xt : (Fin n → ℝ) × ℝ =>
        -Real.log (Real.rpow xt.2 p - pNormPow xt.1)) := by
  dsimp
  let S : Set ((Fin n → ℝ) × ℝ) :=
    {xt | Real.rpow (∑ i : Fin n, Real.rpow (|xt.1 i|) p) (1 / p) < xt.2}
  let slack : ((Fin n → ℝ) × ℝ) → ℝ :=
    fun xt => Real.rpow xt.2 p - ∑ i : Fin n, Real.rpow (|xt.1 i|) p
  let δ : ((Fin n → ℝ) × ℝ) → ℝ :=
    fun xt => Real.rpow (slack xt) (1 / p)
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_le : 1 ≤ p := le_of_lt hp
  have hp_ne : p ≠ 0 := by linarith
  -- The domain inequality immediately forces the final coordinate to be positive.
  have ht_pos : ∀ {xt : (Fin n → ℝ) × ℝ}, xt ∈ S → 0 < xt.2 := by
    intro xt hxt
    have hnorm_nonneg : 0 ≤ Real.rpow (∑ i : Fin n, Real.rpow (|xt.1 i|) p) (1 / p) := by
      refine Real.rpow_nonneg ?_ (1 / p)
      refine Finset.sum_nonneg ?_
      intro i hi
      exact Real.rpow_nonneg (abs_nonneg (xt.1 i)) p
    exact lt_of_le_of_lt hnorm_nonneg hxt
  -- Rewriting the domain condition as positivity of the `p`-slack is the key algebraic bridge.
  have hslack_pos : ∀ {xt : (Fin n → ℝ) × ℝ}, xt ∈ S → 0 < slack xt := by
    intro xt hxt
    have hsum_nonneg : 0 ≤ ∑ i : Fin n, Real.rpow (|xt.1 i|) p := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact Real.rpow_nonneg (abs_nonneg (xt.1 i)) p
    have ht : 0 < xt.2 := ht_pos hxt
    have hxt' : Real.rpow (∑ i : Fin n, Real.rpow (|xt.1 i|) p) p⁻¹ < xt.2 := by
      simpa [S, one_div] using hxt
    have hpow_lt : ∑ i : Fin n, Real.rpow (|xt.1 i|) p < Real.rpow xt.2 p := by
      exact (Real.rpow_inv_lt_iff_of_pos hsum_nonneg (le_of_lt ht) hp_pos).1 hxt'
    dsimp [slack]
    exact sub_pos.2 hpow_lt
  -- The slack root is positive on the domain, which is exactly what the later `log` step needs.
  have hδ_pos : ∀ {xt : (Fin n → ℝ) × ℝ}, xt ∈ S → 0 < δ xt := by
    intro xt hxt
    dsimp [δ]
    exact Real.rpow_pos_of_pos (hslack_pos hxt) (1 / p)
  -- Raising the slack root back to the `p`-th power recovers the original slack.
  have hδ_pow : ∀ {xt : (Fin n → ℝ) × ℝ}, xt ∈ S → Real.rpow (δ xt) p = slack xt := by
    intro xt hxt
    dsimp [δ]
    simpa [one_div] using
      (Real.rpow_inv_rpow (le_of_lt (hslack_pos hxt)) hp_ne :
        Real.rpow (Real.rpow (slack xt) p⁻¹) p = slack xt)
  -- Route correction: instead of duplicating Jensen-style algebra twice, first prove the stronger
  -- slack inequality `(a δx + b δy)^p ≤ slack (a x + b y)` via one augmented Minkowski argument.
  have hslack_bound :
      ∀ {xt ys : (Fin n → ℝ) × ℝ}, xt ∈ S → ys ∈ S →
        ∀ {a b : ℝ}, 0 < a → 0 < b → a + b = 1 →
          Real.rpow (a * δ xt + b * δ ys) p ≤ slack (a • xt + b • ys) := by
    intro xt ys hxt hys a b ha hb hab
    let uxt : Fin (n + 1) → ℝ := Fin.snoc (fun i : Fin n => |xt.1 i|) (δ xt)
    let uys : Fin (n + 1) → ℝ := Fin.snoc (fun i : Fin n => |ys.1 i|) (δ ys)
    have huxt_nonneg : ∀ i : Fin (n + 1), 0 ≤ uxt i := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [uxt] using (hδ_pos hxt).le
      · simp [uxt, abs_nonneg]
    have huys_nonneg : ∀ i : Fin (n + 1), 0 ≤ uys i := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [uys] using (hδ_pos hys).le
      · simp [uys, abs_nonneg]
    -- The augmented vectors have `L^p` norms exactly equal to the corresponding `t`-coordinates.
    have huxt_sum : ∑ i : Fin (n + 1), Real.rpow (uxt i) p = Real.rpow xt.2 p := by
      calc
        ∑ i : Fin (n + 1), Real.rpow (uxt i) p
            = (∑ i : Fin n, Real.rpow (|xt.1 i|) p) + Real.rpow (δ xt) p := by
                rw [Fin.sum_univ_castSucc]
                simp [uxt]
        _ = (∑ i : Fin n, Real.rpow (|xt.1 i|) p) + slack xt := by
              rw [hδ_pow hxt]
        _ = Real.rpow xt.2 p := by
              dsimp [slack]
              ring
    have huys_sum : ∑ i : Fin (n + 1), Real.rpow (uys i) p = Real.rpow ys.2 p := by
      calc
        ∑ i : Fin (n + 1), Real.rpow (uys i) p
            = (∑ i : Fin n, Real.rpow (|ys.1 i|) p) + Real.rpow (δ ys) p := by
                rw [Fin.sum_univ_castSucc]
                simp [uys]
        _ = (∑ i : Fin n, Real.rpow (|ys.1 i|) p) + slack ys := by
              rw [hδ_pow hys]
        _ = Real.rpow ys.2 p := by
              dsimp [slack]
              ring
    have hscaled_xt :
        Real.rpow (∑ i : Fin (n + 1), Real.rpow (a * uxt i) p) (1 / p) = a * xt.2 := by
      calc
        Real.rpow (∑ i : Fin (n + 1), Real.rpow (a * uxt i) p) (1 / p)
            = Real.rpow (Real.rpow a p * ∑ i : Fin (n + 1), Real.rpow (uxt i) p) (1 / p) := by
                congr 1
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro i hi
                simpa using (Real.mul_rpow ha.le (huxt_nonneg i) (z := p))
        _ =
            Real.rpow (Real.rpow a p) (1 / p) *
              Real.rpow (∑ i : Fin (n + 1), Real.rpow (uxt i) p) (1 / p) := by
                simpa using
                  (Real.mul_rpow (Real.rpow_nonneg ha.le p)
                    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (huxt_nonneg i) p)
                    (z := 1 / p))
        _ = a * xt.2 := by
              rw [show Real.rpow (Real.rpow a p) (1 / p) = a by
                    simpa [one_div] using
                      (Real.rpow_rpow_inv ha.le hp_ne :
                        Real.rpow (Real.rpow a p) p⁻¹ = a),
                huxt_sum,
                show Real.rpow (Real.rpow xt.2 p) (1 / p) = xt.2 by
                  simpa [one_div] using
                    (Real.rpow_rpow_inv (le_of_lt (ht_pos hxt)) hp_ne :
                      Real.rpow (Real.rpow xt.2 p) p⁻¹ = xt.2)]
    have hscaled_ys :
        Real.rpow (∑ i : Fin (n + 1), Real.rpow (b * uys i) p) (1 / p) = b * ys.2 := by
      calc
        Real.rpow (∑ i : Fin (n + 1), Real.rpow (b * uys i) p) (1 / p)
            = Real.rpow (Real.rpow b p * ∑ i : Fin (n + 1), Real.rpow (uys i) p) (1 / p) := by
                congr 1
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro i hi
                simpa using (Real.mul_rpow hb.le (huys_nonneg i) (z := p))
        _ =
            Real.rpow (Real.rpow b p) (1 / p) *
              Real.rpow (∑ i : Fin (n + 1), Real.rpow (uys i) p) (1 / p) := by
                simpa using
                  (Real.mul_rpow (Real.rpow_nonneg hb.le p)
                    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (huys_nonneg i) p)
                    (z := 1 / p))
        _ = b * ys.2 := by
              rw [show Real.rpow (Real.rpow b p) (1 / p) = b by
                    simpa [one_div] using
                      (Real.rpow_rpow_inv hb.le hp_ne :
                        Real.rpow (Real.rpow b p) p⁻¹ = b),
                huys_sum,
                show Real.rpow (Real.rpow ys.2 p) (1 / p) = ys.2 by
                  simpa [one_div] using
                    (Real.rpow_rpow_inv (le_of_lt (ht_pos hys)) hp_ne :
                      Real.rpow (Real.rpow ys.2 p) p⁻¹ = ys.2)]
    -- Minkowski on the augmented vectors converts the endpoint equalities into a bound for the
    -- combined slack coordinate.
    have hLp :=
      Real.Lp_add_le_of_nonneg (s := (Finset.univ : Finset (Fin (n + 1))))
        (f := fun i => a * uxt i) (g := fun i => b * uys i) hp_le
        (by
          intro i hi
          exact mul_nonneg ha.le (huxt_nonneg i))
        (by
          intro i hi
          exact mul_nonneg hb.le (huys_nonneg i))
    have hLp' :
        Real.rpow (∑ i : Fin (n + 1), Real.rpow (a * uxt i + b * uys i) p) (1 / p) ≤
          a * xt.2 + b * ys.2 := by
      calc
        Real.rpow (∑ i : Fin (n + 1), Real.rpow (a * uxt i + b * uys i) p) (1 / p)
            ≤ Real.rpow (∑ i : Fin (n + 1), Real.rpow (a * uxt i) p) (1 / p) +
                Real.rpow (∑ i : Fin (n + 1), Real.rpow (b * uys i) p) (1 / p) := by
                  simpa using hLp
        _ = a * xt.2 + b * ys.2 := by rw [hscaled_xt, hscaled_ys]
    have hsum_nonneg :
        0 ≤ ∑ i : Fin (n + 1), Real.rpow (a * uxt i + b * uys i) p := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact Real.rpow_nonneg
        (add_nonneg (mul_nonneg ha.le (huxt_nonneg i)) (mul_nonneg hb.le (huys_nonneg i))) p
    have hcombo_nonneg : 0 ≤ a * xt.2 + b * ys.2 := by
      exact add_nonneg (mul_nonneg ha.le (le_of_lt (ht_pos hxt)))
        (mul_nonneg hb.le (le_of_lt (ht_pos hys)))
    have hLpPow :
        (∑ i : Fin n, Real.rpow (a * |xt.1 i| + b * |ys.1 i|) p) +
            Real.rpow (a * δ xt + b * δ ys) p ≤
          Real.rpow (a * xt.2 + b * ys.2) p := by
      have hpow :
          ∑ i : Fin (n + 1), Real.rpow (a * uxt i + b * uys i) p ≤
            Real.rpow (a * xt.2 + b * ys.2) p := by
        exact (Real.rpow_inv_le_iff_of_pos hsum_nonneg hcombo_nonneg hp_pos).1
          (by simpa [one_div] using hLp')
      simpa [uxt, uys, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last] using hpow
    have hfirst_le :
        ∑ i : Fin n, Real.rpow (|(a • xt + b • ys).1 i|) p ≤
          ∑ i : Fin n, Real.rpow (a * |xt.1 i| + b * |ys.1 i|) p := by
      refine Finset.sum_le_sum ?_
      intro i hi
      change Real.rpow (|a * xt.1 i + b * ys.1 i|) p ≤
        Real.rpow (a * |xt.1 i| + b * |ys.1 i|) p
      have habs : |a * xt.1 i + b * ys.1 i| ≤ a * |xt.1 i| + b * |ys.1 i| := by
        calc
          |a * xt.1 i + b * ys.1 i| ≤ |a * xt.1 i| + |b * ys.1 i| := abs_add_le _ _
          _ = a * |xt.1 i| + b * |ys.1 i| := by
                rw [abs_mul, abs_mul, abs_of_nonneg ha.le, abs_of_nonneg hb.le]
      exact Real.rpow_le_rpow (abs_nonneg _) habs hp_pos.le
    have hcombo_pow :
        (∑ i : Fin n, Real.rpow (|(a • xt + b • ys).1 i|) p) +
            Real.rpow (a * δ xt + b * δ ys) p ≤
          Real.rpow ((a • xt + b • ys).2) p := by
      calc
        (∑ i : Fin n, Real.rpow (|(a • xt + b • ys).1 i|) p) + Real.rpow (a * δ xt + b * δ ys) p
            ≤ (∑ i : Fin n, Real.rpow (a * |xt.1 i| + b * |ys.1 i|) p) +
                Real.rpow (a * δ xt + b * δ ys) p := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right hfirst_le (Real.rpow (a * δ xt + b * δ ys) p)
        _ ≤ Real.rpow (a * xt.2 + b * ys.2) p := hLpPow
        _ = Real.rpow ((a • xt + b • ys).2) p := by
              simp [smul_eq_mul]
    have hsub :
        Real.rpow (a * δ xt + b * δ ys) p ≤
          Real.rpow ((a • xt + b • ys).2) p -
            ∑ i : Fin n, Real.rpow (|(a • xt + b • ys).1 i|) p := by
      linarith
    simpa [slack] using hsub
  -- Taking the `p`-th root of the previous inequality gives the actual concavity inequality.
  have hδ_concavity :
      ∀ {xt ys : (Fin n → ℝ) × ℝ}, xt ∈ S → ys ∈ S →
        ∀ {a b : ℝ}, 0 < a → 0 < b → a + b = 1 →
          a * δ xt + b * δ ys ≤ δ (a • xt + b • ys) := by
    intro xt ys hxt hys a b ha hb hab
    have hbound := hslack_bound hxt hys ha hb hab
    have hleft_nonneg : 0 ≤ a * δ xt + b * δ ys := by
      exact add_nonneg (mul_nonneg ha.le (le_of_lt (hδ_pos hxt)))
        (mul_nonneg hb.le (le_of_lt (hδ_pos hys)))
    have hslack_nonneg : 0 ≤ slack (a • xt + b • ys) := by
      exact le_trans (Real.rpow_nonneg hleft_nonneg p) hbound
    simpa [δ, one_div] using
      ((Real.le_rpow_inv_iff_of_pos hleft_nonneg hslack_nonneg hp_pos).2 hbound)
  -- Positivity of the bounded slack shows the domain is convex.
  have hSconvex : Convex ℝ S := by
    refine convex_iff_forall_pos.2 ?_
    intro xt hxt ys hys a b ha hb hab
    have hδxt_pos := hδ_pos hxt
    have hδys_pos := hδ_pos hys
    have hbound := hslack_bound hxt hys ha hb hab
    have hleft_pos : 0 < a * δ xt + b * δ ys := by positivity
    have hslack_combo_pos : 0 < slack (a • xt + b • ys) := by
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos hleft_pos p) hbound
    have hcombo_t_pos : 0 < (a • xt + b • ys).2 := by
      simpa [smul_eq_mul] using
        add_pos (mul_pos ha (ht_pos hxt)) (mul_pos hb (ht_pos hys))
    have hcombo_sum_nonneg :
        0 ≤ ∑ i : Fin n, Real.rpow (|(a • xt + b • ys).1 i|) p := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact Real.rpow_nonneg (abs_nonneg ((a • xt + b • ys).1 i)) p
    have hcombo_sum_lt :
        ∑ i : Fin n, Real.rpow (|(a • xt + b • ys).1 i|) p <
          Real.rpow ((a • xt + b • ys).2) p := by
      have hslack_combo_pos' :
          0 < Real.rpow ((a • xt + b • ys).2) p -
            ∑ i : Fin n, Real.rpow (|(a • xt + b • ys).1 i|) p := by
        simpa [slack] using hslack_combo_pos
      linarith
    simpa [S, one_div] using
      ((Real.rpow_inv_lt_iff_of_pos hcombo_sum_nonneg (le_of_lt hcombo_t_pos) hp_pos).2
        hcombo_sum_lt)
  -- The strong slack inequality is exactly the concavity statement for the slack root.
  have hδ_concaveOn : ConcaveOn ℝ S δ := by
    refine concaveOn_iff_forall_pos.2 ⟨hSconvex, ?_⟩
    intro xt hxt ys hys a b ha hb hab
    simpa [smul_eq_mul] using hδ_concavity hxt hys ha hb hab
  -- Concavity of `log ∘ δ` follows from concavity of `log` on `(0, ∞)` plus monotonicity of `log`.
  have hlogδ_concaveOn : ConcaveOn ℝ S (fun xt => Real.log (δ xt)) := by
    refine concaveOn_iff_forall_pos.2 ⟨hSconvex, ?_⟩
    intro xt hxt ys hys a b ha hb hab
    have hδxt_pos := hδ_pos hxt
    have hδys_pos := hδ_pos hys
    have hδ_combo := hδ_concavity hxt hys ha hb hab
    have hleft_pos : 0 < a * δ xt + b * δ ys := by positivity
    have hlog_mid :
        a * Real.log (δ xt) + b * Real.log (δ ys) ≤ Real.log (a * δ xt + b * δ ys) := by
      simpa [smul_eq_mul] using
        (strictConcaveOn_log_Ioi.concaveOn.2 hδxt_pos hδys_pos ha.le hb.le hab)
    exact hlog_mid.trans (Real.log_le_log hleft_pos hδ_combo)
  -- Negating and scaling by the positive constant `p` converts concavity of `log ∘ δ`
  -- into convexity of the barrier written as `p * (-log δ)`.
  have hscaled_barrier : ConvexOn ℝ S (fun xt => p * (-Real.log (δ xt))) := by
    simpa [smul_eq_mul] using (hlogδ_concaveOn.neg.smul hp_pos.le)
  have hbarrier : ConvexOn ℝ S (fun xt => -Real.log (slack xt)) := by
    refine hscaled_barrier.congr ?_
    intro xt hxt
    have hslack_xt_pos := hslack_pos hxt
    have hp_mul_inv : p * (1 / p) = 1 := by
      field_simp [hp_ne]
    calc
      p * (-Real.log (δ xt)) = -(p * Real.log (δ xt)) := by ring
      _ = -(p * ((1 / p) * Real.log (slack xt))) := by
            congr 1
            rw [show Real.log (δ xt) = (1 / p) * Real.log (slack xt) by
                  dsimp [δ]
                  rw [Real.log_rpow hslack_xt_pos]]
      _ = -Real.log (slack xt) := by
            calc
              -(p * ((1 / p) * Real.log (slack xt)))
                  = -((p * (1 / p)) * Real.log (slack xt)) := by ring
              _ = -Real.log (slack xt) := by rw [hp_mul_inv, one_mul]
  simpa [S, slack] using hbarrier

end «problem-114»
