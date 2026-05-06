import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open scoped MatrixOrder
open Filter
open scoped BigOperators

namespace «problem-49»
/-
Let 0 < p < 1. Define the function f: ℝ_{++}^n o ℝ by f(x) = (sum_{i = 1}^n xᵢ^p ight)^{1/p}, where
ℝ_{++}^n = {x = (x₁,..., xₙ)∈ ℝ^n: xᵢ > 0, i = 1,..., n}. Using the second-order criterion for
concavity of differentiable functions, prove that f is concave on ℝ_{++}^n.
-/
open scoped BigOperators

theorem lp_quasinorm_concave_on_positive_orthant
    {n : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ i, 0 < x i}
      (fun x => Real.rpow (∑ i, Real.rpow (x i) p) (1 / p)) := by
  by_cases hn : n = 0
  · subst hn
    -- In dimension zero, the domain is `univ` and the quasinorm is the constant zero function.
    have hp_inv : 0 < 1 / p := by positivity
    rw [concaveOn_iff_forall_pos]
    constructor
    · simpa using (convex_univ : Convex ℝ (Set.univ : Set (Fin 0 → ℝ)))
    · intro x hx y hy a b ha hb hab
      have hzero : Real.rpow (0 : ℝ) (1 / p) = 0 := Real.zero_rpow hp_inv.ne'
      have hxsum : ∑ i, Real.rpow (x i) p = 0 := by simp
      have hysum : ∑ i, Real.rpow (y i) p = 0 := by simp
      have hzsum : ∑ i, Real.rpow ((a • x + b • y) i) p = 0 := by simp
      rw [hxsum, hysum, hzsum, hzero]
      simpa [smul_eq_mul]
  · let F : (Fin n → ℝ) → ℝ := fun x => Real.rpow (∑ i, Real.rpow (x i) p) (1 / p)
    -- Positive vectors have a strictly positive `p`-power sum once the index type is nonempty.
    have hsum_pos : ∀ {x : Fin n → ℝ}, (∀ i, 0 < x i) → 0 < ∑ i, Real.rpow (x i) p := by
      intro x hx
      have hn' : 0 < n := Nat.pos_iff_ne_zero.mpr hn
      haveI : Nonempty (Fin n) := ⟨⟨0, hn'⟩⟩
      exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (hx i) p) Finset.univ_nonempty
    -- Weighted Hölder gives a supporting inequality for the quasinorm at each positive base point.
    have hsupport :
        ∀ {x y : Fin n → ℝ}, (∀ i, 0 < x i) → (∀ i, 0 < y i) →
          F y ≤
            Real.rpow (∑ i, Real.rpow (x i) p) (1 / p - 1) *
              ∑ i, Real.rpow (x i) p * (y i / x i) := by
      intro x y hx hy
      let A : ℝ := ∑ i, Real.rpow (x i) p
      let C : ℝ := ∑ i, Real.rpow (x i) p * (y i / x i)
      have hq : 1 ≤ 1 / p := by
        rw [one_le_div hp0]
        linarith
      have hA_pos : 0 < A := hsum_pos hx
      have hA_nonneg : 0 ≤ A := hA_pos.le
      have hC_nonneg : 0 ≤ C := by
        unfold C
        refine Finset.sum_nonneg fun i _ => ?_
        have hdiv_nonneg : 0 ≤ y i / x i := div_nonneg (hy i).le (hx i).le
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt (hx i)) p) hdiv_nonneg
      have hF_nonneg : 0 ≤ F y := by
        dsimp [F]
        exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (le_of_lt (hy i)) p) _
      have hrhs_nonneg :
          0 ≤ Real.rpow A (1 / p - 1) * C := by
        exact mul_nonneg (Real.rpow_nonneg hA_nonneg _) hC_nonneg
      have hholder :
          ∑ i, Real.rpow (y i) p ≤ Real.rpow A (1 - p) * Real.rpow C p := by
        have hraw :=
          Real.inner_le_weight_mul_Lp_of_nonneg (s := Finset.univ) (p := 1 / p) hq
            (fun i => Real.rpow (x i) p) (fun i => Real.rpow (y i / x i) p)
            (fun i => Real.rpow_nonneg (le_of_lt (hx i)) p)
            (fun i => Real.rpow_nonneg (div_nonneg (hy i).le (hx i).le) p)
        calc
          ∑ i, Real.rpow (y i) p = ∑ i, Real.rpow (x i) p * Real.rpow (y i / x i) p := by
            symm
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              Real.rpow (x i) p * Real.rpow (y i / x i) p =
                  Real.rpow (x i * (y i / x i)) p := by
                simpa using
                  (Real.mul_rpow (le_of_lt (hx i)) (div_nonneg (hy i).le (hx i).le) (z := p)).symm
              _ = Real.rpow (y i) p := by
                field_simp [ne_of_gt (hx i)]
          _ ≤ Real.rpow A (1 - (1 / p)⁻¹) *
                Real.rpow
                  (∑ i, Real.rpow (x i) p * Real.rpow (Real.rpow (y i / x i) p) (1 / p))
                  ((1 / p)⁻¹) := by
            simpa [A] using hraw
          _ = Real.rpow A (1 - p) * Real.rpow C p := by
            have hp_inv : (1 / p : ℝ)⁻¹ = p := by field_simp [hp0.ne']
            have hsum_eq :
                ∑ i, Real.rpow (x i) p * Real.rpow (Real.rpow (y i / x i) p) (1 / p) = C := by
              unfold C
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hcancel :
                  Real.rpow (Real.rpow (y i / x i) p) (1 / p) = Real.rpow (y i / x i) (p * (1 / p)) := by
                simpa using
                  (Real.rpow_mul (div_nonneg (hy i).le (hx i).le) p (1 / p)).symm
              have hmulpinv : p * (1 / p) = 1 := by
                field_simp [hp0.ne']
              rw [hcancel, hmulpinv]
              congr 1
              simpa using (Real.rpow_one (y i / x i))
            rw [hp_inv, hsum_eq]
      -- Raise both sides to the positive power `p` to convert Hölder's estimate into the support inequality.
      rw [← Real.rpow_le_rpow_iff hF_nonneg hrhs_nonneg hp0]
      calc
        Real.rpow (F y) p = ∑ i, Real.rpow (y i) p := by
          change Real.rpow (Real.rpow (∑ i, Real.rpow (y i) p) (1 / p)) p = _
          have hpow :
              Real.rpow (Real.rpow (∑ i, Real.rpow (y i) p) (1 / p)) p =
                Real.rpow (∑ i, Real.rpow (y i) p) ((1 / p) * p) := by
            simpa using
              (Real.rpow_mul
                (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (le_of_lt (hy i)) p) (1 / p) p).symm
          have hinv_mul : (1 / p) * p = 1 := by
            field_simp [hp0.ne']
          rw [hpow, hinv_mul]
          simpa using (Real.rpow_one (∑ i, Real.rpow (y i) p))
        _ ≤ Real.rpow A (1 - p) * Real.rpow C p := hholder
        _ = Real.rpow
              (Real.rpow A (1 / p - 1) * C) p := by
          have hexp : (1 / p - 1) * p = 1 - p := by
            field_simp [hp0.ne']
          calc
            Real.rpow A (1 - p) * Real.rpow C p
                = Real.rpow A ((1 / p - 1) * p) * Real.rpow C p := by rw [hexp]
            _ = Real.rpow (Real.rpow A (1 / p - 1)) p * Real.rpow C p := by
              congr 1
              simpa using (Real.rpow_mul hA_nonneg (1 / p - 1) p)
            _ = Real.rpow (Real.rpow A (1 / p - 1) * C) p := by
              simpa using
                (Real.mul_rpow (Real.rpow_nonneg hA_nonneg _) hC_nonneg (z := p)).symm
    -- Evaluating the same support functional at `x` and `y` yields superadditivity.
    have hsuper :
        ∀ {x y : Fin n → ℝ}, (∀ i, 0 < x i) → (∀ i, 0 < y i) → F x + F y ≤ F (x + y) := by
      intro x y hx hy
      have hxy : ∀ i, 0 < x i + y i := by
        intro i
        linarith [hx i, hy i]
      have hx' := hsupport hxy hx
      have hy' := hsupport hxy hy
      let A : ℝ := ∑ i, Real.rpow (x i + y i) p
      have hA_pos : 0 < A := hsum_pos hxy
      calc
        F x + F y ≤
            Real.rpow A (1 / p - 1) *
                ∑ i, Real.rpow (x i + y i) p * (x i / (x i + y i)) +
              Real.rpow A (1 / p - 1) *
                ∑ i, Real.rpow (x i + y i) p * (y i / (x i + y i)) := by
          exact add_le_add hx' hy'
        _ = Real.rpow A (1 / p - 1) *
              (∑ i, Real.rpow (x i + y i) p * (x i / (x i + y i)) +
                ∑ i, Real.rpow (x i + y i) p * (y i / (x i + y i))) := by ring
        _ = Real.rpow A (1 / p - 1) * ∑ i, Real.rpow (x i + y i) p := by
          congr 1
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hz_ne : x i + y i ≠ 0 := ne_of_gt (hxy i)
          field_simp [hz_ne]
        _ = F (x + y) := by
          dsimp [F, A]
          have hAeq :
              Real.rpow (∑ i, Real.rpow (x i + y i) p) (1 / p - 1) *
                  (∑ i, Real.rpow (x i + y i) p) =
                Real.rpow (∑ i, Real.rpow (x i + y i) p) (1 / p) := by
            calc
              Real.rpow (∑ i, Real.rpow (x i + y i) p) (1 / p - 1) *
                  (∑ i, Real.rpow (x i + y i) p) =
                  Real.rpow (∑ i, Real.rpow (x i + y i) p) (1 / p - 1) *
                    Real.rpow (∑ i, Real.rpow (x i + y i) p) 1 := by
                congr 1
                simpa using (Real.rpow_one (∑ i, Real.rpow (x i + y i) p))
              _ = Real.rpow (∑ i, Real.rpow (x i + y i) p) ((1 / p - 1) + 1) := by
                symm
                exact Real.rpow_add hA_pos (1 / p - 1) 1
              _ = Real.rpow (∑ i, Real.rpow (x i + y i) p) (1 / p) := by ring_nf
          exact hAeq
    -- Positive homogeneity turns superadditivity into concavity on the positive orthant.
    have hhom :
        ∀ {c : ℝ} {x : Fin n → ℝ}, 0 ≤ c → (∀ i, 0 < x i) → F (c • x) = c * F x := by
      intro c x hc hx
      rcases eq_or_lt_of_le hc with rfl | hc'
      · dsimp [F]
        have hp_inv : 0 < 1 / p := by positivity
        have hzero : Real.rpow (0 : ℝ) (1 / p) = 0 := Real.zero_rpow hp_inv.ne'
        simpa [Real.zero_rpow hp0.ne'] using hzero
      · have hsum :
          ∑ i, Real.rpow (c * x i) p = Real.rpow c p * ∑ i, Real.rpow (x i) p := by
          calc
            ∑ i, Real.rpow (c * x i) p = ∑ i, Real.rpow c p * Real.rpow (x i) p := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa using Real.mul_rpow hc'.le (le_of_lt (hx i)) (z := p)
            _ = Real.rpow c p * ∑ i, Real.rpow (x i) p := by rw [Finset.mul_sum]
        have hcpow : Real.rpow (Real.rpow c p) (1 / p) = c := by
          have hpow : Real.rpow (Real.rpow c p) (1 / p) = Real.rpow c (p * (1 / p)) := by
            simpa using (Real.rpow_mul hc'.le p (1 / p)).symm
          have hmulpinv : p * (1 / p) = 1 := by
            field_simp [hp0.ne']
          rw [hpow, hmulpinv]
          simpa using (Real.rpow_one c)
        calc
          F (c • x) = Real.rpow (Real.rpow c p * ∑ i, Real.rpow (x i) p) (1 / p) := by
            simpa [F, Pi.smul_apply] using congrArg (fun t => Real.rpow t (1 / p)) hsum
          _ = Real.rpow (Real.rpow c p) (1 / p) * Real.rpow (∑ i, Real.rpow (x i) p) (1 / p) := by
            simpa using
              (Real.mul_rpow (Real.rpow_nonneg hc p)
                (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (le_of_lt (hx i)) p) (z := 1 / p))
          _ = c * F x := by rw [hcpow]
    rw [concaveOn_iff_forall_pos]
    constructor
    · -- Positive coordinates are preserved by strict convex combinations.
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
      change a * F x + b * F y ≤ F (a • x + b • y)
      calc
        a * F x + b * F y = F (a • x) + F (b • y) := by
          rw [hhom ha.le hx, hhom hb.le hy]
        _ ≤ F (a • x + b • y) := hsuper hax hby

/-- The cone of positive definite real matrices is convex. -/
lemma convex_setOf_posDef
    (n : ℕ) :
    Convex ℝ {X : Matrix (Fin n) (Fin n) ℝ | X.PosDef} := by
  intro X hX Y hY a b ha hb hab
  rcases eq_or_lt_of_le ha with rfl | ha'
  · -- If the first weight vanishes, the convex combination is just `Y`.
    have hb1 : b = 1 := by linarith
    simpa [hb1]
  rcases eq_or_lt_of_le hb with rfl | hb'
  · -- If the second weight vanishes, the convex combination is just `X`.
    have ha1 : a = 1 := by linarith
    simpa [ha1, add_comm]
  · -- In the genuine convex-combination case, positivity is preserved by scaling and addition.
    exact (hX.smul ha').add (hY.smul hb')

/-- The scalar barrier inequality `tr A - n - log det A ≥ 0` on the positive definite cone. -/
lemma trace_sub_log_det_nonneg_of_posDef
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    0 ≤ Matrix.trace A - (n : ℝ) - Real.log (Matrix.det A) := by
  -- Rewrite trace and determinant through the Hermitian spectral theorem.
  have htrace : Matrix.trace A = ∑ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.trace_eq_sum_eigenvalues
  have hdet : Matrix.det A = ∏ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.det_eq_prod_eigenvalues
  have hlog : Real.log (Matrix.det A) = ∑ i, Real.log (hA.isHermitian.eigenvalues i) := by
    rw [hdet, Real.log_prod]
    intro i hi
    exact (hA.eigenvalues_pos i).ne'
  rw [htrace, hlog]
  have hsum :
      0 ≤ ∑ i,
        (hA.isHermitian.eigenvalues i - 1 - Real.log (hA.isHermitian.eigenvalues i)) := by
    -- Each eigenvalue contributes the scalar inequality `log u ≤ u - 1`.
    refine Finset.sum_nonneg ?_
    intro i hi
    have hi : 0 < hA.isHermitian.eigenvalues i := hA.eigenvalues_pos i
    linarith [Real.log_le_sub_one_of_pos hi]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  norm_num at hsum ⊢
  linarith

/-- The supporting-hyperplane inequality for `X ↦ -log(det X)` on positive definite matrices. -/
lemma neg_log_det_supporting_inequality
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    -Real.log (Matrix.det B) ≥
      -Real.log (Matrix.det A) - Matrix.trace (A⁻¹ * (B - A)) := by
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (A⁻¹)
  have hSpos : S.PosDef := by
    -- The positive square root of the inverse remains positive definite.
    exact Matrix.isStrictlyPositive_iff_posDef.mp (hA.inv.isStrictlyPositive.sqrt)
  have hSeq : Sᵀ = S := by
    -- Over `ℝ`, Hermitian means symmetric.
    simpa [Matrix.IsHermitian] using hSpos.isHermitian.eq
  have hSdetpos : 0 < Matrix.det S := hSpos.det_pos
  have hSdet_ne : Matrix.det S ≠ 0 := ne_of_gt hSdetpos
  have hSsq : S * S = A⁻¹ := by
    -- `S` squares back to `A⁻¹`.
    simp [S, CFC.sqrt_mul_sqrt_self (A⁻¹) (show 0 ≤ A⁻¹ from hA.inv.posSemidef.nonneg)]
  have hMpos : (S * B * S).PosDef := by
    -- Conjugation by the invertible square root preserves positive definiteness.
    have hSunit : IsUnit S := hSpos.isUnit
    have hconj : (S * B * star S).PosDef := by
      exact (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := B) (U := S) hSunit).2 hB
    simpa [Matrix.star_eq_conjTranspose, hSeq] using hconj
  have htraceS : Matrix.trace (S * B * S) = Matrix.trace (A⁻¹ * B) := by
    -- Use cyclic invariance of the trace and then collapse `S^2`.
    calc
      Matrix.trace (S * B * S) = Matrix.trace (S * S * B) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (A⁻¹ * B) := by rw [hSsq]
  have hdetS : Matrix.det S * Matrix.det S = Matrix.det (A⁻¹) := by
    -- The determinant also sees the identity `S^2 = A⁻¹`.
    have hdet := congrArg Matrix.det hSsq
    simpa [Matrix.det_mul] using hdet
  have hlogS :
      Real.log (Matrix.det (S * B * S)) = Real.log (Matrix.det B) - Real.log (Matrix.det A) := by
    have hBdetpos : 0 < Matrix.det B := hB.det_pos
    have hBdet_ne : Matrix.det B ≠ 0 := ne_of_gt hBdetpos
    -- Factor the determinant of the conjugated matrix and simplify the inverse term.
    calc
      Real.log (Matrix.det (S * B * S)) =
          Real.log (Matrix.det S * Matrix.det B * Matrix.det S) := by
        rw [Matrix.det_mul, Matrix.det_mul]
      _ = Real.log (Matrix.det S) + Real.log (Matrix.det B) + Real.log (Matrix.det S) := by
        rw [show Matrix.det S * Matrix.det B * Matrix.det S =
            (Matrix.det S * Matrix.det B) * Matrix.det S by ring,
          Real.log_mul (mul_ne_zero hSdet_ne hBdet_ne) hSdet_ne,
          Real.log_mul hSdet_ne hBdet_ne]
      _ = Real.log (Matrix.det S * Matrix.det S) + Real.log (Matrix.det B) := by
        rw [Real.log_mul hSdet_ne hSdet_ne]
        ring
      _ = Real.log (Matrix.det (A⁻¹)) + Real.log (Matrix.det B) := by
        rw [hdetS]
      _ = -Real.log (Matrix.det A) + Real.log (Matrix.det B) := by
        rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv]
      _ = Real.log (Matrix.det B) - Real.log (Matrix.det A) := by ring
  have htraceAA : Matrix.trace (A⁻¹ * A) = (n : ℝ) := by
    -- The inverse multiplied by `A` is the identity, whose trace is `n`.
    have hunit : IsUnit (Matrix.det A) := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
    simpa using congrArg Matrix.trace (Matrix.nonsing_inv_mul A hunit)
  have hbarrier := trace_sub_log_det_nonneg_of_posDef (S * B * S) hMpos
  have hcore :
      0 ≤ Matrix.trace (A⁻¹ * B) - (n : ℝ) - (Real.log (Matrix.det B) - Real.log (Matrix.det A)) := by
    rw [htraceS, hlogS] at hbarrier
    exact hbarrier
  have htrace_sub :
      Matrix.trace (A⁻¹ * (B - A)) = Matrix.trace (A⁻¹ * B) - (n : ℝ) := by
    -- The trace term separates linearly into the `B` and `A` contributions.
    rw [Matrix.mul_sub, Matrix.trace_sub, htraceAA]
  linarith [hcore, htrace_sub]

/-- The function `X ↦ -log(det X)` is convex on the positive definite cone. -/
lemma convexOn_neg_log_det_posDef
    (n : ℕ) :
    ConvexOn ℝ
      {X : Matrix (Fin n) (Fin n) ℝ | X.PosDef}
      (fun X => -Real.log (Matrix.det X)) := by
  refine ⟨convex_setOf_posDef n, ?_⟩
  intro X hX Y hY a b ha hb hab
  let Z : Matrix (Fin n) (Fin n) ℝ := a • X + b • Y
  have hZ : Z.PosDef := (convex_setOf_posDef n) hX hY ha hb hab
  have hZX := neg_log_det_supporting_inequality Z X hZ hX
  have hZY := neg_log_det_supporting_inequality Z Y hZ hY
  have hweighted :
      a * (-Real.log (Matrix.det X)) + b * (-Real.log (Matrix.det Y)) ≥
        (a + b) * (-Real.log (Matrix.det Z)) -
          (a * Matrix.trace (Z⁻¹ * (X - Z)) + b * Matrix.trace (Z⁻¹ * (Y - Z))) := by
    -- Multiply the two support inequalities by the convex weights and add them.
    nlinarith
  have hcombo_zero :
      a • (X - Z) + b • (Y - Z) = (0 : Matrix (Fin n) (Fin n) ℝ) := by
    -- The weighted displacement from the base point cancels because `Z = aX + bY`.
    ext i j
    have hb_eq : b = 1 - a := by linarith
    subst b
    simp [Z, sub_eq_add_neg]
    ring
  have htrace_cancel :
      a * Matrix.trace (Z⁻¹ * (X - Z)) + b * Matrix.trace (Z⁻¹ * (Y - Z)) = 0 := by
    -- Trace is linear, so the previous cancellation happens inside the trace as well.
    calc
      a * Matrix.trace (Z⁻¹ * (X - Z)) + b * Matrix.trace (Z⁻¹ * (Y - Z))
          = a • Matrix.trace (Z⁻¹ * (X - Z)) + b • Matrix.trace (Z⁻¹ * (Y - Z)) := by
              simp [smul_eq_mul]
      _ = Matrix.trace (a • (Z⁻¹ * (X - Z))) + Matrix.trace (b • (Z⁻¹ * (Y - Z))) := by
            rw [Matrix.trace_smul, Matrix.trace_smul]
      _ = Matrix.trace (a • (Z⁻¹ * (X - Z)) + b • (Z⁻¹ * (Y - Z))) := by
            rw [Matrix.trace_add]
      _ = Matrix.trace (Z⁻¹ * (a • (X - Z) + b • (Y - Z))) := by
            rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
      _ = 0 := by rw [hcombo_zero]; simp
  have hfinal : -Real.log (Matrix.det Z) ≤
      a * (-Real.log (Matrix.det X)) + b * (-Real.log (Matrix.det Y)) := by
    -- After the trace term disappears, only the convexity inequality remains.
    rw [htrace_cancel, hab, one_mul, sub_zero] at hweighted
    linarith
  simpa [Z, smul_eq_mul] using hfinal

/-- The perspective rewrite for the base function `X ↦ -log(det X)`. -/
lemma perspective_neg_log_det_eq
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosDef) {t : ℝ} (ht : 0 < t) :
    t * (-Real.log (Matrix.det (t⁻¹ • X))) =
      (n : ℝ) * t * Real.log t - t * Real.log (Matrix.det X) := by
  have ht_ne : t ≠ 0 := ht.ne'
  have hdet_pos : 0 < Matrix.det X := hX.det_pos
  have hdet_ne : Matrix.det X ≠ 0 := hdet_pos.ne'
  have hpow_ne : (t⁻¹) ^ n ≠ 0 := by
    exact pow_ne_zero _ (inv_ne_zero ht_ne)
  have hlogpow : Real.log ((t⁻¹) ^ n) = (n : ℝ) * Real.log (t⁻¹) := by
    simpa using (Real.log_pow (t⁻¹) n)
  -- Rewrite the determinant of the scaled matrix and simplify the scalar logarithms.
  calc
    t * (-Real.log (Matrix.det (t⁻¹ • X)))
        = t * (-Real.log ((t⁻¹) ^ n * Matrix.det X)) := by
            rw [Matrix.det_smul]
            simp
    _ = t * (-(Real.log ((t⁻¹) ^ n) + Real.log (Matrix.det X))) := by
          rw [Real.log_mul hpow_ne hdet_ne]
    _ = t * (-(n : ℝ) * Real.log (t⁻¹) - Real.log (Matrix.det X)) := by
          rw [hlogpow]
          ring
    _ = t * ((n : ℝ) * Real.log t - Real.log (Matrix.det X)) := by
          have hinner :
              (-(n : ℝ) * Real.log (t⁻¹) - Real.log (Matrix.det X)) =
                (n : ℝ) * Real.log t - Real.log (Matrix.det X) := by
            rw [Real.log_inv]
            ring_nf
          rw [hinner]
    _ = (n : ℝ) * t * Real.log t - t * Real.log (Matrix.det X) := by ring


theorem convexOn_spd_pos_log_det_perspective
    (n : ℕ) :
    ConvexOn ℝ
      { p : Matrix (Fin n) (Fin n) ℝ × ℝ |
          p.1.PosDef ∧ 0 < p.2 }
      (fun p =>
        (n : ℝ) * p.2 * Real.log p.2 - p.2 * Real.log (Matrix.det p.1)) := by
  let base : Matrix (Fin n) (Fin n) ℝ → ℝ := fun X => -Real.log (Matrix.det X)
  have hbase : ConvexOn ℝ {X : Matrix (Fin n) (Fin n) ℝ | X.PosDef} base :=
    convexOn_neg_log_det_posDef n
  refine ⟨?_, ?_⟩
  · -- The domain is the product of the convex positive-definite cone and the positive half-line.
    intro p hp q hq a b ha hb hab
    refine ⟨(convex_setOf_posDef n) hp.1 hq.1 ha hb hab, ?_⟩
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      simpa [hb1] using hq.2
    rcases eq_or_lt_of_le hb with rfl | hb'
    · have ha1 : a = 1 := by linarith
      simpa [ha1, add_comm] using hp.2
    · simpa [smul_eq_mul] using add_pos (mul_pos ha' hp.2) (mul_pos hb' hq.2)
  · intro p hp q hq a b ha hb hab
    rcases p with ⟨X₁, t₁⟩
    rcases q with ⟨X₂, t₂⟩
    dsimp at hp hq
    let z : ℝ := a * t₁ + b * t₂
    let Z : Matrix (Fin n) (Fin n) ℝ := a • X₁ + b • X₂
    have ht₁_pos : 0 < t₁ := hp.2
    have ht₂_pos : 0 < t₂ := hq.2
    have hz_pos : 0 < z := by
      -- The scalar part of the convex combination stays positive.
      dsimp [z]
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb1 : b = 1 := by linarith
        simpa [hb1] using ht₂_pos
      rcases eq_or_lt_of_le hb with rfl | hb'
      · have ha1 : a = 1 := by linarith
        simpa [ha1, add_comm] using ht₁_pos
      · exact add_pos (mul_pos ha' ht₁_pos) (mul_pos hb' ht₂_pos)
    have hx₁ : t₁⁻¹ • X₁ ∈ {X : Matrix (Fin n) (Fin n) ℝ | X.PosDef} := by
      -- Positive scaling preserves positive definiteness.
      exact hp.1.smul (inv_pos.mpr ht₁_pos)
    have hx₂ : t₂⁻¹ • X₂ ∈ {X : Matrix (Fin n) (Fin n) ℝ | X.PosDef} := by
      -- The same normalization works for the second point.
      exact hq.1.smul (inv_pos.mpr ht₂_pos)
    have hdiv := (convexOn_iff_div.mp hbase).2 hx₁ hx₂
      (show 0 ≤ a * t₁ by positivity)
      (show 0 ≤ b * t₂ by positivity)
      (by simpa [z] using hz_pos)
    have hpoint :
        ((a * t₁) / z) • (t₁⁻¹ • X₁) + ((b * t₂) / z) • (t₂⁻¹ • X₂) = z⁻¹ • Z := by
      -- Normalize the matrix convex combination by the positive scalar `z`.
      ext i j
      have hz_ne : z ≠ 0 := hz_pos.ne'
      have ht₁_ne : t₁ ≠ 0 := ht₁_pos.ne'
      have ht₂_ne : t₂ ≠ 0 := ht₂_pos.ne'
      simp [Z, z]
      field_simp [hz_ne, ht₁_ne, ht₂_ne]
    have hscaled :
        z * base (z⁻¹ • Z) ≤
          a * (t₁ * base (t₁⁻¹ • X₁)) + b * (t₂ * base (t₂⁻¹ • X₂)) := by
      -- Multiply the normalized convexity inequality by the positive denominator `z`.
      have hz_nonneg : 0 ≤ z := hz_pos.le
      have hdiv' :
          base (z⁻¹ • Z) ≤
            ((a * t₁) / z) * base (t₁⁻¹ • X₁) + ((b * t₂) / z) * base (t₂⁻¹ • X₂) := by
        simpa [smul_eq_mul, hpoint, z] using hdiv
      have hmul := mul_le_mul_of_nonneg_left hdiv' hz_nonneg
      have hz_ne : z ≠ 0 := hz_pos.ne'
      have hrewrite :
          z * ((((a * t₁) / z) * base (t₁⁻¹ • X₁)) + (((b * t₂) / z) * base (t₂⁻¹ • X₂))) =
            a * (t₁ * base (t₁⁻¹ • X₁)) + b * (t₂ * base (t₂⁻¹ • X₂)) := by
        field_simp [hz_ne]
      simpa [smul_eq_mul, hrewrite] using hmul
    have hZpos : Z.PosDef := (convex_setOf_posDef n) hp.1 hq.1 ha hb hab
    -- Rewrite the perspective inequality back into the target explicit formula.
    simpa [base, Z, z, smul_eq_mul] using
      (calc
        (n : ℝ) * z * Real.log z - z * Real.log (Matrix.det Z)
            = z * base (z⁻¹ • Z) := by
                simpa [base] using (perspective_neg_log_det_eq hZpos hz_pos).symm
        _ ≤ a * (t₁ * base (t₁⁻¹ • X₁)) + b * (t₂ * base (t₂⁻¹ • X₂)) := hscaled
        _ = a * ((n : ℝ) * t₁ * Real.log t₁ - t₁ * Real.log (Matrix.det X₁)) +
              b * ((n : ℝ) * t₂ * Real.log t₂ - t₂ * Real.log (Matrix.det X₂)) := by
                rw [perspective_neg_log_det_eq hp.1 ht₁_pos, perspective_neg_log_det_eq hq.1 ht₂_pos])

/- [BLOCK Exercise 2.6 | 8 | thm]
Let S_{++}^n denote the set of n × n real symmetric positive definite matrices, and let ℝ_{++} = { t
∈ ℝ | t > 0 }. For X ∈ S_{++}^n, let det X denote the determinant of X, tr X denote the trace of X,
and log denote the natural logarithm. Also show that the function
g(X)=n(trX)log(trX)-(trX)(logdet X)
is convex on S_{++}^n.
-/

theorem convexOn_spd_trace_log_det
    (n : ℕ) :
    ConvexOn ℝ
      { X : Matrix (Fin n) (Fin n) ℝ | X.PosDef }
      (fun X =>
        (n : ℝ) * Matrix.trace X * Real.log (Matrix.trace X) -
          Matrix.trace X * Real.log (Matrix.det X)) := by
  by_cases hn : n = 0
  · subst hn
    -- In dimension zero, the unique matrix has trace `0` and determinant `1`, so the function is constant.
    refine ⟨convex_setOf_posDef 0, ?_⟩
    intro X hX Y hY a b ha hb hab
    have hXY : X = Y := Subsingleton.elim _ _
    simp [hXY]
  · have hn_pos : 0 < n := Nat.pos_iff_ne_zero.mpr hn
    letI : Nonempty (Fin n) := Fintype.card_pos_iff.mp (by simpa using hn_pos)
    have hpersp := convexOn_spd_pos_log_det_perspective n
    refine ⟨convex_setOf_posDef n, ?_⟩
    intro X hX Y hY a b ha hb hab
    have hpairX :
        ((X, Matrix.trace X) :
          Matrix (Fin n) (Fin n) ℝ × ℝ) ∈
          { p : Matrix (Fin n) (Fin n) ℝ × ℝ | p.1.PosDef ∧ 0 < p.2 } := by
      -- Positive definite matrices have positive trace in positive dimension.
      exact ⟨hX, hX.trace_pos⟩
    have hpairY :
        ((Y, Matrix.trace Y) :
          Matrix (Fin n) (Fin n) ℝ × ℝ) ∈
          { p : Matrix (Fin n) (Fin n) ℝ × ℝ | p.1.PosDef ∧ 0 < p.2 } := by
      -- The same trace positivity holds for `Y`.
      exact ⟨hY, hY.trace_pos⟩
    -- Apply the perspective theorem to the affine lift `X ↦ (X, trace X)`.
    simpa [smul_eq_mul, Matrix.trace_add, Matrix.trace_smul, mul_add, add_mul] using
      hpersp.2 hpairX hpairY ha hb hab
end «problem-49»
