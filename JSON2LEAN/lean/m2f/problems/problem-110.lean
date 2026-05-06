import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-110»
/-
Let A₀, …, Aₙ be real symmetric m×m matrices and define M(x) = A₀ + x₁A₁ + ··· + x_nA_n. On the
domain {x:
M(x) ≻ 0}, define f(x) = −(det M(x))^(1/m). Prove that f is convex on this domain.
-/
open scoped BigOperators Matrix

/-- The affine matrix map `x ↦ A 0 + ∑ i, x i • A i.succ` preserves convex combinations. -/
lemma matrixAffine_eval_smul_add
    {m n : ℕ}
    (A : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ)
    {x y : Fin n → ℝ} {a b : ℝ} (hab : a + b = 1) :
    A 0 + ∑ i : Fin n, ((a • x + b • y) i) • A i.succ =
      a • (A 0 + ∑ i : Fin n, (x i) • A i.succ) +
        b • (A 0 + ∑ i : Fin n, (y i) • A i.succ) := by
  -- Expand the pointwise affine combination and regroup the matrix terms.
  let SX : Matrix (Fin m) (Fin m) ℝ := ∑ i : Fin n, (x i) • A i.succ
  let SY : Matrix (Fin m) (Fin m) ℝ := ∑ i : Fin n, (y i) • A i.succ
  calc
    A 0 + ∑ i : Fin n, ((a • x + b • y) i) • A i.succ
      = A 0 + ∑ i : Fin n, ((a * x i) • A i.succ + (b * y i) • A i.succ) := by
          simp [Pi.smul_apply, add_smul]
    _ = A 0 + ∑ i : Fin n, (a • ((x i) • A i.succ) + b • ((y i) • A i.succ)) := by
          simp [smul_smul]
    _ = A 0 + (a • SX + b • SY) := by
          simp [SX, SY, Finset.sum_add_distrib, Finset.smul_sum]
    _ = (a • A 0 + b • A 0) + (a • SX + b • SY) := by
          calc
            A 0 + (a • SX + b • SY) = (a + b) • A 0 + (a • SX + b • SY) := by
              rw [hab, one_smul]
            _ = (a • A 0 + b • A 0) + (a • SX + b • SY) := by
              rw [add_smul]
    _ = (a • A 0 + a • SX) + (b • A 0 + b • SY) := by ac_rfl
    _ = a • (A 0 + SX) + b • (A 0 + SY) := by rw [smul_add, smul_add]
    _ = a • (A 0 + ∑ i : Fin n, (x i) • A i.succ) +
          b • (A 0 + ∑ i : Fin n, (y i) • A i.succ) := by
          simp [SX, SY]

/-- A convex combination of positive-definite real matrices is positive definite. -/
lemma posDef_convexCombination
    {m : ℕ}
    {X Y : Matrix (Fin m) (Fin m) ℝ}
    (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • X + b • Y).PosDef := by
  -- Split off the zero-weight edge cases before using positivity of the coefficients.
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    simpa [hb1]
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have ha1 : a = 1 := by linarith
    simpa [ha1, add_comm]
  -- In the genuine convex-combination case, positivity is preserved by scaling and addition.
  exact (hX.smul ha').add (hY.smul hb')

/-- The determinant root of a positive-definite matrix is bounded by its normalized trace. -/
lemma det_root_le_trace_div
    {m : ℕ} (hm : 0 < m)
    {X : Matrix (Fin m) (Fin m) ℝ} (hX : X.PosDef) :
    Real.rpow (Matrix.det X) (1 / (m : ℝ)) ≤ Matrix.trace X / m := by
  -- Apply the scalar AM-GM inequality to the positive eigenvalues of `X`.
  have hgm :=
    Real.geom_mean_le_arith_mean (s := Finset.univ)
      (w := fun _ : Fin m => (1 : ℝ))
      (z := fun i : Fin m => hX.isHermitian.eigenvalues i)
      (fun _ _ => by positivity)
      (by
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        simpa using hmR)
      (fun i _ => (hX.eigenvalues_pos i).le)
  -- Rewrite the geometric and arithmetic sides back into determinant and trace.
  simpa [hX.isHermitian.det_eq_prod_eigenvalues, hX.isHermitian.trace_eq_sum_eigenvalues,
    Real.rpow_one, one_div, div_eq_mul_inv] using hgm

/-- A determinant-one positive-definite matrix yields a supporting affine lower bound for the
determinant root. -/
lemma det_root_supporting_le
    {m : ℕ} (hm : 0 < m)
    {X Y : Matrix (Fin m) (Fin m) ℝ}
    (hX : X.PosDef) (hY : Y.PosDef) (hdetY : Matrix.det Y = 1) :
    Real.rpow (Matrix.det X) (1 / (m : ℝ)) ≤ Matrix.trace (X * Y) / m := by
  obtain ⟨B, hB_unit, hY_fac⟩ := Matrix.posDef_iff_eq_conjTranspose_mul_self.mp hY
  have hY_fac_star : Y = star B * B := by
    simpa [Matrix.star_eq_conjTranspose] using hY_fac
  have hconj : (B * X * star B).PosDef := by
    -- Conjugating by an invertible factor preserves positive definiteness.
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := X) hB_unit).2 hX
  have hdet_star : Matrix.det (star B) = Matrix.det B := by
    -- Over `ℝ`, the determinant is unchanged by conjugate transpose.
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
    simp
  have htrace :
      Matrix.trace (B * X * star B) = Matrix.trace (X * Y) := by
    -- Cycle the trace and then use the factorization `Y = Bᴴ * B`.
    calc
      Matrix.trace (B * X * star B) = Matrix.trace ((star B * B) * X) := by
        simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle B X (star B)
      _ = Matrix.trace (Y * X) := by rw [← hY_fac_star]
      _ = Matrix.trace (X * Y) := by
        rw [Matrix.trace_mul_comm]
  have hdet :
      Matrix.det (B * X * star B) = Matrix.det X := by
    -- The determinant is unchanged because the conjugating factor has determinant `det Y = 1`.
    calc
      Matrix.det (B * X * star B) = Matrix.det (B * X) * Matrix.det (star B) := by
        rw [Matrix.det_mul]
      _ = Matrix.det B * Matrix.det X * Matrix.det (star B) := by
        rw [Matrix.det_mul]
      _ = Matrix.det B * Matrix.det X * Matrix.det B := by rw [hdet_star]
      _ = Matrix.det X * Matrix.det (star B * B) := by
        rw [Matrix.det_mul, hdet_star]
        ring
      _ = Matrix.det X * Matrix.det Y := by rw [← hY_fac_star]
      _ = Matrix.det X := by rw [hdetY, mul_one]
  -- Finish with AM-GM on the conjugated matrix.
  simpa [hdet, htrace] using det_root_le_trace_div hm hconj

theorem neg_det_root_convexOn_posDef_domain
    {m n : ℕ}
    (hm : 0 < m)
    (A : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, (A i)ᵀ = A i) :
    ConvexOn ℝ
      {x : Fin n → ℝ | Matrix.PosDef (A 0 + ∑ i : Fin n, (x i) • A i.succ)}
      (fun x => -Real.rpow (Matrix.det (A 0 + ∑ i : Fin n, (x i) • A i.succ)) (1 / (m : ℝ))) := by
  -- The symmetry data is part of the exercise statement, but the proof uses only positivity on the
  -- chosen domain points.
  let _ := hA
  let M : (Fin n → ℝ) → Matrix (Fin m) (Fin m) ℝ :=
    fun x => A 0 + ∑ i : Fin n, (x i) • A i.succ
  change ConvexOn ℝ {x : Fin n → ℝ | Matrix.PosDef (M x)}
    (fun x => -Real.rpow (Matrix.det (M x)) (1 / (m : ℝ)))
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    -- The domain is convex because `M` is affine and the positive-definite cone is convex.
    change Matrix.PosDef (M (a • x + b • y))
    rw [show M (a • x + b • y) = a • M x + b • M y by
      simpa [M] using matrixAffine_eval_smul_add A (x := x) (y := y) hab]
    exact posDef_convexCombination hx hy ha hb hab
  · intro x hx y hy a b ha hb hab
    -- Route correction: instead of proving determinant-root concavity directly on matrix segments,
    -- use the affine support representation coming from determinant-one test matrices.
    let Z : Matrix (Fin m) (Fin m) ℝ := M (a • x + b • y)
    have hZ_affine : Z = a • M x + b • M y := by
      simpa [Z, M] using matrixAffine_eval_smul_add A (x := x) (y := y) hab
    have hZ : Z.PosDef := by
      -- The Jensen point stays in the positive-definite cone.
      rw [hZ_affine]
      exact posDef_convexCombination hx hy ha hb hab
    let g : ℝ := Real.rpow (Matrix.det Z) (1 / (m : ℝ))
    let W : Matrix (Fin m) (Fin m) ℝ := g • Z⁻¹
    have hg_pos : 0 < g := by
      -- The determinant root is positive on the positive-definite cone.
      dsimp [g]
      exact Real.rpow_pos_of_pos hZ.det_pos _
    have hW : W.PosDef := by
      -- The chosen supporting matrix is a positive scalar multiple of the inverse.
      dsimp [W]
      exact (hZ.inv).smul hg_pos
    have hWdet : Matrix.det W = 1 := by
      -- The normalized inverse has determinant one by construction.
      have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
      have hZdet_pos : 0 < Matrix.det Z := hZ.det_pos
      have hZdet_unit : IsUnit (Matrix.det Z) := (Matrix.isUnit_iff_isUnit_det Z).mp hZ.isUnit
      have hgpow : g ^ m = Matrix.det Z := by
        dsimp [g]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZdet_pos.le]
        field_simp [hm_ne]
        rw [Real.rpow_one]
      dsimp [W]
      rw [Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Fintype.card_fin, hgpow]
      field_simp [hZdet_pos.ne']
    have hsupport_x :
        -(Matrix.trace (M x * W) / m) ≤
          -Real.rpow (Matrix.det (M x)) (1 / (m : ℝ)) := by
      -- Every determinant-one positive-definite matrix underestimates the target function.
      exact neg_le_neg (det_root_supporting_le hm hx hW hWdet)
    have hsupport_y :
        -(Matrix.trace (M y * W) / m) ≤
          -Real.rpow (Matrix.det (M y)) (1 / (m : ℝ)) := by
      -- The same support inequality applies at the second endpoint.
      exact neg_le_neg (det_root_supporting_le hm hy hW hWdet)
    have hZW :
        Z * W = g • (1 : Matrix (Fin m) (Fin m) ℝ) := by
      -- At the supporting point, the affine minorant is exact.
      have hZdet_unit : IsUnit (Matrix.det Z) := (Matrix.isUnit_iff_isUnit_det Z).mp hZ.isUnit
      dsimp [W]
      rw [Matrix.mul_smul, Matrix.mul_nonsing_inv _ hZdet_unit]
    have htraceZW : Matrix.trace (Z * W) / m = g := by
      -- Evaluating the trace of `Z * W` reduces to the trace of a scalar matrix.
      have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
      calc
        Matrix.trace (Z * W) / m = Matrix.trace (g • (1 : Matrix (Fin m) (Fin m) ℝ)) / m := by
          rw [hZW]
        _ = (g * m) / m := by simp [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
        _ = g := by field_simp [hm_ne]
    have htrace_combo :
        Matrix.trace (Z * W) =
          a * Matrix.trace (M x * W) + b * Matrix.trace (M y * W) := by
      -- The supporting functional is affine along the segment.
      rw [hZ_affine, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.trace_smul, Matrix.trace_smul]
      simp [smul_eq_mul]
    have hweighted_support :
        -(Matrix.trace (Z * W) / m) ≤
          a * (-Real.rpow (Matrix.det (M x)) (1 / (m : ℝ))) +
            b * (-Real.rpow (Matrix.det (M y)) (1 / (m : ℝ))) := by
      -- Combine the two endpoint support inequalities using the convex weights.
      have hx' := mul_le_mul_of_nonneg_left hsupport_x ha
      have hy' := mul_le_mul_of_nonneg_left hsupport_y hb
      have hsum := add_le_add hx' hy'
      have hrewrite :
          -(Matrix.trace (Z * W) / m) =
            a * (-(Matrix.trace (M x * W) / m)) + b * (-(Matrix.trace (M y * W) / m)) := by
        rw [htrace_combo]
        ring
      rw [hrewrite]
      exact hsum
    -- Replace the exact supporting value at `Z` and conclude the convexity inequality.
    rw [htraceZW] at hweighted_support
    simpa [Z, g] using hweighted_support

end «problem-110»
