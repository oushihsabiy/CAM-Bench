import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-135»
/-
Let x ∈ ℝ^k be a random vector taking values in the finite set {α_1, ..., α_n} ⊂ ℝ^k with
probabilities pᵢ = prob(x = α_i), where pᵢ ≥ 0 for i = 1, ..., n and \sum_{i = 1}^n pᵢ = 1. Its
expectation is Ex = \sum_{i = 1}^n pᵢ α_i, and its covariance matrix is Eigl((x - Ex)(x -
Ex)ᵀigr). Let
S ∈ ℝ^{k \times k} be a given symmetric matrix, and let A preceq B mean that B - A is positive
semidefinite. Show that the constraint S preceq Eigl((x - Ex)(x - Ex)ᵀigr) on the covariance
matrix of
x is a convex constraint in p = (p₁, ..., pₙ).
-/
open scoped BigOperators

/-- The mean vector determined by the weights `p` on the support points `α`. -/
private def meanVec {n k : ℕ} (α : Fin n → Fin k → ℝ) (p : Fin n → ℝ) : Fin k → ℝ :=
  fun x => ∑ l, p l * α l x

/-- The raw second moment matrix determined by the weights `p`. -/
private def rawSecondMoment {n k : ℕ} (α : Fin n → Fin k → ℝ) (p : Fin n → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ i, p i • Matrix.vecMulVec (α i) (α i)

/-- The covariance matrix written directly as a centered second-moment sum. -/
private def covarianceMatrix {n k : ℕ} (α : Fin n → Fin k → ℝ) (p : Fin n → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ i, p i •
    Matrix.vecMulVec
      (fun a => α i a - meanVec α p a)
      (fun b => α i b - meanVec α p b)

/-- The mean vector is affine in the probability weights. -/
private lemma meanVec_convexCombo {n k : ℕ} (α : Fin n → Fin k → ℝ)
    (p q : Fin n → ℝ) (a b : ℝ) :
    meanVec α (fun i => a * p i + b * q i) = a • meanVec α p + b • meanVec α q := by
  -- Expand the mean coordinatewise and distribute the two scalar weights through the finite sum.
  ext x
  change ∑ l, (a * p l + b * q l) * α l x =
    a * (∑ l, p l * α l x) + b * (∑ l, q l * α l x)
  simp [Finset.mul_sum, Finset.sum_add_distrib, mul_assoc, add_mul]

/-- The raw second moment is affine in the probability weights. -/
private lemma rawSecondMoment_convexCombo {n k : ℕ} (α : Fin n → Fin k → ℝ)
    (p q : Fin n → ℝ) (a b : ℝ) :
    rawSecondMoment α (fun i => a * p i + b * q i) =
      a • rawSecondMoment α p + b • rawSecondMoment α q := by
  -- Compare entries and push the convex coefficients through the matrix-valued sum.
  ext x y
  have hentry :
      ∑ i, (a * p i + b * q i) * (α i x * α i y) =
        a * (∑ i, p i * (α i x * α i y)) + b * (∑ i, q i * (α i x * α i y)) := by
    simp [Finset.mul_sum, Finset.sum_add_distrib, mul_assoc, add_mul]
  simpa [rawSecondMoment, Matrix.sum_apply, Matrix.vecMulVec_apply] using hentry

/-- Centering the second moment subtracts the outer product of the mean vector. -/
private lemma covariance_eq_rawSecondMoment_sub_meanOuter {n k : ℕ}
    (α : Fin n → Fin k → ℝ) (p : Fin n → ℝ) (hp : ∑ i, p i = 1) :
    covarianceMatrix α p =
      rawSecondMoment α p - Matrix.vecMulVec (meanVec α p) (meanVec α p) := by
  -- Compare entries and expand the centered product into raw moments and mean terms.
  ext x y
  let mx : ℝ := meanVec α p x
  let my : ℝ := meanVec α p y
  have hmx : ∑ i, p i * α i x = mx := rfl
  have hmy : ∑ i, p i * α i y = my := rfl
  have hentry :
      ∑ i, p i * ((α i x - mx) * (α i y - my)) =
        ∑ i, p i * (α i x * α i y) - mx * my := by
    calc
    ∑ i, p i * ((α i x - mx) * (α i y - my))
      = ∑ i, (p i * (α i x * α i y) - (p i * α i x) * my - mx * (p i * α i y) + p i * (mx * my)) := by
          congr with i
          ring
    _ =
        (∑ i, p i * (α i x * α i y)) - (∑ i, p i * α i x) * my - mx * (∑ i, p i * α i y) +
          (∑ i, p i) * (mx * my) := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
    _ = ∑ i, p i * (α i x * α i y) - mx * my := by
          rw [hmx, hmy, hp]
          ring
  simpa [covarianceMatrix, rawSecondMoment, meanVec, Matrix.sub_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, mx, my] using hentry

/-- The mean outer product along a convex combination differs by a PSD correction term. -/
private lemma meanOuter_combo_correction {k : ℕ} (u v : Fin k → ℝ) {a b : ℝ} (hab : a + b = 1) :
    a • Matrix.vecMulVec u u + b • Matrix.vecMulVec v v -
        Matrix.vecMulVec (a • u + b • v) (a • u + b • v) =
      (a * b) • Matrix.vecMulVec (u - v) (u - v) := by
  -- The defect of the rank-one term is the usual `ab (u - v)(u - v)ᵀ` identity.
  have hb : b = 1 - a := by linarith
  ext x y
  simp [Matrix.sub_apply, Matrix.vecMulVec_apply, hb]
  ring

/-- The covariance matrix of a convex combination is the convex combination plus a PSD defect. -/
private lemma covariance_convexCombo_eq {n k : ℕ} (α : Fin n → Fin k → ℝ)
    (p q : Fin n → ℝ) {a b : ℝ} (hab : a + b = 1) (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) :
    covarianceMatrix α (fun i => a * p i + b * q i) =
      a • covarianceMatrix α p + b • covarianceMatrix α q +
        (a * b) • Matrix.vecMulVec (meanVec α p - meanVec α q) (meanVec α p - meanVec α q) := by
  have hr : ∑ i, (a * p i + b * q i) = 1 := by
    -- The convex combination still has total mass `1`.
    calc
      ∑ i, (a * p i + b * q i) = a * (∑ i, p i) + b * (∑ i, q i) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
      _ = 1 := by simpa [hp, hq] using hab
  -- Rewrite each covariance matrix in terms of raw moments and mean outer products.
  calc
    covarianceMatrix α (fun i => a * p i + b * q i)
      =
        a • (rawSecondMoment α p - Matrix.vecMulVec (meanVec α p) (meanVec α p)) +
        b • (rawSecondMoment α q - Matrix.vecMulVec (meanVec α q) (meanVec α q)) +
        (a * b) • Matrix.vecMulVec (meanVec α p - meanVec α q) (meanVec α p - meanVec α q) := by
          rw [covariance_eq_rawSecondMoment_sub_meanOuter α (fun i => a * p i + b * q i) hr,
            rawSecondMoment_convexCombo α p q a b, meanVec_convexCombo α p q a b]
          calc
            a • rawSecondMoment α p + b • rawSecondMoment α q -
                Matrix.vecMulVec (a • meanVec α p + b • meanVec α q) (a • meanVec α p + b • meanVec α q)
              =
                a • (rawSecondMoment α p - Matrix.vecMulVec (meanVec α p) (meanVec α p)) +
                b • (rawSecondMoment α q - Matrix.vecMulVec (meanVec α q) (meanVec α q)) +
                (a • Matrix.vecMulVec (meanVec α p) (meanVec α p) +
                  b • Matrix.vecMulVec (meanVec α q) (meanVec α q) -
                  Matrix.vecMulVec (a • meanVec α p + b • meanVec α q)
                    (a • meanVec α p + b • meanVec α q)) := by
                  ext x y
                  simp [Matrix.sub_apply]
                  ring
            _ =
                a • (rawSecondMoment α p - Matrix.vecMulVec (meanVec α p) (meanVec α p)) +
                b • (rawSecondMoment α q - Matrix.vecMulVec (meanVec α q) (meanVec α q)) +
                (a * b) • Matrix.vecMulVec (meanVec α p - meanVec α q)
                  (meanVec α p - meanVec α q) := by
                  rw [meanOuter_combo_correction (meanVec α p) (meanVec α q) hab]
    _ =
        a • covarianceMatrix α p + b • covarianceMatrix α q +
        (a * b) • Matrix.vecMulVec (meanVec α p - meanVec α q) (meanVec α p - meanVec α q) := by
          simp [← covariance_eq_rawSecondMoment_sub_meanOuter α p hp,
            ← covariance_eq_rawSecondMoment_sub_meanOuter α q hq]

theorem covariance_lower_bound_constraint_is_convex
    {n k : ℕ} (α : Fin n → Fin k → ℝ) (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.IsSymm) :
    Convex ℝ
      {p : Fin n → ℝ |
        (∀ i, 0 ≤ p i) ∧
        (∑ i, p i = 1) ∧
        Matrix.PosSemidef
          ((∑ i, p i •
              Matrix.vecMulVec
                (fun a => α i a - ∑ l, p l * α l a)
                (fun b => α i b - ∑ l, p l * α l b)) - S)} := by
  -- Keep the symmetry hypothesis in scope even though the convexity proof only needs PSD closure.
  let _ := hS
  rw [convex_iff_add_mem]
  intro p hp q hq a b ha hb hab
  -- Work with the convex combination pointwise so the simplex constraints are easy to verify.
  change
    (∀ i, 0 ≤ (fun i => a * p i + b * q i) i) ∧
      (∑ i, (fun i => a * p i + b * q i) i = 1) ∧
      Matrix.PosSemidef (covarianceMatrix α (fun i => a * p i + b * q i) - S)
  refine ⟨?_, ?_, ?_⟩
  · -- Each coordinate stays nonnegative because the convex coefficients are nonnegative.
    intro i
    exact add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i))
  · -- The convex combination of two probability vectors still has total mass `1`.
    calc
      ∑ i, (a * p i + b * q i) = a * (∑ i, p i) + b * (∑ i, q i) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
      _ = 1 := by simpa [hp.2.1, hq.2.1] using hab
  · -- Rewrite the covariance of the convex combination and use PSD closure under convex sums.
    have hcov := covariance_convexCombo_eq α p q hab hp.2.1 hq.2.1
    have hpS : Matrix.PosSemidef (a • (covarianceMatrix α p - S)) :=
      Matrix.PosSemidef.smul hp.2.2 ha
    have hqS : Matrix.PosSemidef (b • (covarianceMatrix α q - S)) :=
      Matrix.PosSemidef.smul hq.2.2 hb
    have hcorr :
        Matrix.PosSemidef
          ((a * b) •
            Matrix.vecMulVec (meanVec α p - meanVec α q) (meanVec α p - meanVec α q)) := by
      -- The correction term is rank one and therefore PSD, with a nonnegative scalar factor.
      have hbase :
          Matrix.PosSemidef
            (Matrix.vecMulVec (meanVec α p - meanVec α q) (meanVec α p - meanVec α q)) := by
        simpa using Matrix.posSemidef_vecMulVec_self_star (meanVec α p - meanVec α q)
      exact Matrix.PosSemidef.smul hbase (mul_nonneg ha hb)
    have hrewrite :
        covarianceMatrix α (fun i => a * p i + b * q i) - S =
          a • (covarianceMatrix α p - S) + b • (covarianceMatrix α q - S) +
            (a * b) • Matrix.vecMulVec (meanVec α p - meanVec α q) (meanVec α p - meanVec α q) := by
      -- Use `a + b = 1` to distribute the `-S` term across the convex combination.
      have hb' : b = 1 - a := by linarith
      rw [hcov]
      ext x y
      simp [Matrix.sub_apply, hb']
      ring
    rw [hrewrite]
    exact Matrix.PosSemidef.add (Matrix.PosSemidef.add hpS hqS) hcorr

end «problem-135»
