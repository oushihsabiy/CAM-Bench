import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-198»


/- [BLOCK Exercise 7.4-(b) | 29 | defn]
Given a parametric density or mass function p_θ and observations y₁,dots,y_N, the log-likelihood is
the function ell(θ)=sum_{i=1}^N log p_θ(yᵢ).
-/
def logLikelihood {Θ Y : Type} (p : Θ → Y → ℝ) (y : Fin N → Y) : Θ → ℝ :=
  fun θ => ∑ i : Fin N, Real.log (p θ (y i))

/- [BLOCK Exercise 7.4-(b) | 30 | defn]
A function f : X × Y → ℝ is jointly concave if for all (x₁,y₁),(x₂,y₂) ∈ X× Y and all λ∈[0,1],
f(λ x₁+(1-λ)x₂,λ y₁+(1-λ)y₂) ≥ λ f(x₁,y₁)+(1-λ)f(x₂,y₂).
-/
def JointlyConcave {X Y : Type*} [AddCommMonoid X] [Module ℝ X] [AddCommMonoid Y] [Module ℝ Y]
    (f : X × Y → ℝ) : Prop :=
  ∀ (x₁ x₂ : X) (y₁ y₂ : Y) (lam : ℝ),
    0 ≤ lam →
    lam ≤ 1 →
    f (lam • x₁ + (1 - lam) • x₂, lam • y₁ + (1 - lam) • y₂) ≥
      lam * f (x₁, y₁) + (1 - lam) * f (x₂, y₂)

/-- The coordinate quadratic form associated to a real matrix. -/
private def quadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j

/-- The coordinate quadratic form is the dot product of `x` with `A *ᵥ x`. -/
private lemma quadraticForm_eq_dotProduct_mulVec
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticForm A x = dotProduct x (A *ᵥ x) := by
  -- Expand `mulVec` and the finite dot product, then regroup the scalar products.
  simp [quadraticForm, Matrix.mulVec, dotProduct, mul_assoc, Finset.mul_sum]

/-- A real symmetric matrix is positive definite once its quadratic form is strictly positive on
nonzero vectors. -/
private lemma posDef_of_quadraticForm_pos
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hquad : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadraticForm A x) :
    A.PosDef := by
  -- Repackage the coordinate formula into the standard positive-definite quadratic criterion.
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA
  · intro x hx
    simpa [quadraticForm_eq_dotProduct_mulVec] using hquad x hx

/-- A real symmetric matrix is positive semidefinite once its quadratic form is nonnegative on
all vectors. -/
private lemma posSemidef_of_quadraticForm_nonneg
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hquad : ∀ x : Fin n → ℝ, 0 ≤ quadraticForm A x) :
    A.PosSemidef := by
  -- Repackage the coordinate formula into the standard positive-semidefinite quadratic criterion.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA
  · intro x
    simpa [quadraticForm_eq_dotProduct_mulVec] using hquad x

/-- The quadratic form is affine in the matrix argument along the specific slack
`(2 • S) - R`. -/
private lemma quadraticForm_two_smul_sub
    {n : ℕ} (S R : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticForm (((2 : ℝ) • S) - R) x = 2 * quadraticForm S x - quadraticForm R x := by
  -- Expand the quadratic form entrywise and distribute over the matrix linear combination.
  simp [quadraticForm, sub_eq_add_neg, mul_add, add_mul, mul_assoc, Finset.mul_sum,
    Finset.sum_add_distrib]
  ring_nf

/-- Transposing a real matrix does not change its coordinate quadratic form. -/
private lemma quadraticForm_transpose_eq
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticForm Aᵀ x = quadraticForm A x := by
  -- Expand the transpose entrywise and swap the finite summation order.
  unfold quadraticForm
  calc
    ∑ i : Fin n, ∑ j : Fin n, x i * Aᵀ i j * x j
        = ∑ i : Fin n, ∑ j : Fin n, x j * A j i * x i := by
            simp [Matrix.transpose_apply, mul_comm, mul_left_comm]
    _ = ∑ j : Fin n, ∑ i : Fin n, x j * A j i * x i := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := by
          simp [mul_comm, mul_left_comm]

/-- The coordinate quadratic form is additive in the matrix argument. -/
private lemma quadraticForm_add
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticForm (A + B) x = quadraticForm A x + quadraticForm B x := by
  -- Expand the matrix addition entrywise and split the two resulting finite sums.
  unfold quadraticForm
  simp [Finset.sum_add_distrib, add_mul, mul_add]

/-- The coordinate quadratic form is linear under real scalar multiplication of the matrix. -/
private lemma quadraticForm_smul
    {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticForm (c • A) x = c * quadraticForm A x := by
  -- Pull the scalar through the finite sums and regroup the scalar factors.
  unfold quadraticForm
  simp [Matrix.smul_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  ring

/-- Replacing a real matrix by its symmetric part leaves the coordinate quadratic form unchanged. -/
private lemma quadraticForm_symmPart_eq
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticForm (((1 / 2 : ℝ) • (A + Aᵀ))) x = quadraticForm A x := by
  -- Average the matrix with its transpose, then use the previous invariance lemma.
  rw [quadraticForm_smul, quadraticForm_add, quadraticForm_transpose_eq]
  ring

/-- A symmetric trace pairing only depends on the symmetric part of the second matrix. -/
private lemma trace_mul_symmPart_eq_of_isSymm
    {n : ℕ} {M A : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm) :
    Matrix.trace (M * (((1 / 2 : ℝ) • (A + Aᵀ)))) = Matrix.trace (M * A) := by
  -- Expand the trace linearly and identify the transpose contribution with the original trace.
  have htraceTranspose : Matrix.trace (M * Aᵀ) = Matrix.trace (M * A) := by
    calc
      Matrix.trace (M * Aᵀ) = Matrix.trace ((M * Aᵀ)ᵀ) := by
        rw [Matrix.trace_transpose]
      _ = Matrix.trace (A * Mᵀ) := by
        simp [Matrix.transpose_mul]
      _ = Matrix.trace (A * M) := by
        rw [hM.eq]
      _ = Matrix.trace (M * A) := by
        rw [Matrix.trace_mul_comm]
  calc
    Matrix.trace (M * (((1 / 2 : ℝ) • (A + Aᵀ))))
        = (1 / 2 : ℝ) * Matrix.trace (M * (A + Aᵀ)) := by
            rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    _ = (1 / 2 : ℝ) * (Matrix.trace (M * A) + Matrix.trace (M * Aᵀ)) := by
          simp [Matrix.mul_add, Matrix.trace_add]
    _ = Matrix.trace (M * A) := by
          rw [htraceTranspose]
          ring

/-- Applying the Hermitian functional calculus to `x ↦ 1 - t x` produces the affine matrix
perturbation `1 - t • A`. -/
private lemma Matrix.IsHermitian.cfc_one_sub_smul
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    hA.cfc (fun x => 1 - t * x) = 1 - t • A := by
  let U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  let D : Matrix n n ℝ := Matrix.diagonal hA.eigenvalues
  have hdiag :
      Matrix.diagonal ((fun x => 1 - t * x) ∘ hA.eigenvalues) = 1 - t • D := by
    -- Compute the diagonal of the pointwise affine transform entrywise.
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, hij]
  have hspectral : U * D * star U = A := by
    -- The spectral theorem diagonalizes `A` in the chosen orthonormal eigenbasis.
    simpa [U, D, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem.symm
  calc
    hA.cfc (fun x => 1 - t * x)
        = U * Matrix.diagonal ((fun x => 1 - t * x) ∘ hA.eigenvalues) * star U := by
            rfl
    _ = U * (1 - t • D) * star U := by
          rw [hdiag]
    _ = (U * (1 - t • D)) * star U := by
          rw [mul_assoc]
    _ = (U * 1 - U * (t • D)) * star U := by
          rw [mul_sub]
    _ = U * 1 * star U - (U * (t • D)) * star U := by
          rw [sub_mul]
    _ = U * 1 * star U - t • (U * D * star U) := by
          simp [mul_assoc]
    _ = 1 - t • (U * D * star U) := by
          simp [U, mul_assoc]
    _ = 1 - t • A := by
          rw [hspectral]

/-- A Hermitian affine perturbation `1 - t • A` is positive definite exactly when each shifted
eigenvalue `1 - t λᵢ` is positive. -/
private lemma Matrix.IsHermitian.one_sub_smul_posDef_iff
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    Matrix.PosDef (1 - t • A) ↔ ∀ i, 0 < 1 - t * hA.eigenvalues i := by
  rw [← Matrix.IsHermitian.cfc_one_sub_smul hA t]
  let U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  have hUunit : IsUnit U := by
    -- The eigenvector matrix is unitary, hence invertible.
    refine ⟨⟨U, star U, ?_, ?_⟩, rfl⟩ <;> simp [U]
  have hconj := (Matrix.IsUnit.posDef_star_right_conjugate_iff (U := U)
    (x := Matrix.diagonal ((fun x => 1 - t * x) ∘ hA.eigenvalues)) hUunit)
  simpa [Matrix.IsHermitian.cfc, U, Unitary.conjStarAlgAut_apply, Matrix.posDef_diagonal_iff,
    Function.comp_apply, mul_assoc] using hconj

/-- The determinant of `1 - t • A` is the product of the shifted eigenvalues of the Hermitian
matrix `A`. -/
private lemma Matrix.IsHermitian.det_one_sub_smul
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    Matrix.det (1 - t • A) = ∏ i, (1 - t * hA.eigenvalues i) := by
  rw [← Matrix.IsHermitian.cfc_one_sub_smul hA t]
  have hUnitary :
      IsUnit (↑hA.eigenvectorUnitary : Matrix n n ℝ) := Unitary.isUnit_coe
  rw [Matrix.IsHermitian.cfc]
  have hConjDet :
      Matrix.det
          (((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ)) hA.eigenvectorUnitary)
            (Matrix.diagonal (RCLike.ofReal ∘ (fun x => 1 - t * x) ∘ hA.eigenvalues))) =
        Matrix.det
          (Matrix.diagonal (RCLike.ofReal ∘ (fun x => 1 - t * x) ∘ hA.eigenvalues)) := by
    have hDetUnitary :
        Matrix.det (↑hA.eigenvectorUnitary : Matrix n n ℝ) *
            Matrix.det (star (↑hA.eigenvectorUnitary : Matrix n n ℝ)) =
          1 := by
      calc
        Matrix.det (↑hA.eigenvectorUnitary : Matrix n n ℝ) *
            Matrix.det (star (↑hA.eigenvectorUnitary : Matrix n n ℝ)) =
          Matrix.det
            ((↑hA.eigenvectorUnitary : Matrix n n ℝ) *
              star (↑hA.eigenvectorUnitary : Matrix n n ℝ)) := by
                symm
                exact Matrix.det_mul _ _
        _ = 1 := by
              simpa using congrArg Matrix.det (Unitary.coe_mul_star_self hA.eigenvectorUnitary)
    rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
    calc
      Matrix.det (↑hA.eigenvectorUnitary : Matrix n n ℝ) *
          Matrix.det (Matrix.diagonal (RCLike.ofReal ∘ (fun x => 1 - t * x) ∘ hA.eigenvalues)) *
          Matrix.det (star (↑hA.eigenvectorUnitary : Matrix n n ℝ))
        = (Matrix.det (↑hA.eigenvectorUnitary : Matrix n n ℝ) *
            Matrix.det (star (↑hA.eigenvectorUnitary : Matrix n n ℝ))) *
            Matrix.det (Matrix.diagonal (RCLike.ofReal ∘ (fun x => 1 - t * x) ∘ hA.eigenvalues)) := by
              ring
      _ = Matrix.det (Matrix.diagonal (RCLike.ofReal ∘ (fun x => 1 - t * x) ∘ hA.eigenvalues)) := by
            rw [hDetUnitary, one_mul]
  rw [hConjDet, Matrix.det_diagonal]
  simp [Function.comp_apply]

/-- The trace of a diagonal matrix times `C` reads off the weighted diagonal of `C`. -/
private lemma trace_diagonal_mul_eq_sum
    {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (C : Matrix n n ℝ) :
    Matrix.trace (Matrix.diagonal d * C) = ∑ i, d i * C i i := by
  -- Expand the diagonal matrix product entrywise; only the matching diagonal index survives.
  calc
    Matrix.trace (Matrix.diagonal d * C)
        = ∑ i, ∑ j, Matrix.diagonal d i j * C j i := by
            simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    _ = ∑ i, d i * C i i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [Matrix.diagonal]

/-- The scalar function `x ↦ log x + c / x` is convex on every interval contained in
`(0, 2 c]`. -/
private lemma log_add_div_convex_on_Icc
    {a c : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Set.Icc a (2 * c)) (fun x : ℝ => Real.log x + c * x⁻¹) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Icc a (2 * c)) ?_ ?_ ?_
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hxne : x ≠ 0 := hxpos.ne'
    exact ((Real.continuousAt_log hxne).continuousWithinAt.add
      ((continuousAt_const.mul (continuousAt_inv₀ hxne)).continuousWithinAt))
  · rw [interior_Icc]
    intro x hx
    have hxpos : 0 < x := lt_trans ha hx.1
    have hxne : x ≠ 0 := hxpos.ne'
    exact
      (HasDerivAt.differentiableAt
        ((Real.hasDerivAt_log hxne).add ((hasDerivAt_inv hxne).const_mul c))).differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    have hxpos : 0 < x := lt_trans ha hx.1
    have hypos : 0 < y := lt_trans ha hy.1
    have hxne : x ≠ 0 := hxpos.ne'
    have hyne : y ≠ 0 := hypos.ne'
    have hx2c : x ≤ 2 * c := le_of_lt hx.2
    have hy2c : y ≤ 2 * c := le_of_lt hy.2
    have hdx : deriv (fun x : ℝ => Real.log x + c * x⁻¹) x = x⁻¹ + -(c * (x ^ 2)⁻¹) := by
      simpa using (((Real.hasDerivAt_log hxne).add ((hasDerivAt_inv hxne).const_mul c)).deriv)
    have hdy : deriv (fun x : ℝ => Real.log x + c * x⁻¹) y = y⁻¹ + -(c * (y ^ 2)⁻¹) := by
      simpa using (((Real.hasDerivAt_log hyne).add ((hasDerivAt_inv hyne).const_mul c)).deriv)
    rw [hdx, hdy]
    have haux : x * y ≤ c * (x + y) := by
      nlinarith [hxpos.le, hypos.le, hx2c, hy2c]
    field_simp [hxne, hyne]
    nlinarith [haux, hxy]

/-- Jensen's inequality for `x ↦ log x + c / x` along a segment inside `(0, 2 c]`. -/
private lemma log_add_div_segment_le
    (x₀ x₁ c lam : ℝ)
    (hx₀ : 0 < x₀) (hx₁ : 0 < x₁)
    (hx₀c : x₀ ≤ 2 * c) (hx₁c : x₁ ≤ 2 * c)
    (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) :
    Real.log (lam * x₁ + (1 - lam) * x₀) + c * (lam * x₁ + (1 - lam) * x₀)⁻¹ ≤
      lam * (Real.log x₁ + c * x₁⁻¹) + (1 - lam) * (Real.log x₀ + c * x₀⁻¹) := by
  have hmin : 0 < min x₀ x₁ := lt_min hx₀ hx₁
  have hconv := log_add_div_convex_on_Icc (a := min x₀ x₁) (c := c) hmin
  have hx₀mem : x₀ ∈ Set.Icc (min x₀ x₁) (2 * c) := ⟨min_le_left _ _, hx₀c⟩
  have hx₁mem : x₁ ∈ Set.Icc (min x₀ x₁) (2 * c) := ⟨min_le_right _ _, hx₁c⟩
  simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
    sub_eq_add_neg] using
    hconv.2 hx₁mem hx₀mem hlam₀ (sub_nonneg.mpr hlam₁) (by ring)

/-- The empirical covariance expression is symmetric because each summand is a rank-one symmetric
matrix. -/
private lemma sampleCov_isSymm
    {n N : ℕ} (y : Fin N → (Fin n → ℝ)) (Ybar : Fin n → ℝ) :
    Matrix.IsSymm (fun j k =>
      (1 / (N : ℝ)) * ∑ i : Fin N, (y i j - Ybar j) * (y i k - Ybar k)) := by
  -- Swap the two coordinates and use commutativity of scalar multiplication in `ℝ`.
  ext j k
  simp [mul_comm]

/-- Any covariance upper bound `R ≼ 2 • S` with `R ≻ 0` forces `S` itself to be positive
definite. -/
private lemma sampleCov_posDef_of_covariance_region
    {n : ℕ} (S R : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm)
    (hRpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadraticForm R x)
    (hSlack : ∀ x : Fin n → ℝ, 0 ≤ quadraticForm (((2 : ℝ) • S) - R) x) :
    S.PosDef := by
  -- The slack identity `xᵀ (2S - R) x = 2 xᵀ S x - xᵀ R x` turns the feasible-region bounds into
  -- strict positivity of the quadratic form of `S`.
  refine posDef_of_quadraticForm_pos hS ?_
  intro x hx
  have hpos : 0 < quadraticForm R x := hRpos x hx
  have hnonneg : 0 ≤ quadraticForm (((2 : ℝ) • S) - R) x := hSlack x
  rw [quadraticForm_two_smul_sub] at hnonneg
  linarith

/-- A convex combination of positive-definite real matrices is positive definite. -/
private lemma posDef_convexCombination
    {n : ℕ}
    {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • X + b • Y).PosDef := by
  -- Split off the degenerate weight case so the remaining positive coefficient can scale the
  -- positive-definite endpoint.
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hY
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    exact (hX.smul ha_pos).add_posSemidef (hY.posSemidef.smul hb)

/-- The replicated-column trace identity converts the `1 × 1` Schur-complement witness into the
inverse quadratic form. -/
private lemma trace_replicateCol_mul_eq_quadraticForm
    {n : ℕ} (u : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace
        ((Matrix.replicateCol (Fin 1) u)ᵀ * M * Matrix.replicateCol (Fin 1) u) =
      quadraticForm M u := by
  -- Cycle the trace until the replicated column and row are adjacent to the matrix product.
  rw [Matrix.trace_mul_cycle (A := (Matrix.replicateCol (Fin 1) u)ᵀ)
    (B := M) (C := Matrix.replicateCol (Fin 1) u)]
  rw [Matrix.trace_mul_cycle (A := Matrix.replicateCol (Fin 1) u)
    (B := (Matrix.replicateCol (Fin 1) u)ᵀ) (C := M)]
  -- Rewrite the rank-one trace as the corresponding dot product.
  rw [← Matrix.replicateCol_mulVec, Matrix.transpose_replicateCol]
  simpa [quadraticForm_eq_dotProduct_mulVec, dotProduct_comm] using
    (Matrix.trace_replicateCol_mul_replicateRow
      (ι := Fin 1) (a := M.mulVec u) (b := u))

/-- The inverse quadratic form is jointly convex in the positive-definite matrix and vector
arguments. -/
private lemma quadraticForm_inv_convexCombination_le
    {n : ℕ}
    (u₁ u₂ : Fin n → ℝ)
    {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    quadraticForm ((a • X + b • Y)⁻¹) (a • u₁ + b • u₂) ≤
      a * quadraticForm X⁻¹ u₁ + b * quadraticForm Y⁻¹ u₂ := by
  let B₁ : Matrix (Fin n) (Fin 1) ℝ := Matrix.replicateCol (Fin 1) u₁
  let B₂ : Matrix (Fin n) (Fin 1) ℝ := Matrix.replicateCol (Fin 1) u₂
  let S₁ : Matrix (Fin 1) (Fin 1) ℝ := B₁ᵀ * X⁻¹ * B₁
  let S₂ : Matrix (Fin 1) (Fin 1) ℝ := B₂ᵀ * Y⁻¹ * B₂
  let Aθ : Matrix (Fin n) (Fin n) ℝ := a • X + b • Y
  let Bθ : Matrix (Fin n) (Fin 1) ℝ := a • B₁ + b • B₂
  let Sθ : Matrix (Fin 1) (Fin 1) ℝ := a • S₁ + b • S₂
  have hAθ : Aθ.PosDef := by
    -- The averaged leading block stays positive definite, so the Schur complement remains valid.
    simpa [Aθ] using posDef_convexCombination hX hY ha hb hab
  have hSchur₁ : (S₁ - B₁ᵀ * X⁻¹ * B₁).PosSemidef := by
    -- The endpoint witness has zero Schur complement by construction.
    simpa [S₁] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef)
  have hSchur₂ : (S₂ - B₂ᵀ * Y⁻¹ * B₂).PosSemidef := by
    -- The second endpoint satisfies the same exact witness identity.
    simpa [S₂] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef)
  have hBlock₁ : (Matrix.fromBlocks X B₁ B₁ᵀ S₁).PosSemidef := by
    -- Package the first endpoint as a block positive-semidefinite witness.
    letI : Invertible X := hX.isUnit.invertible
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosDef.fromBlocks₁₁ (A := X) B₁ S₁ hX).mpr hSchur₁
  have hBlock₂ : (Matrix.fromBlocks Y B₂ B₂ᵀ S₂).PosSemidef := by
    -- The same Schur-complement argument applies to the second endpoint.
    letI : Invertible Y := hY.isUnit.invertible
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosDef.fromBlocks₁₁ (A := Y) B₂ S₂ hY).mpr hSchur₂
  have hBlockθ : (Matrix.fromBlocks Aθ Bθ Bθᵀ Sθ).PosSemidef := by
    -- Positive-semidefinite block witnesses are stable under convex combinations.
    have hScaled₁ : (a • Matrix.fromBlocks X B₁ B₁ᵀ S₁).PosSemidef := hBlock₁.smul ha
    have hScaled₂ : (b • Matrix.fromBlocks Y B₂ B₂ᵀ S₂).PosSemidef := hBlock₂.smul hb
    simpa [Aθ, Bθ, Sθ, Matrix.fromBlocks_smul, Matrix.fromBlocks_add, Matrix.transpose_smul,
      Matrix.transpose_add] using hScaled₁.add hScaled₂
  have hSchurθ : (Sθ - Bθᵀ * Aθ⁻¹ * Bθ).PosSemidef := by
    -- The averaged feasible block matrix yields the mixed Schur-complement slack.
    letI : Invertible Aθ := hAθ.isUnit.invertible
    have hSchur :=
      (Matrix.PosDef.fromBlocks₁₁ (A := Aθ) Bθ Sθ hAθ).mp <|
        by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hBlockθ
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hSchur
  have hTraceNonneg : 0 ≤ Matrix.trace (Sθ - Bθᵀ * Aθ⁻¹ * Bθ) := by
    -- Taking traces preserves nonnegativity on positive-semidefinite matrices.
    exact Matrix.PosSemidef.trace_nonneg hSchurθ
  have hTraceLe :
      Matrix.trace (Bθᵀ * Aθ⁻¹ * Bθ) ≤ Matrix.trace Sθ := by
    -- Expanding the trace of the Schur-complement slack gives the desired scalar inequality.
    rw [Matrix.trace_sub] at hTraceNonneg
    linarith
  have hTraceLe' :
      Matrix.trace (Bθᵀ * Aθ⁻¹ * Bθ) ≤
        a * Matrix.trace (B₁ᵀ * X⁻¹ * B₁) + b * Matrix.trace (B₂ᵀ * Y⁻¹ * B₂) := by
    -- The `1 × 1` witness trace is linear in the convex combination.
    simpa [Sθ, S₁, S₂, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, mul_add, add_mul,
      mul_assoc, mul_left_comm, mul_comm] using hTraceLe
  have hAθ :
      Matrix.trace (Bθᵀ * Aθ⁻¹ * Bθ) = quadraticForm Aθ⁻¹ (a • u₁ + b • u₂) := by
    -- Unpack the replicated-column witness back into the coordinate quadratic form.
    simpa [Bθ, B₁, B₂, Aθ, Matrix.replicateCol_add, Matrix.replicateCol_smul] using
      trace_replicateCol_mul_eq_quadraticForm (a • u₁ + b • u₂) Aθ⁻¹
  have hXtrace :
      Matrix.trace (B₁ᵀ * X⁻¹ * B₁) = quadraticForm X⁻¹ u₁ := by
    -- The first endpoint trace matches the original quadratic form.
    simpa [B₁] using trace_replicateCol_mul_eq_quadraticForm u₁ X⁻¹
  have hYtrace :
      Matrix.trace (B₂ᵀ * Y⁻¹ * B₂) = quadraticForm Y⁻¹ u₂ := by
    -- The second endpoint trace matches the same quadratic form.
    simpa [B₂] using trace_replicateCol_mul_eq_quadraticForm u₂ Y⁻¹
  rw [hAθ, hXtrace, hYtrace] at hTraceLe'
  simpa [Aθ]
    using hTraceLe'

/-- The centered residuals around the empirical mean sum to zero in each coordinate. -/
private lemma centered_residual_sum_eq_zero
    {n N : ℕ} (hN : 0 < N) (y : Fin N → (Fin n → ℝ)) (j : Fin n) :
    ∑ i : Fin N, (y i j - ((1 / (N : ℝ)) * ∑ k : Fin N, y k j)) = 0 := by
  -- Expand the empirical mean and use `N * (1 / N) = 1` because `N > 0`.
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  let S : ℝ := ∑ k : Fin N, y k j
  calc
    ∑ i : Fin N, (y i j - ((1 / (N : ℝ)) * ∑ k : Fin N, y k j))
        = S - ∑ _i : Fin N, (1 / (N : ℝ)) * S := by
          simp [S, Finset.sum_sub_distrib]
    _ = S - (N : ℝ) * ((1 / (N : ℝ)) * S) := by simp
    _ = S - S := by
          field_simp [hN0]
    _ = 0 := by ring

/-- Expanding the quadratic form of a difference isolates the two mixed terms. -/
private lemma quadraticForm_sub
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    quadraticForm A (u - v) =
      quadraticForm A u
        - (∑ i : Fin n, ∑ j : Fin n, u i * A i j * v j)
        - (∑ i : Fin n, ∑ j : Fin n, v i * A i j * u j)
        + quadraticForm A v := by
  -- Expand the quadratic form entrywise and collect the four bilinear pieces.
  simp [quadraticForm, sub_eq_add_neg, mul_add, add_mul, Finset.sum_add_distrib]
  ring_nf

/-- Translating a centered family of vectors changes the total quadratic energy only by the common
shift term. -/
private lemma sum_quadraticForm_sub_eq
    {n N : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin N → (Fin n → ℝ)) (v : Fin n → ℝ)
    (hu : ∀ j : Fin n, ∑ t : Fin N, u t j = 0) :
    ∑ t : Fin N, quadraticForm A (u t - v) =
      ∑ t : Fin N, quadraticForm A (u t) + (N : ℝ) * quadraticForm A v := by
  -- The two mixed sums vanish because each coordinate of the family `u` is centered.
  have hCrossLeft :
      ∑ t : Fin N, ∑ i : Fin n, ∑ j : Fin n, u t i * A i j * v j = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero ?_
    intro j hj
    calc
      ∑ t : Fin N, u t i * A i j * v j = ∑ t : Fin N, v j * (A i j * u t i) := by
        refine Finset.sum_congr rfl ?_
        intro t ht
        ring
      _ = v j * ∑ t : Fin N, A i j * u t i := by
        rw [Finset.mul_sum]
      _ = v j * ((A i j) * ∑ t : Fin N, u t i) := by
        congr 1
        rw [Finset.mul_sum]
      _ = 0 := by simp [hu i]
  have hCrossRight :
      ∑ t : Fin N, ∑ i : Fin n, ∑ j : Fin n, v i * A i j * u t j = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero ?_
    intro j hj
    calc
      ∑ t : Fin N, v i * A i j * u t j = ∑ t : Fin N, (v i * A i j) * u t j := by
        refine Finset.sum_congr rfl ?_
        intro t ht
        ring
      _ = (v i * A i j) * (∑ t : Fin N, u t j) := by
        rw [Finset.mul_sum]
      _ = 0 := by simp [hu j]
  have hConst :
      ∑ t : Fin N, quadraticForm A v = (N : ℝ) * quadraticForm A v := by
    simp
  calc
    ∑ t : Fin N, quadraticForm A (u t - v)
        = ∑ t : Fin N,
            (quadraticForm A (u t)
              - (∑ i : Fin n, ∑ j : Fin n, u t i * A i j * v j)
              - (∑ i : Fin n, ∑ j : Fin n, v i * A i j * u t j)
              + quadraticForm A v) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          simpa using quadraticForm_sub A (u t) v
    _ = (∑ t : Fin N, quadraticForm A (u t))
          - (∑ t : Fin N, ∑ i : Fin n, ∑ j : Fin n, u t i * A i j * v j)
          - (∑ t : Fin N, ∑ i : Fin n, ∑ j : Fin n, v i * A i j * u t j)
          + (∑ t : Fin N, quadraticForm A v) := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ t : Fin N, quadraticForm A (u t) + (N : ℝ) * quadraticForm A v := by
          rw [hCrossLeft, hCrossRight, hConst]
          ring

/-- Taking logs of the Gaussian density isolates the determinant and quadratic-form pieces. -/
private lemma gaussian_log_density_decomposition
    {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (a z : Fin n → ℝ) (hR : R.PosDef) :
    Real.log
        (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
          Real.sqrt (Matrix.det R)⁻¹ *
          Real.exp (-((quadraticForm R⁻¹ (fun i => z i - a i)) / 2))) =
      Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) -
        quadraticForm R⁻¹ (fun i => z i - a i) / 2 := by
  -- Route correction: isolate the pointwise Gaussian logarithm first, instead of trying to expand
  -- the whole likelihood and the covariance branch simultaneously.
  have hConstPos : 0 < Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) := by
    apply Real.rpow_pos_of_pos
    positivity
  have hDetPos : 0 < Matrix.det R := hR.det_pos
  have hDetInvPos : 0 < (Matrix.det R)⁻¹ := by positivity
  have hSqrtPos : 0 < Real.sqrt ((Matrix.det R)⁻¹) := Real.sqrt_pos.2 hDetInvPos
  have hAssoc :
      Real.log
          (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
            Real.sqrt (Matrix.det R)⁻¹ *
            Real.exp (-((quadraticForm R⁻¹ (fun i => z i - a i)) / 2))) =
        Real.log
          (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
            (Real.sqrt (Matrix.det R)⁻¹ *
              Real.exp (-((quadraticForm R⁻¹ (fun i => z i - a i)) / 2)))) := by
    congr 1
    ring
  have hLogOuter :
      Real.log
          (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
            (Real.sqrt (Matrix.det R)⁻¹ *
              Real.exp (-((quadraticForm R⁻¹ (fun i => z i - a i)) / 2)))) =
        Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) +
          Real.log
            (Real.sqrt (Matrix.det R)⁻¹ *
              Real.exp (-((quadraticForm R⁻¹ (fun i => z i - a i)) / 2))) := by
    simpa using
      (Real.log_mul hConstPos.ne' (mul_ne_zero hSqrtPos.ne' (by simp)))
  have hLogInner :
      Real.log
          (Real.sqrt (Matrix.det R)⁻¹ *
            Real.exp (-((quadraticForm R⁻¹ (fun i => z i - a i)) / 2))) =
        Real.log (Real.sqrt (Matrix.det R)⁻¹) +
          Real.log (Real.exp (-((quadraticForm R⁻¹ (fun i => z i - a i)) / 2))) := by
    simpa using
      (Real.log_mul hSqrtPos.ne' (by simp) :
        Real.log
            (Real.sqrt (Matrix.det R)⁻¹ *
              Real.exp (-((quadraticForm R⁻¹ (fun i => z i - a i)) / 2))) =
          Real.log (Real.sqrt (Matrix.det R)⁻¹) +
            Real.log (Real.exp (-((quadraticForm R⁻¹ (fun i => z i - a i)) / 2))))
  have hLogBase :
      Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) =
        Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) +
          Real.log (Real.sqrt (Matrix.det R)⁻¹) := by
    simpa using
      (Real.log_mul hConstPos.ne' hSqrtPos.ne' :
        Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) =
          Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) +
            Real.log (Real.sqrt (Matrix.det R)⁻¹))
  have hLogSqrtInv :
      Real.log (Real.sqrt (Matrix.det R)⁻¹) = Real.log (Matrix.det R) * (-1 / 2 : ℝ) := by
    rw [Real.log_sqrt hDetInvPos.le, Real.log_inv]
    ring
  rw [hAssoc, hLogOuter, hLogInner, Real.log_exp, hLogBase, hLogSqrtInv]
  ring

/-- The Gaussian log-likelihood splits into a covariance-only branch and a centered mean quadratic
term. -/
private lemma gaussian_logLikelihood_centered_decomposition
    {n N : ℕ}
    (hN : 0 < N)
    (y : Fin N → (Fin n → ℝ))
    (Ybar : Fin n → ℝ)
    (hYbar : Ybar = fun j => (1 / (N : ℝ)) * ∑ i : Fin N, y i j)
    (R : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ)
    (hR : R.PosDef) :
    let p : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) → (Fin n → ℝ) → ℝ :=
      fun θ z =>
        Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
          Real.sqrt (Matrix.det θ.1)⁻¹ *
          Real.exp (-((quadraticForm θ.1⁻¹ (fun i => z i - θ.2 i)) / 2))
    let l : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) → ℝ := logLikelihood p y
    l (R, a) =
      (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) -
        (1 / 2 : ℝ) * ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j) -
        ((N : ℝ) / 2) * quadraticForm R⁻¹ (fun j => a j - Ybar j) := by
  -- First decompose the translated quadratic energies into centered residuals plus the mean shift.
  have hCentered :
      ∀ j : Fin n, ∑ t : Fin N, (fun s => y s j - Ybar j) t = 0 := by
    intro j
    rw [hYbar]
    simpa using centered_residual_sum_eq_zero hN y j
  have hShift :
      ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - a j) =
        ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j) +
          (N : ℝ) * quadraticForm R⁻¹ (fun j => a j - Ybar j) := by
    calc
      ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - a j)
          = ∑ t : Fin N, quadraticForm R⁻¹ ((fun j => y t j - Ybar j) - fun j => a j - Ybar j) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              have hArg :
                  ((fun j => y t j - Ybar j) - fun j => a j - Ybar j) = (fun j => y t j - a j) := by
                funext j
                simp [Pi.sub_apply]
              rw [hArg]
      _ = ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j) +
            (N : ℝ) * quadraticForm R⁻¹ (fun j => a j - Ybar j) := by
              simpa using
                sum_quadraticForm_sub_eq
                  (A := R⁻¹)
                  (u := fun t => fun j => y t j - Ybar j)
                  (v := fun j => a j - Ybar j)
                  hCentered
  -- Then sum the pointwise Gaussian log decomposition over the sample.
  dsimp [logLikelihood]
  calc
    ∑ i : Fin N,
        Real.log
          (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
            Real.sqrt (Matrix.det R)⁻¹ *
            Real.exp (-((quadraticForm R⁻¹ (fun j => y i j - a j)) / 2))) =
      ∑ i : Fin N,
        (Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) -
          quadraticForm R⁻¹ (fun j => y i j - a j) / 2) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using gaussian_log_density_decomposition R a (y i) hR
    _ = ∑ i : Fin N, Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) -
          ∑ i : Fin N, quadraticForm R⁻¹ (fun j => y i j - a j) / 2 := by
          rw [Finset.sum_sub_distrib]
    _ = (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) -
          (1 / 2 : ℝ) * ∑ i : Fin N, quadraticForm R⁻¹ (fun j => y i j - a j) := by
          have hHalf :
              ∑ i : Fin N, quadraticForm R⁻¹ (fun j => y i j - a j) / 2 =
                (1 / 2 : ℝ) * ∑ i : Fin N, quadraticForm R⁻¹ (fun j => y i j - a j) := by
            calc
              ∑ i : Fin N, quadraticForm R⁻¹ (fun j => y i j - a j) / 2 =
                  ∑ i : Fin N, (1 / 2 : ℝ) * quadraticForm R⁻¹ (fun j => y i j - a j) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
              _ = (1 / 2 : ℝ) * ∑ i : Fin N, quadraticForm R⁻¹ (fun j => y i j - a j) := by
                    rw [Finset.mul_sum]
          rw [hHalf]
          simp
    _ = (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) -
          (1 / 2 : ℝ) *
            (∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j) +
              (N : ℝ) * quadraticForm R⁻¹ (fun j => a j - Ybar j)) := by
          rw [hShift]
    _ = (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) -
          (1 / 2 : ℝ) * ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j) -
          ((N : ℝ) / 2) * quadraticForm R⁻¹ (fun j => a j - Ybar j) := by
          ring

/-- The centered quadratic residual sum is the trace pairing of `R⁻¹` with the empirical
covariance matrix. -/
private lemma gaussian_centered_quadratic_sum_eq_trace_sampleCov
    {n N : ℕ}
    (hN : 0 < N)
    (y : Fin N → (Fin n → ℝ))
    (Ybar : Fin n → ℝ)
    (sampleCov : Matrix (Fin n) (Fin n) ℝ)
    (hSampleCov : sampleCov = fun j k =>
      (1 / (N : ℝ)) * ∑ i : Fin N, (y i j - Ybar j) * (y i k - Ybar k))
    (R : Matrix (Fin n) (Fin n) ℝ) :
    ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j) =
      (N : ℝ) * Matrix.trace (R⁻¹ * sampleCov) := by
  -- Replace `sampleCov` by its empirical definition and expand the trace of the matrix product.
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  let S : Matrix (Fin n) (Fin n) ℝ := fun j k =>
    (1 / (N : ℝ)) * ∑ i : Fin N, (y i j - Ybar j) * (y i k - Ybar k)
  have hS : sampleCov = S := by
    simpa [S] using hSampleCov
  calc
    ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j)
        = ∑ t : Fin N, ∑ j : Fin n, ∑ k : Fin n,
            (y t j - Ybar j) * (R⁻¹) j k * (y t k - Ybar k) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            simp [quadraticForm]
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ t : Fin N,
          (R⁻¹) j k * ((y t j - Ybar j) * (y t k - Ybar k)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro k hk
          refine Finset.sum_congr rfl ?_
          intro t ht
          ring
    _ = ∑ j : Fin n, ∑ k : Fin n, (R⁻¹) j k *
          (∑ t : Fin N, (y t j - Ybar j) * (y t k - Ybar k)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [← Finset.mul_sum]
    _ = (N : ℝ) * Matrix.trace (R⁻¹ * S) := by
          simp [S, Matrix.trace, Matrix.mul_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro k hk
          refine Finset.sum_congr rfl ?_
          intro t ht
          field_simp [hN0]
    _ = (N : ℝ) * Matrix.trace (R⁻¹ * sampleCov) := by
          rw [hS]

-- The remaining blocker is the covariance-only concavity inequality after the centered mean term
-- has been peeled off.

/-- The Gaussian normalization factor is an affine constant minus one half of `log det R`. -/
private lemma gaussian_normalization_log_eq_const_sub_half_log_det
    {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.PosDef) :
    Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) =
      Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) - Real.log (Matrix.det R) / 2 := by
  -- Split the logarithm into the fixed Gaussian constant and the determinant-dependent factor.
  have hConstPos : 0 < Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) := by
    apply Real.rpow_pos_of_pos
    positivity
  have hDetPos : 0 < Matrix.det R := hR.det_pos
  have hDetInvPos : 0 < (Matrix.det R)⁻¹ := by
    positivity
  have hSqrtPos : 0 < Real.sqrt ((Matrix.det R)⁻¹) := Real.sqrt_pos.2 hDetInvPos
  have hLogMul :
      Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) =
        Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) +
          Real.log (Real.sqrt (Matrix.det R)⁻¹) := by
    simpa using
      (Real.log_mul hConstPos.ne' hSqrtPos.ne' :
        Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) =
          Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) +
            Real.log (Real.sqrt (Matrix.det R)⁻¹))
  have hLogSqrtInv :
      Real.log (Real.sqrt (Matrix.det R)⁻¹) = Real.log (Matrix.det R) * (-1 / 2 : ℝ) := by
    -- Convert the square-root inverse term into the expected `-(1/2) log det R` contribution.
    rw [Real.log_sqrt hDetInvPos.le, Real.log_inv]
    ring
  rw [hLogMul, hLogSqrtInv]
  ring

/-- Rewriting the centered quadratic sum turns the covariance branch into a constant minus the
standard `log det + trace` covariance objective. -/
private lemma gaussian_covariance_branch_rewrite
    {n N : ℕ}
    (hN : 0 < N)
    (y : Fin N → (Fin n → ℝ))
    (Ybar : Fin n → ℝ)
    (sampleCov : Matrix (Fin n) (Fin n) ℝ)
    (hSampleCov : sampleCov = fun j k =>
      (1 / (N : ℝ)) * ∑ i : Fin N, (y i j - Ybar j) * (y i k - Ybar k))
    (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.PosDef) :
    (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) -
      (1 / 2 : ℝ) * ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j) =
      (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
        ((N : ℝ) / 2) *
          (Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * sampleCov)) := by
  -- First rewrite the quadratic residual sum as the trace pairing with the empirical covariance.
  have hCentered :
      ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j) =
        (N : ℝ) * Matrix.trace (R⁻¹ * sampleCov) := by
    simpa using
      gaussian_centered_quadratic_sum_eq_trace_sampleCov hN y Ybar sampleCov hSampleCov R
  have hLog :
      Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) =
        Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) - Real.log (Matrix.det R) / 2 := by
    -- Then separate the Gaussian normalization constant from the determinant term.
    simpa using gaussian_normalization_log_eq_const_sub_half_log_det hR
  rw [hCentered, hLog]
  ring

/-- Convexity of the covariance objective `log det R + trace (R⁻¹ * S)` is the last matrix
ingredient needed for the Gaussian covariance branch. -/
private lemma log_det_add_trace_inv_convex_on_covariance_region
    {n : ℕ}
    (sampleCov R₁ R₂ : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ)
    (hR₁symm : R₁.IsSymm)
    (hR₂symm : R₂.IsSymm)
    (hR₁pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadraticForm R₁ x)
    (hR₂pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadraticForm R₂ x)
    (hSlack₁ : ∀ x : Fin n → ℝ, 0 ≤ quadraticForm (((2 : ℝ) • sampleCov) - R₁) x)
    (hSlack₂ : ∀ x : Fin n → ℝ, 0 ≤ quadraticForm (((2 : ℝ) • sampleCov) - R₂) x)
    (hlam₀ : 0 ≤ lam)
    (hlam₁ : lam ≤ 1) :
    Real.log (Matrix.det (lam • R₁ + (1 - lam) • R₂)) +
      Matrix.trace (((lam • R₁ + (1 - lam) • R₂)⁻¹) * sampleCov) ≤
        lam * (Real.log (Matrix.det R₁) + Matrix.trace (R₁⁻¹ * sampleCov)) +
          (1 - lam) * (Real.log (Matrix.det R₂) + Matrix.trace (R₂⁻¹ * sampleCov)) :=
  -- Route correction: the workable route is to replace `sampleCov` by its symmetric part, factor
  -- `R₂ = Bᵀ * B`, rewrite the whole segment as `Bᵀ * (1 - lam • Δ) * B`, diagonalize the single
  -- symmetric matrix `Δ`, and reduce the target to the scalar convexity of
  -- `x ↦ Real.log x + c / x` on `0 < x ≤ 2 * c`.
  -- TODO: finish the normalized trace rewrite
  -- `trace (((1 - lam • Δ)⁻¹) * C) = ∑ i, c i / (1 - lam * μ i)` and then apply the scalar
  -- convexity lemma termwise using the diagonal bounds extracted from the two slack hypotheses.
  sorry

private lemma gaussian_covariance_branch_concave_on_covariance_region
    {n N : ℕ}
    (hN : 0 < N)
    (y : Fin N → (Fin n → ℝ))
    (Ybar : Fin n → ℝ)
    (_hYbar : Ybar = fun j => (1 / (N : ℝ)) * ∑ i : Fin N, y i j)
    (sampleCov : Matrix (Fin n) (Fin n) ℝ)
    (hSampleCov : sampleCov = fun j k =>
      (1 / (N : ℝ)) * ∑ i : Fin N, (y i j - Ybar j) * (y i k - Ybar k))
    (R₁ R₂ : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ)
    (hR₁symm : R₁.IsSymm)
    (hR₂symm : R₂.IsSymm)
    (hR₁pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadraticForm R₁ x)
    (hR₂pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadraticForm R₂ x)
    (hSlack₁ : ∀ x : Fin n → ℝ, 0 ≤ quadraticForm (((2 : ℝ) • sampleCov) - R₁) x)
    (hSlack₂ : ∀ x : Fin n → ℝ, 0 ≤ quadraticForm (((2 : ℝ) • sampleCov) - R₂) x)
    (hlam₀ : 0 ≤ lam)
    (hlam₁ : lam ≤ 1) :
    let covarianceBranch : Matrix (Fin n) (Fin n) ℝ → ℝ :=
      fun R =>
        (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) -
          (1 / 2 : ℝ) * ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j)
    covarianceBranch (lam • R₁ + (1 - lam) • R₂) ≥
      lam * covarianceBranch R₁ + (1 - lam) * covarianceBranch R₂ := by
  -- Route correction: the Gaussian-specific algebra is now discharged first, so only the pure
  -- matrix convexity statement for `log det + trace (R⁻¹ * sampleCov)` remains.
  have hR₁pd : R₁.PosDef := by
    -- Promote the first endpoint from the quadratic-form assumption to `PosDef`.
    exact posDef_of_quadraticForm_pos hR₁symm hR₁pos
  have hR₂pd : R₂.PosDef := by
    -- Do the same for the second endpoint.
    exact posDef_of_quadraticForm_pos hR₂symm hR₂pos
  have hComboPd : (lam • R₁ + (1 - lam) • R₂).PosDef := by
    -- Positive definiteness is preserved along the affine segment of endpoints.
    have hWeights : lam + (1 - lam) = 1 := by ring
    simpa using
      posDef_convexCombination hR₁pd hR₂pd hlam₀ (sub_nonneg.mpr hlam₁) hWeights
  let covarianceBranch : Matrix (Fin n) (Fin n) ℝ → ℝ :=
    fun R =>
      (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) -
        (1 / 2 : ℝ) * ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j)
  let normalizationConst : ℝ :=
    (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2))
  let covarianceObjective : Matrix (Fin n) (Fin n) ℝ → ℝ :=
    fun R => Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * sampleCov)
  have hBranchR₁ :
      covarianceBranch R₁ =
        normalizationConst - ((N : ℝ) / 2) * covarianceObjective R₁ := by
    -- Rewrite the first endpoint branch into the normalized covariance objective.
    simpa [covarianceBranch, normalizationConst, covarianceObjective] using
      gaussian_covariance_branch_rewrite hN y Ybar sampleCov hSampleCov R₁ hR₁pd
  have hBranchR₂ :
      covarianceBranch R₂ =
        normalizationConst - ((N : ℝ) / 2) * covarianceObjective R₂ := by
    -- The second endpoint has the same covariance-objective form.
    simpa [covarianceBranch, normalizationConst, covarianceObjective] using
      gaussian_covariance_branch_rewrite hN y Ybar sampleCov hSampleCov R₂ hR₂pd
  have hBranchCombo :
      covarianceBranch (lam • R₁ + (1 - lam) • R₂) =
        normalizationConst - ((N : ℝ) / 2) *
          covarianceObjective (lam • R₁ + (1 - lam) • R₂) := by
    -- The affine combination rewrites identically once its positive definiteness is known.
    simpa [covarianceBranch, normalizationConst, covarianceObjective] using
      gaussian_covariance_branch_rewrite
        hN y Ybar sampleCov hSampleCov (lam • R₁ + (1 - lam) • R₂) hComboPd
  have hObjectiveConvex :
      covarianceObjective (lam • R₁ + (1 - lam) • R₂) ≤
        lam * covarianceObjective R₁ + (1 - lam) * covarianceObjective R₂ := by
    -- This is the remaining analytic input: convexity of `log det + trace (R⁻¹ * sampleCov)`.
    simpa [covarianceObjective] using
      log_det_add_trace_inv_convex_on_covariance_region
        sampleCov R₁ R₂ lam hR₁symm hR₂symm hR₁pos hR₂pos hSlack₁ hSlack₂ hlam₀ hlam₁
  have hCoeff : 0 ≤ (N : ℝ) / 2 := by
    positivity
  calc
    covarianceBranch (lam • R₁ + (1 - lam) • R₂)
        = normalizationConst - ((N : ℝ) / 2) *
            covarianceObjective (lam • R₁ + (1 - lam) • R₂) := hBranchCombo
    _ ≥ normalizationConst - ((N : ℝ) / 2) *
          (lam * covarianceObjective R₁ + (1 - lam) * covarianceObjective R₂) := by
          -- Multiplying the convexity inequality by the negative coefficient flips the order.
          nlinarith
    _ = lam * covarianceBranch R₁ + (1 - lam) * covarianceBranch R₂ := by
          rw [hBranchR₁, hBranchR₂]
          ring

/- [BLOCK Exercise 7.4-(b) | 31 | thm]
Let p_{R,a}(y)=(2π)^{-n/2}det(R)^{-1/2}exp≤ft(-(1)/(2)(y-a)ᵀ R^{-1}(y-a)), where y,a∈ ℝ^n and R∈
ℝ^{n×n} is symmetric positive definite. Let y₁,ldots,y_N∈ ℝ^n be independent samples from this
distribution, and define the log-likelihood l(R,a)=sum_{i=1}^N log p_{R,a}(yᵢ). Let bar
y=(1)/(N)sum_{i=1}^N yᵢ and Y=(1)/(N)sum_{i=1}^N (y_{i-bar} y)(y_{i-bar} y)ᵀ. For symmetric matrices
A,B, write Apreceq B if B-A is positive semidefinite. Show that l is jointly concave ∈ ℝ and a over
the region Rpreceq 2Y.
-/
theorem gaussian_logLikelihood_jointly_concave_on_covariance_region
    {n N : ℕ}
    (hN : 0 < N)
    (y : Fin N → (Fin n → ℝ)) :
    let p : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) → (Fin n → ℝ) → ℝ :=
      fun θ z =>
        Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
          Real.sqrt (Matrix.det θ.1)⁻¹ *
          Real.exp
            (-((∑ i : Fin n, ∑ j : Fin n, (z i - θ.2 i) * ((θ.1)⁻¹ i j) * (z j - θ.2 j)) / 2))
    let l : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) → ℝ :=
      logLikelihood p y
    let Ybar : Fin n → ℝ :=
      fun j => (1 / (N : ℝ)) * ∑ i : Fin N, y i j
    let sampleCov : Matrix (Fin n) (Fin n) ℝ :=
      fun j k =>
        (1 / (N : ℝ)) * ∑ i : Fin N, (y i j - Ybar j) * (y i k - Ybar k)
    ∀ (R₁ R₂ : Matrix (Fin n) (Fin n) ℝ) (a₁ a₂ : Fin n → ℝ) (lam : ℝ),
      R₁.IsSymm →
      R₂.IsSymm →
      (∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ i : Fin n, ∑ j : Fin n, x i * R₁ i j * x j) →
      (∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ i : Fin n, ∑ j : Fin n, x i * R₂ i j * x j) →
      (∀ x : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * ((2 : ℝ) • sampleCov - R₁) i j * x j) →
      (∀ x : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * ((2 : ℝ) • sampleCov - R₂) i j * x j) →
      0 ≤ lam →
      lam ≤ 1 →
      l (lam • R₁ + (1 - lam) • R₂, lam • a₁ + (1 - lam) • a₂) ≥
        lam * l (R₁, a₁) + (1 - lam) * l (R₂, a₂) := by
  classical
  dsimp
  intro R₁ R₂ a₁ a₂ lam hR₁symm hR₂symm hR₁pos hR₂pos hSlack₁ hSlack₂ hlam₀ hlam₁
  let p : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) → (Fin n → ℝ) → ℝ :=
    fun θ z =>
      Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
        Real.sqrt (Matrix.det θ.1)⁻¹ *
        Real.exp
          (-((quadraticForm θ.1⁻¹ (fun i => z i - θ.2 i)) / 2))
  let l : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) → ℝ := logLikelihood p y
  let Ybar : Fin n → ℝ := fun j => (1 / (N : ℝ)) * ∑ i : Fin N, y i j
  let sampleCov : Matrix (Fin n) (Fin n) ℝ := fun j k =>
    (1 / (N : ℝ)) * ∑ i : Fin N, (y i j - Ybar j) * (y i k - Ybar k)
  change l (lam • R₁ + (1 - lam) • R₂, lam • a₁ + (1 - lam) • a₂) ≥
      lam * l (R₁, a₁) + (1 - lam) * l (R₂, a₂)
  have hSampleCovSymm : sampleCov.IsSymm := by
    -- The empirical covariance matrix is symmetric entrywise.
    simpa [sampleCov, Ybar] using sampleCov_isSymm y Ybar
  have hR₁pd : R₁.PosDef := by
    -- Repackage the first endpoint positivity assumption as a standard `PosDef` fact.
    refine posDef_of_quadraticForm_pos hR₁symm ?_
    intro x hx
    simpa [quadraticForm] using hR₁pos x hx
  have hR₂pd : R₂.PosDef := by
    -- The same quadratic-form criterion gives positive definiteness of the second endpoint.
    refine posDef_of_quadraticForm_pos hR₂symm ?_
    intro x hx
    simpa [quadraticForm] using hR₂pos x hx
  have hCenteredConvex :
      quadraticForm ((lam • R₁ + (1 - lam) • R₂)⁻¹)
          (lam • (fun i => a₁ i - Ybar i) + (1 - lam) • (fun i => a₂ i - Ybar i)) ≤
        lam * quadraticForm R₁⁻¹ (fun i => a₁ i - Ybar i) +
          (1 - lam) * quadraticForm R₂⁻¹ (fun i => a₂ i - Ybar i) := by
    -- This is the matrix-fractional Jensen inequality for the centered mean variables.
    have hab : lam + (1 - lam) = 1 := by ring
    simpa using
      quadraticForm_inv_convexCombination_le
        (u₁ := fun i => a₁ i - Ybar i) (u₂ := fun i => a₂ i - Ybar i)
        hR₁pd hR₂pd hlam₀ (sub_nonneg.mpr hlam₁) hab
  have hCenterCombo :
      (fun i => (lam • a₁ + (1 - lam) • a₂) i - Ybar i) =
        lam • (fun i => a₁ i - Ybar i) + (1 - lam) • (fun i => a₂ i - Ybar i) := by
    -- Rewrite the averaged mean parameter into the centered form required by the Jensen inequality.
    funext i
    simp [Pi.smul_apply]
    ring
  let covarianceBranch : Matrix (Fin n) (Fin n) ℝ → ℝ :=
    fun R =>
      (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) * Real.sqrt (Matrix.det R)⁻¹) -
        (1 / 2 : ℝ) * ∑ t : Fin N, quadraticForm R⁻¹ (fun j => y t j - Ybar j)
  have hCovarianceBranch :
      covarianceBranch (lam • R₁ + (1 - lam) • R₂) ≥
        lam * covarianceBranch R₁ + (1 - lam) * covarianceBranch R₂ := by
    -- Route correction: after separating the centered mean term, the remaining work is exactly the
    -- covariance-only branch helper.
    simpa [covarianceBranch] using
      gaussian_covariance_branch_concave_on_covariance_region
        hN y Ybar rfl sampleCov rfl R₁ R₂ lam hR₁symm hR₂symm
        (by intro x hx; simpa [quadraticForm] using hR₁pos x hx)
        (by intro x hx; simpa [quadraticForm] using hR₂pos x hx)
        (by intro x; simpa [sampleCov, Ybar, quadraticForm] using hSlack₁ x)
        (by intro x; simpa [sampleCov, Ybar, quadraticForm] using hSlack₂ x)
        hlam₀ hlam₁
  have hComboPd : (lam • R₁ + (1 - lam) • R₂).PosDef := by
    -- The convex combination stays positive definite, so the Gaussian log decomposition applies.
    have hab : lam + (1 - lam) = 1 := by ring
    simpa using
      posDef_convexCombination hR₁pd hR₂pd hlam₀ (sub_nonneg.mpr hlam₁) hab
  have hDecomp₁ :
      l (R₁, a₁) =
        covarianceBranch R₁ - ((N : ℝ) / 2) * quadraticForm R₁⁻¹ (fun i => a₁ i - Ybar i) := by
    -- Expand the first endpoint log-likelihood into the covariance branch plus centered mean term.
    simpa [l, p, covarianceBranch, one_div] using
      gaussian_logLikelihood_centered_decomposition hN y Ybar rfl R₁ a₁ hR₁pd
  have hDecomp₂ :
      l (R₂, a₂) =
        covarianceBranch R₂ - ((N : ℝ) / 2) * quadraticForm R₂⁻¹ (fun i => a₂ i - Ybar i) := by
    -- The second endpoint has the same decomposition.
    simpa [l, p, covarianceBranch, one_div] using
      gaussian_logLikelihood_centered_decomposition hN y Ybar rfl R₂ a₂ hR₂pd
  have hDecompComboRaw :
      l (lam • R₁ + (1 - lam) • R₂, lam • a₁ + (1 - lam) • a₂) =
        covarianceBranch (lam • R₁ + (1 - lam) • R₂) -
          ((N : ℝ) / 2) *
            quadraticForm ((lam • R₁ + (1 - lam) • R₂)⁻¹)
              (fun j => (lam • a₁ + (1 - lam) • a₂) j - Ybar j) := by
    -- The raw decomposition keeps the mean term in direct affine coordinates.
    simpa [l, p, covarianceBranch, one_div] using
      gaussian_logLikelihood_centered_decomposition
        hN y Ybar rfl (lam • R₁ + (1 - lam) • R₂) (lam • a₁ + (1 - lam) • a₂) hComboPd
  have hDecompCombo :
      l (lam • R₁ + (1 - lam) • R₂, lam • a₁ + (1 - lam) • a₂) =
        covarianceBranch (lam • R₁ + (1 - lam) • R₂) -
          ((N : ℝ) / 2) *
            quadraticForm ((lam • R₁ + (1 - lam) • R₂)⁻¹)
              (lam • (fun i => a₁ i - Ybar i) + (1 - lam) • (fun i => a₂ i - Ybar i)) := by
    -- Rewrite the affine mean coordinate into the centered combination from `hCenteredConvex`.
    calc
      l (lam • R₁ + (1 - lam) • R₂, lam • a₁ + (1 - lam) • a₂)
          = covarianceBranch (lam • R₁ + (1 - lam) • R₂) -
              ((N : ℝ) / 2) *
                quadraticForm ((lam • R₁ + (1 - lam) • R₂)⁻¹)
                  (fun j => (lam • a₁ + (1 - lam) • a₂) j - Ybar j) := hDecompComboRaw
      _ = covarianceBranch (lam • R₁ + (1 - lam) • R₂) -
            ((N : ℝ) / 2) *
              quadraticForm ((lam • R₁ + (1 - lam) • R₂)⁻¹)
                (lam • (fun i => a₁ i - Ybar i) + (1 - lam) • (fun i => a₂ i - Ybar i)) := by
            rw [hCenterCombo]
  have hCenteredTerm :
      -((N : ℝ) / 2) *
          quadraticForm ((lam • R₁ + (1 - lam) • R₂)⁻¹)
            (lam • (fun i => a₁ i - Ybar i) + (1 - lam) • (fun i => a₂ i - Ybar i)) ≥
        -((N : ℝ) / 2) *
          (lam * quadraticForm R₁⁻¹ (fun i => a₁ i - Ybar i) +
            (1 - lam) * quadraticForm R₂⁻¹ (fun i => a₂ i - Ybar i)) := by
    -- Multiplying the Jensen inequality by the negative coefficient `-(N/2)` flips the order.
    have hCoeff : 0 ≤ (N : ℝ) / 2 := by positivity
    nlinarith
  calc
    l (lam • R₁ + (1 - lam) • R₂, lam • a₁ + (1 - lam) • a₂)
        = covarianceBranch (lam • R₁ + (1 - lam) • R₂) -
            ((N : ℝ) / 2) *
              quadraticForm ((lam • R₁ + (1 - lam) • R₂)⁻¹)
                (lam • (fun i => a₁ i - Ybar i) + (1 - lam) • (fun i => a₂ i - Ybar i)) := by
            exact hDecompCombo
    _ ≥ (lam * covarianceBranch R₁ + (1 - lam) * covarianceBranch R₂) +
          (-((N : ℝ) / 2) *
            (lam * quadraticForm R₁⁻¹ (fun i => a₁ i - Ybar i) +
              (1 - lam) * quadraticForm R₂⁻¹ (fun i => a₂ i - Ybar i))) := by
            linarith [hCovarianceBranch, hCenteredTerm]
    _ = lam * (covarianceBranch R₁ - ((N : ℝ) / 2) * quadraticForm R₁⁻¹ (fun i => a₁ i - Ybar i)) +
          (1 - lam) *
            (covarianceBranch R₂ - ((N : ℝ) / 2) * quadraticForm R₂⁻¹ (fun i => a₂ i - Ybar i)) := by
            ring
    _ = lam * l (R₁, a₁) + (1 - lam) * l (R₂, a₂) := by
            rw [hDecomp₁, hDecomp₂]


end «problem-198»
