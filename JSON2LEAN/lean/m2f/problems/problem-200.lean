import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-200»

/- [BLOCK Exercise 7.4-(a) | 1 | defn]
Given a parametric family of densities or likelihoods {p_θ} and observed data, a parameter value
hatθ is a maximum-likelihood estimate if hatθ ∈ argmax_θ L(θ), equivalently if hatθ ∈ argmax_θ
ell(θ), where L is the likelihood and ell = log L is the log-likelihood.
-/
def IsMaximumLikelihoodEstimate {Θ : Type*} (L ℓ : Θ → ℝ) (θhat : Θ) : Prop :=
  (∀ θ : Θ, 0 < L θ) ∧
    (∀ θ : Θ, ℓ θ = Real.log (L θ)) ∧
    (∀ θ : Θ, L θ ≤ L θhat) ∧
    (∀ θ : Θ, ℓ θ ≤ ℓ θhat)

/- [BLOCK Exercise 7.4-(a) | 2 | defn]
For observed data y₁,dots,y_N under a parametric density p_θ, the log-likelihood function is
ell(θ)=sum_{k=1}^N log p_θ(yₖ), defined for parameter values θ such that each p_θ(yₖ)>0.
-/
def logLikelihood {Θ Y : Type*} (p : Θ → Y → ℝ) (y : Fin N → Y) :
    {θ : Θ // ∀ k : Fin N, p θ (y k) > 0} → ℝ :=
  fun θ => ∑ k : Fin N, Real.log (p θ.1 (y k))

/-- Every Gaussian likelihood factor, and hence the full likelihood, is positive. -/
lemma gaussian_likelihood_pos {n N : ℕ} (y : Fin N → Fin n → ℝ) :
    let p :
        ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)) →
          (Fin n → ℝ) → ℝ :=
      fun θ z =>
        (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
          Real.rpow (Matrix.det θ.1.1) (-(1 : ℝ) / 2)) *
          Real.exp
            (-(1 / 2 : ℝ) *
              dotProduct (fun i => z i - θ.2 i)
                (fun i => ∑ j : Fin n, (θ.1.1⁻¹) i j * (z j - θ.2 j)))
    let L :
        ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)) → ℝ :=
      fun θ => ∏ k : Fin N, p θ (y k)
    ∀ θ : ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)), 0 < L θ := by
  dsimp
  intro θ
  -- Each Gaussian density factor is positive, so the finite product stays positive.
  refine Finset.prod_pos ?_
  intro k hk
  have hdet : 0 < Matrix.det θ.1.1 := Matrix.PosDef.det_pos θ.1.2
  positivity

/-- The centered sample vectors sum to zero. -/
lemma sample_centered_sum_eq_zero {n N : ℕ} (hN : 0 < N) (y : Fin N → Fin n → ℝ) :
    let μ : Fin n → ℝ := fun i => (N : ℝ)⁻¹ * ∑ t : Fin N, y t i
    ∑ k : Fin N, (fun i => y k i - μ i) = 0 := by
  dsimp
  ext i
  -- Evaluate the vector-valued sum coordinatewise and separate the constant mean term.
  rw [Finset.sum_apply, Pi.zero_apply, Finset.sum_sub_distrib]
  have hsum :
      (∑ _k : Fin N, ((N : ℝ)⁻¹ * ∑ t : Fin N, y t i)) =
        (N : ℝ) * ((N : ℝ)⁻¹ * ∑ t : Fin N, y t i) := by
    simp [nsmul_eq_mul]
  -- The duplicated mean contribution cancels against the raw sample sum.
  rw [hsum]
  field_simp [hN.ne']
  ring

/-- The quadratic mean-gap term is nonnegative for every positive-definite precision matrix. -/
lemma mean_gap_nonneg {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ}
    (hR : R.PosDef) (μ a : Fin n → ℝ) :
    0 ≤ dotProduct (fun i => μ i - a i) (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)) := by
  -- This is the standard positive-semidefinite quadratic-form inequality for `R⁻¹`.
  simpa using Matrix.PosSemidef.dotProduct_mulVec_nonneg hR.inv.posSemidef (fun i => μ i - a i)

/-- If the positive-definite quadratic mean-gap vanishes, then the candidate mean equals the sample mean. -/
lemma mean_gap_eq_zero_implies_eq {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ}
    (hR : R.PosDef) (μ a : Fin n → ℝ)
    (hzero :
      dotProduct (fun i => μ i - a i) (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)) = 0) :
    a = μ := by
  -- Vanishing of the quadratic form forces the inverse covariance to kill the gap vector.
  have hmul : R⁻¹ *ᵥ (fun i => μ i - a i) = 0 := by
    simpa using
      (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hR.inv.posSemidef (fun i => μ i - a i)).mp
        hzero
  have hinj : Function.Injective (fun x : Fin n → ℝ => R⁻¹ *ᵥ x) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hR.inv.isUnit
  have hvec : (fun i => μ i - a i) = 0 := hinj <| by simp [hmul]
  -- Read the zero vector coordinatewise to recover equality of the two means.
  ext i
  have hi : μ i - a i = 0 := by simpa using congrFun hvec i
  linarith

/-- For a positive-definite matrix, `log det` is bounded above by `trace - dim`. -/
lemma posDef_log_det_le_trace_sub_card {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) :
    Real.log (Matrix.det A) ≤ Matrix.trace A - (Fintype.card n : ℝ) := by
  -- Diagonalize the positive-definite matrix and reduce to the scalar inequality
  -- `log x ≤ x - 1` on each positive eigenvalue.
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues]
  change Real.log (∏ i : n, (hA.isHermitian.eigenvalues i : ℝ)) ≤
    (∑ i : n, (hA.isHermitian.eigenvalues i : ℝ)) - (Fintype.card n : ℝ)
  rw [show Real.log (∏ i : n, (hA.isHermitian.eigenvalues i : ℝ)) =
      ∑ i : n, Real.log (hA.isHermitian.eigenvalues i) by
        simpa using (Real.log_prod (s := Finset.univ)
          (f := fun i : n => (hA.isHermitian.eigenvalues i : ℝ))
          (fun i _ => (hA.eigenvalues_pos i).ne'))]
  calc
    ∑ i, Real.log (hA.isHermitian.eigenvalues i)
      ≤ ∑ i, (hA.isHermitian.eigenvalues i - 1) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)
    _ = (∑ i, hA.isHermitian.eigenvalues i) - (Fintype.card n : ℝ) := by
      rw [Finset.sum_sub_distrib]
      simp

/-- Equality in the positive-definite `log det ≤ trace - dim` inequality forces the matrix to be the identity. -/
lemma posDef_log_det_eq_trace_sub_card_implies_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef)
    (heq : Real.log (Matrix.det A) = Matrix.trace A - (Fintype.card n : ℝ)) :
    A = 1 := by
  -- Rewrite the equality in terms of eigenvalues, so the scalar equality case can be applied
  -- coordinatewise.
  have heq' := heq
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues] at heq'
  change Real.log (∏ i : n, (hA.isHermitian.eigenvalues i : ℝ)) =
    (∑ i : n, (hA.isHermitian.eigenvalues i : ℝ)) - (Fintype.card n : ℝ) at heq'
  rw [show Real.log (∏ i : n, (hA.isHermitian.eigenvalues i : ℝ)) =
      ∑ i : n, Real.log (hA.isHermitian.eigenvalues i) by
        simpa using (Real.log_prod (s := Finset.univ)
          (f := fun i : n => (hA.isHermitian.eigenvalues i : ℝ))
          (fun i _ => (hA.eigenvalues_pos i).ne'))] at heq'
  have hcard : (Fintype.card n : ℝ) = ∑ i : n, (1 : ℝ) := by simp
  rw [hcard] at heq'
  have hsumEq :
      (∑ i : n, Real.log (hA.isHermitian.eigenvalues i)) =
        ∑ i : n, ((hA.isHermitian.eigenvalues i : ℝ) - 1) := by
    simpa [Finset.sum_sub_distrib] using heq'
  have hsumZero :
      ∑ i : n,
        (((hA.isHermitian.eigenvalues i : ℝ) - 1) - Real.log (hA.isHermitian.eigenvalues i)) = 0 := by
    rw [Finset.sum_sub_distrib, hsumEq]
    ring
  have htermNonneg :
      ∀ i : n,
        0 ≤ (((hA.isHermitian.eigenvalues i : ℝ) - 1) - Real.log (hA.isHermitian.eigenvalues i)) := by
    intro i
    linarith [Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)]
  have htermZero :
      ∀ i : n,
        (((hA.isHermitian.eigenvalues i : ℝ) - 1) - Real.log (hA.isHermitian.eigenvalues i)) = 0 := by
    have h :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun i : n =>
          (((hA.isHermitian.eigenvalues i : ℝ) - 1) - Real.log (hA.isHermitian.eigenvalues i)))
        fun i _ => htermNonneg i)
    intro i
    exact (h.mp hsumZero) i (Finset.mem_univ i)
  have heig : hA.isHermitian.eigenvalues = fun _ => 1 := by
    funext i
    by_contra hi
    -- A non-unit eigenvalue would force strict inequality in the scalar bound.
    have hlt :
        Real.log (hA.isHermitian.eigenvalues i) < (hA.isHermitian.eigenvalues i : ℝ) - 1 :=
      Real.log_lt_sub_one_of_pos (hA.eigenvalues_pos i) hi
    have hzero := htermZero i
    linarith
  -- With all eigenvalues equal to `1`, the spectral theorem collapses the matrix to the identity.
  rw [hA.isHermitian.spectral_theorem, heig]
  simp

/-- Pairing a rank-one outer product with the trace recovers the associated quadratic form. -/
private lemma trace_mul_vecMulVec_eq_dotProduct {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix.trace (M * Matrix.vecMulVec x x) = dotProduct x (M *ᵥ x) := by
  -- Rewrite the product as a rank-one matrix built from `M *ᵥ x`, then read off its trace.
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- If the centered sample vectors sum to zero, then the shifted outer-product sum splits into the
centered covariance part and the pure mean-shift part. -/
private lemma sum_vecMulVec_split_centered {n N : ℕ}
    (y : Fin N → Fin n → ℝ) (μ a : Fin n → ℝ)
    (hCentered : ∑ k : Fin N, (fun i => y k i - μ i) = 0) :
    ∑ k : Fin N,
        Matrix.vecMulVec (fun i => y k i - a i) (fun j => y k j - a j) =
      ∑ k : Fin N,
        Matrix.vecMulVec (fun i => y k i - μ i) (fun j => y k j - μ j) +
        (N : ℝ) • Matrix.vecMulVec (fun i => μ i - a i) (fun j => μ j - a j) := by
  ext i j
  have hi : ∑ k : Fin N, (y k i - μ i) = 0 := by
    simpa using congrFun hCentered i
  have hj : ∑ k : Fin N, (y k j - μ j) = 0 := by
    simpa using congrFun hCentered j
  have hCrossLeft : ∑ x : Fin N, (y x i - μ i) * (μ j - a j) = 0 := by
    calc
      ∑ x : Fin N, (y x i - μ i) * (μ j - a j)
          = (∑ x : Fin N, (y x i - μ i)) * (μ j - a j) := by
              rw [Finset.sum_mul]
      _ = 0 := by rw [hi, zero_mul]
  have hCrossRight : ∑ x : Fin N, (μ i - a i) * (y x j - μ j) = 0 := by
    calc
      ∑ x : Fin N, (μ i - a i) * (y x j - μ j)
          = (μ i - a i) * ∑ x : Fin N, (y x j - μ j) := by
              rw [Finset.mul_sum]
      _ = 0 := by rw [hj, mul_zero]
  -- Expand the shifted product entrywise and kill the mixed terms with the centering identities.
  calc
    (∑ k : Fin N, Matrix.vecMulVec (fun i => y k i - a i) (fun j => y k j - a j)) i j
        = ∑ k : Fin N, (y k i - a i) * (y k j - a j) := by
            simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
    _ =
        ∑ k : Fin N,
          ((y k i - μ i) * (y k j - μ j) +
            (y k i - μ i) * (μ j - a j) +
            (μ i - a i) * (y k j - μ j) +
            (μ i - a i) * (μ j - a j)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ =
        ∑ k : Fin N,
          Matrix.vecMulVec (fun i => y k i - μ i) (fun j => y k j - μ j) i j +
        ((N : ℝ) • Matrix.vecMulVec (fun i => μ i - a i) (fun j => μ j - a j)) i j := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [hCrossLeft, hCrossRight]
          simp [Matrix.smul_apply, Matrix.vecMulVec_apply]
    _ =
        (∑ k : Fin N,
          Matrix.vecMulVec (fun i => y k i - μ i) (fun j => y k j - μ j) +
          (N : ℝ) • Matrix.vecMulVec (fun i => μ i - a i) (fun j => μ j - a j)) i j := by
          simp [Matrix.sum_apply]

/-- The summed Gaussian quadratic term splits into covariance and centered mean-gap contributions. -/
private lemma quadratic_sum_split_at_sample_mean {n N : ℕ} (hN : 0 < N)
    (y : Fin N → Fin n → ℝ) {R : Matrix (Fin n) (Fin n) ℝ}
    (_hR : R.PosDef) (a : Fin n → ℝ) :
    let μ : Fin n → ℝ := fun i => (N : ℝ)⁻¹ * ∑ t : Fin N, y t i
    let Y : Matrix (Fin n) (Fin n) ℝ :=
      (N : ℝ)⁻¹ •
        ∑ k : Fin N,
          Matrix.vecMulVec
            (fun i => y k i - μ i)
            (fun i => y k i - μ i)
    ∑ k : Fin N,
        dotProduct (fun i => y k i - a i)
          (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)) =
      (N : ℝ) * Matrix.trace (R⁻¹ * Y) +
        (N : ℝ) *
          dotProduct (fun i => μ i - a i)
            (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)) := by
  dsimp
  let μ : Fin n → ℝ := fun i => (N : ℝ)⁻¹ * ∑ t : Fin N, y t i
  let Y : Matrix (Fin n) (Fin n) ℝ :=
    (N : ℝ)⁻¹ •
      ∑ k : Fin N,
        Matrix.vecMulVec (fun i => y k i - μ i) (fun i => y k i - μ i)
  change
    ∑ k : Fin N,
        dotProduct (fun i => y k i - a i)
          (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)) =
      (N : ℝ) * Matrix.trace (R⁻¹ * Y) +
        (N : ℝ) *
          dotProduct (fun i => μ i - a i)
            (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j))
  have hOuter :
      ∑ k : Fin N,
          Matrix.vecMulVec (fun i => y k i - a i) (fun j => y k j - a j) =
        ∑ k : Fin N,
          Matrix.vecMulVec (fun i => y k i - μ i)
            (fun j => y k j - μ j) +
          (N : ℝ) •
            Matrix.vecMulVec (fun i => μ i - a i) (fun j => μ j - a j) := by
    have hCentered :
        ∑ k : Fin N, (fun i => y k i - μ i) = 0 := by
      -- The empirical mean centers the sample, so the mixed terms vanish.
      simpa [μ] using sample_centered_sum_eq_zero hN y
    simpa using sum_vecMulVec_split_centered y μ a hCentered
  have hYsum :
      ∑ k : Fin N,
          Matrix.vecMulVec (fun i => y k i - μ i) (fun i => y k i - μ i) =
        (N : ℝ) • Y := by
    -- This is the defining scalar normalization of the sample covariance matrix.
    simp [Y, smul_smul, hN.ne']
  -- Convert the quadratic-form sum into a trace of outer products, then substitute the split sum.
  calc
    ∑ k : Fin N,
        dotProduct (fun i => y k i - a i)
          (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j))
        =
        ∑ k : Fin N,
          Matrix.trace
            (R⁻¹ * Matrix.vecMulVec (fun i => y k i - a i) (fun j => y k j - a j)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          symm
          simpa using trace_mul_vecMulVec_eq_dotProduct R⁻¹ (fun i => y k i - a i)
    _ =
        Matrix.trace
          (R⁻¹ *
            ∑ k : Fin N, Matrix.vecMulVec (fun i => y k i - a i) (fun j => y k j - a j)) := by
          rw [Matrix.mul_sum, Matrix.trace_sum]
    _ =
        Matrix.trace
          (R⁻¹ *
            ((N : ℝ) • Y +
              (N : ℝ) •
                Matrix.vecMulVec (fun i => μ i - a i)
                  (fun j => μ j - a j))) := by
          rw [hOuter, hYsum]
    _ =
        (N : ℝ) *
            Matrix.trace
              (R⁻¹ * Y) +
          (N : ℝ) *
            Matrix.trace
              (R⁻¹ * Matrix.vecMulVec (fun i => μ i - a i) (fun j => μ j - a j)) := by
          simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    _ =
        (N : ℝ) *
            Matrix.trace (R⁻¹ * Y) +
          (N : ℝ) *
            dotProduct (fun i => μ i - a i)
              (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)) := by
          simpa [Matrix.mulVec] using
            congrArg (fun t : ℝ => (N : ℝ) * Matrix.trace (R⁻¹ * Y) + (N : ℝ) * t)
              (trace_mul_vecMulVec_eq_dotProduct R⁻¹ (fun i => μ i - a i))

/-- The square-root sandwich packages the covariance term into a positive-definite matrix with the
same trace contribution and determinant ratio. -/
private lemma covariance_sandwich_trace_det {n : ℕ}
    {Y R : Matrix (Fin n) (Fin n) ℝ} (hY : Y.PosDef) (hR : R.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ,
      Y = Sᴴ * S ∧
      IsUnit S ∧
      let A : Matrix (Fin n) (Fin n) ℝ := S * R⁻¹ * Sᴴ
      A.PosDef ∧ Matrix.trace A = Matrix.trace (R⁻¹ * Y) ∧
        Matrix.det A = Matrix.det Y / Matrix.det R := by
  obtain ⟨S, hSfac⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hY.posSemidef
  have hSunit : IsUnit S := by
    have hdetY :
        Matrix.det Y = Matrix.det S * Matrix.det S := by
      rw [hSfac, Matrix.det_mul, Matrix.det_conjTranspose]
      simp
    have hSdet_ne : Matrix.det S ≠ 0 := by
      have hYdetPos : 0 < Matrix.det Y := hY.det_pos
      intro hzero
      rw [hdetY, hzero] at hYdetPos
      norm_num at hYdetPos
    exact (Matrix.isUnit_iff_isUnit_det (A := S)).2 (IsUnit.mk0 _ hSdet_ne)
  have hApos' : (S * R⁻¹ * star S).PosDef := by
    -- Positive definiteness is preserved by conjugation with the invertible factor `S`.
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (U := S) (x := R⁻¹) hSunit).2 hR.inv
  have hTrace :
      Matrix.trace (S * R⁻¹ * Sᴴ) = Matrix.trace (R⁻¹ * Y) := by
    -- Cycle the trace until the factorization `Y = Sᴴ * S` appears.
    calc
      Matrix.trace (S * R⁻¹ * Sᴴ)
          = Matrix.trace (Sᴴ * S * R⁻¹) := by
              rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (R⁻¹ * (Sᴴ * S)) := by
            rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (R⁻¹ * Y) := by
            rw [hSfac]
  have hDet :
      Matrix.det (S * R⁻¹ * Sᴴ) = Matrix.det Y / Matrix.det R := by
    -- The determinant factors through the sandwich, and the `Sᴴ * S` term recovers `det Y`.
    calc
      Matrix.det (S * R⁻¹ * Sᴴ)
          = Matrix.det S * Matrix.det R⁻¹ * Matrix.det Sᴴ := by
              rw [Matrix.det_mul, Matrix.det_mul]
      _ = Matrix.det S * Matrix.det S * Matrix.det R⁻¹ := by
            rw [Matrix.det_conjTranspose]
            simp
            ring
      _ = Matrix.det Y * Matrix.det R⁻¹ := by
            rw [hSfac, Matrix.det_mul, Matrix.det_conjTranspose]
            simp
      _ = Matrix.det Y / Matrix.det R := by
            rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, div_eq_mul_inv]
  exact ⟨S, hSfac, hSunit, hApos', hTrace, hDet⟩

/-- If the square-root covariance sandwich is the identity, then the candidate covariance equals
the sample covariance. -/
private lemma covariance_sandwich_eq_one_implies_eq {n : ℕ}
    {Y R : Matrix (Fin n) (Fin n) ℝ} (_hY : Y.PosDef) (hR : R.PosDef)
    {S : Matrix (Fin n) (Fin n) ℝ} (hSfac : Y = Sᴴ * S) (hSunit : IsUnit S)
    (hA : S * R⁻¹ * Sᴴ = 1) :
    R = Y := by
  letI := hSunit.invertible
  have hLeft : Y * R⁻¹ = 1 := by
    have hSstarUnit : IsUnit Sᴴ := hSunit.star
    letI := hSstarUnit.invertible
    -- Multiply the sandwich identity by `Sᴴ` on the left and `(Sᴴ)⁻¹` on the right.
    calc
      Y * R⁻¹ = (Sᴴ * S) * R⁻¹ := by rw [hSfac]
      _ = Sᴴ * (S * R⁻¹) := by rw [Matrix.mul_assoc]
      _ = Sᴴ * ((S * R⁻¹) * (Sᴴ * (Sᴴ)⁻¹)) := by
            congr 1
            calc
              S * R⁻¹ = (S * R⁻¹) * 1 := by simp
              _ = (S * R⁻¹) * (Sᴴ * (Sᴴ)⁻¹) := by rw [Matrix.mul_inv_of_invertible]
      _ = Sᴴ * ((S * R⁻¹ * Sᴴ) * (Sᴴ)⁻¹) := by
            congr 1
            rw [← Matrix.mul_assoc]
      _ = Sᴴ * (1 * (Sᴴ)⁻¹) := by rw [hA]
      _ = 1 := by simp [Matrix.mul_inv_of_invertible]
  letI := hR.isUnit.invertible
  -- The same right inverse for `R⁻¹` determines the covariance uniquely.
  exact Matrix.right_inv_eq_left_inv (A := R⁻¹) (B := R) (C := Y)
    (Matrix.inv_mul_of_invertible R) hLeft

/-- The covariance contribution is always nonnegative, and equality characterizes the true sample
covariance. -/
private lemma covariance_gap_nonneg_eq_zero_iff {n : ℕ}
    {Y R : Matrix (Fin n) (Fin n) ℝ} (hY : Y.PosDef) (hR : R.PosDef) :
    (Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ) ≤
        Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y)) ∧
      ((Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ) =
          Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y)) → R = Y) := by
  obtain ⟨S, hSfac, hSunit, hApos, hTrace, hDet⟩ := covariance_sandwich_trace_det hY hR
  have hBase :
      Real.log (Matrix.det (S * R⁻¹ * Sᴴ)) ≤
        Matrix.trace (S * R⁻¹ * Sᴴ) - (Fintype.card (Fin n) : ℝ) := by
    -- Apply the scalar `log det ≤ trace - dim` inequality to the square-root sandwich.
    simpa using posDef_log_det_le_trace_sub_card hApos
  have hCovLe :
      Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ) ≤
        Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) := by
    -- Rewrite the sandwich inequality in terms of the original covariance matrices.
    rw [hTrace, hDet, Real.log_div hY.det_pos.ne' hR.det_pos.ne'] at hBase
    linarith
  refine ⟨hCovLe, ?_⟩
  intro hEq
  have hBaseEq :
      Real.log (Matrix.det (S * R⁻¹ * Sᴴ)) =
        Matrix.trace (S * R⁻¹ * Sᴴ) - (Fintype.card (Fin n) : ℝ) := by
    -- Equality of the covariance gap upgrades the sandwich inequality to equality.
    calc
      Real.log (Matrix.det (S * R⁻¹ * Sᴴ))
          = Real.log (Matrix.det Y) - Real.log (Matrix.det R) := by
              rw [hDet, Real.log_div hY.det_pos.ne' hR.det_pos.ne']
      _ = Matrix.trace (R⁻¹ * Y) - (Fintype.card (Fin n) : ℝ) := by
            linarith [hEq]
      _ = Matrix.trace (S * R⁻¹ * Sᴴ) - (Fintype.card (Fin n) : ℝ) := by
            rw [hTrace]
  have hAone : S * R⁻¹ * Sᴴ = 1 :=
    posDef_log_det_eq_trace_sub_card_implies_one hApos hBaseEq
  -- Transport the identity sandwich back to equality of covariance matrices.
  exact covariance_sandwich_eq_one_implies_eq hY hR hSfac hSunit hAone

/-- The Gaussian log-likelihood rewrites as a constant minus a covariance gap and a mean gap. -/
private lemma gaussian_logLikelihood_rewrite {n N : ℕ} (hN : 0 < N)
    (y : Fin N → Fin n → ℝ) {R : Matrix (Fin n) (Fin n) ℝ}
    (hR : R.PosDef) (a : Fin n → ℝ) :
    let μ : Fin n → ℝ := fun i => (N : ℝ)⁻¹ * ∑ t : Fin N, y t i
    let Y : Matrix (Fin n) (Fin n) ℝ :=
      (N : ℝ)⁻¹ •
        ∑ k : Fin N,
          Matrix.vecMulVec
            (fun i => y k i - μ i)
            (fun i => y k i - μ i)
    Real.log
        (∏ k : Fin N,
          ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det R) ^ (-(1 : ℝ) / 2)) *
            Real.exp
              (-(1 / 2 : ℝ) *
                dotProduct (fun i => y k i - a i)
                  (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)))) =
      (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
        ((N : ℝ) / 2) *
          (Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) +
            dotProduct (fun i => μ i - a i) (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j))) := by
  dsimp
  let c : ℝ := Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)
  let d : ℝ := Real.rpow (Matrix.det R) (-(1 : ℝ) / 2)
  have hcPos : 0 < c := by
    -- The Gaussian normalizing constant is strictly positive.
    dsimp [c]
    positivity
  have hdetPos : 0 < Matrix.det R := hR.det_pos
  have hdPos : 0 < d := by
    -- The determinant factor stays positive because `R` is positive definite.
    dsimp [d]
    exact Real.rpow_pos_of_pos hdetPos _
  have hQuad :
      ∑ k : Fin N,
          dotProduct (fun i => y k i - a i)
            (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)) =
        (N : ℝ) *
            Matrix.trace
              (R⁻¹ *
                ((N : ℝ)⁻¹ •
                  ∑ k : Fin N,
                    Matrix.vecMulVec (fun i => y k i - (N : ℝ)⁻¹ * ∑ t : Fin N, y t i)
                      (fun i => y k i - (N : ℝ)⁻¹ * ∑ t : Fin N, y t i))) +
          (N : ℝ) *
            dotProduct (fun i => (N : ℝ)⁻¹ * ∑ t : Fin N, y t i - a i)
              (fun i => ∑ j : Fin n, R⁻¹ i j * ((N : ℝ)⁻¹ * ∑ t : Fin N, y t j - a j)) := by
    -- This is the completion-of-squares identity at the sample mean.
    simpa using quadratic_sum_split_at_sample_mean hN y hR a
  have hProd :
      Real.log
          (∏ k : Fin N,
            (c * d) *
              Real.exp
                (-(1 / 2 : ℝ) *
                  dotProduct (fun i => y k i - a i)
                    (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)))) =
        ∑ k : Fin N,
          Real.log
            ((c * d) *
              Real.exp
                (-(1 / 2 : ℝ) *
                  dotProduct (fun i => y k i - a i)
                    (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)))) := by
    -- The log of the positive finite product becomes the sum of the logs.
    simpa using
      (Real.log_prod (s := Finset.univ)
        (f := fun k : Fin N =>
          (c * d) *
            Real.exp
              (-(1 / 2 : ℝ) *
                dotProduct (fun i => y k i - a i)
                  (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j))))
        (fun k hk => (show 0 <
          (c * d) *
            Real.exp
              (-(1 / 2 : ℝ) *
                dotProduct (fun i => y k i - a i)
                  (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j))) by positivity).ne'))
  -- Expand the logarithm termwise and then substitute the quadratic split.
  calc
    Real.log
        (∏ k : Fin N,
          ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det R) ^ (-(1 : ℝ) / 2)) *
            Real.exp
              (-(1 / 2 : ℝ) *
                dotProduct (fun i => y k i - a i)
                  (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j))))
        =
        ∑ k : Fin N,
          Real.log
            ((c * d) *
              Real.exp
                (-(1 / 2 : ℝ) *
                  dotProduct (fun i => y k i - a i)
                    (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)))) := by
          simpa [c, d] using hProd
    _ =
        ∑ k : Fin N,
          (Real.log c - Real.log (Matrix.det R) / 2 -
            dotProduct (fun i => y k i - a i)
              (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)) / 2) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          calc
            Real.log
                ((c * d) *
                  Real.exp
                    (-(1 / 2 : ℝ) *
                      dotProduct (fun i => y k i - a i)
                        (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j))))
                =
                Real.log (c * d) +
                  Real.log
                    (Real.exp
                      (-(1 / 2 : ℝ) *
                        dotProduct (fun i => y k i - a i)
                          (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)))) := by
                  rw [Real.log_mul (mul_ne_zero hcPos.ne' hdPos.ne') (Real.exp_ne_zero _)]
            _ =
                Real.log c + Real.log d -
                  dotProduct (fun i => y k i - a i)
                    (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)) / 2 := by
                  rw [Real.log_mul hcPos.ne' hdPos.ne', Real.log_exp]
                  ring
            _ =
                Real.log c - Real.log (Matrix.det R) / 2 -
                  dotProduct (fun i => y k i - a i)
                    (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)) / 2 := by
                  rw [show Real.log d = (-(1 : ℝ) / 2) * Real.log (Matrix.det R) by
                        dsimp [d]
                        rw [Real.log_rpow hdetPos]]
                  ring
    _ =
        (N : ℝ) * Real.log c -
          (N : ℝ) * (Real.log (Matrix.det R) / 2) -
          ((∑ k : Fin N,
              dotProduct (fun i => y k i - a i)
                (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j))) / 2) := by
          have hHalfSum :
              (∑ k : Fin N,
                  dotProduct (fun i => y k i - a i)
                    (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)) / 2) =
                ((∑ k : Fin N,
                    dotProduct (fun i => y k i - a i)
                      (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j))) / 2) := by
            simp [div_eq_mul_inv, Finset.sum_mul]
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
            hHalfSum]
          simp [nsmul_eq_mul]
    _ =
        (N : ℝ) * Real.log c -
          (N : ℝ) * (Real.log (Matrix.det R) / 2) -
          (((N : ℝ) *
              Matrix.trace
                (R⁻¹ *
                  ((N : ℝ)⁻¹ •
                    ∑ k : Fin N,
                      Matrix.vecMulVec (fun i => y k i - (N : ℝ)⁻¹ * ∑ t : Fin N, y t i)
                        (fun i => y k i - (N : ℝ)⁻¹ * ∑ t : Fin N, y t i))) +
              (N : ℝ) *
                dotProduct (fun i => (N : ℝ)⁻¹ * ∑ t : Fin N, y t i - a i)
                  (fun i => ∑ j : Fin n, R⁻¹ i j * ((N : ℝ)⁻¹ * ∑ t : Fin N, y t j - a j))) / 2) := by
          rw [hQuad]
    _ =
        (N : ℝ) * Real.log c -
          ((N : ℝ) / 2) *
            (Real.log (Matrix.det R) +
              Matrix.trace
                (R⁻¹ *
                  ((N : ℝ)⁻¹ •
                    ∑ k : Fin N,
                      Matrix.vecMulVec (fun i => y k i - (N : ℝ)⁻¹ * ∑ t : Fin N, y t i)
                        (fun i => y k i - (N : ℝ)⁻¹ * ∑ t : Fin N, y t i))) +
              dotProduct (fun i => (N : ℝ)⁻¹ * ∑ t : Fin N, y t i - a i)
                (fun i => ∑ j : Fin n, R⁻¹ i j * ((N : ℝ)⁻¹ * ∑ t : Fin N, y t j - a j))) := by
          ring
    _ =
        (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
          ((N : ℝ) / 2) *
            (Real.log (Matrix.det R) +
              Matrix.trace
                (R⁻¹ *
                  ((N : ℝ)⁻¹ •
                    ∑ k : Fin N,
                      Matrix.vecMulVec (fun i => y k i - (N : ℝ)⁻¹ * ∑ t : Fin N, y t i)
                        (fun i => y k i - (N : ℝ)⁻¹ * ∑ t : Fin N, y t i))) +
              dotProduct (fun i => (N : ℝ)⁻¹ * ∑ t : Fin N, y t i - a i)
                (fun i => ∑ j : Fin n, R⁻¹ i j * ((N : ℝ)⁻¹ * ∑ t : Fin N, y t j - a j))) := by
          simp [c]


/- [BLOCK Exercise 7.4-(a) | 4 | thm]
Let R ∈ ℝ^{n imes n} be symmetric positive definite, R succ 0, and let a ∈ ℝ^n. For y ∈ ℝ^n, define
p_{R,a}(y)=(2π)^{-n/2}det(R)^{-1/2}exp≤ft(-
rac{1}{2}(y-a)ᵀ R^{-1}(y-a)
ight). Let y₁,ldots,y_N ∈ ℝ^n be independent samples from this density, and define μ=
rac{1}{N}sum_{k=1}^N yₖ, Y=
rac{1}{N}sum_{k=1}^N (yₖ-μ)(yₖ-μ)ᵀ. The log-likelihood function is l(R,a)= -
rac{Nn}{2}log(2π)-
rac{N}{2}logdet R-
rac{1}{2}sum_{k=1}^N (y_{k-a})ᵀ R^{-1}(y_{k-a}), and l(R,a)=
rac{N}{2}≤ft(-nlog(2π)-logdet R-tr(R^{-1}Y)-(a-μ)ᵀ R^{-1}(a-μ)
ight). Using this expression, show that if Y succ 0, then the maximum-likelihood estimates of R and
a are unique and satisfy a_{ml}=μ, R_{ml}=Y.
-/
theorem gaussian_mle_unique_at_sample_mean_and_covariance
    {n N : ℕ} (hN : 0 < N)
    (y : Fin N → Fin n → ℝ)
    (hYpd :
      ((N : ℝ)⁻¹ •
        ∑ k : Fin N,
          Matrix.vecMulVec
            (fun i => y k i - ((N : ℝ)⁻¹ * ∑ t : Fin N, y t i))
            (fun i => y k i - ((N : ℝ)⁻¹ * ∑ t : Fin N, y t i))).PosDef) :
    let μ : Fin n → ℝ :=
      fun i => (N : ℝ)⁻¹ * ∑ t : Fin N, y t i
    let Y : Matrix (Fin n) (Fin n) ℝ :=
      (N : ℝ)⁻¹ •
        ∑ k : Fin N,
          Matrix.vecMulVec
            (fun i => y k i - μ i)
            (fun i => y k i - μ i)
    let p :
        ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)) →
          (Fin n → ℝ) → ℝ :=
      fun θ z =>
        (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
          Real.rpow (Matrix.det θ.1.1) (-(1 : ℝ) / 2)) *
          Real.exp
            (-(1 / 2 : ℝ) *
              dotProduct (fun i => z i - θ.2 i)
                (fun i => ∑ j : Fin n, (θ.1.1⁻¹) i j * (z j - θ.2 j)))
    let L :
        ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)) → ℝ :=
      fun θ => ∏ k : Fin N, p θ (y k)
    let ell :
        ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)) → ℝ :=
      fun θ => Real.log (L θ)
    let θstar : ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)) :=
      (⟨Y, hYpd⟩, μ)
    IsMaximumLikelihoodEstimate
        L
        ell
        θstar ∧
      ∀ θ : ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)),
        IsMaximumLikelihoodEstimate
            L
            ell
            θ →
          θ = θstar := by
  dsimp
  have hLpos :
      ∀ θ : ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)),
        0 <
          ∏ k : Fin N,
            ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θ.1.1) ^ (-(1 : ℝ) / 2)) *
              Real.exp
                (-(1 / 2 : ℝ) *
                  dotProduct (fun i => y k i - θ.2 i)
                    (fun i => ∑ j : Fin n, (θ.1.1⁻¹) i j * (y k j - θ.2 j))) := by
    -- The positivity part of the MLE predicate is immediate from the Gaussian density formula.
    simpa using gaussian_likelihood_pos y
  have hLogEq :
      ∀ θ : ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)),
        Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θ.1.1) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - θ.2 i)
                      (fun i => ∑ j : Fin n, (θ.1.1⁻¹) i j * (y k j - θ.2 j)))) =
          Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θ.1.1) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - θ.2 i)
                      (fun i => ∑ j : Fin n, (θ.1.1⁻¹) i j * (y k j - θ.2 j)))) := by
    -- The log-likelihood was defined to be `Real.log` of the likelihood.
    intro θ
    rfl
  have hCentered :
      ∑ k : Fin N, (fun i => y k i - (N : ℝ)⁻¹ * ∑ t : Fin N, y t i) = 0 := by
    -- The centered observations always sum to zero.
    simpa using sample_centered_sum_eq_zero hN y
  let μ : Fin n → ℝ := fun i => (N : ℝ)⁻¹ * ∑ t : Fin N, y t i
  let Y : Matrix (Fin n) (Fin n) ℝ :=
    (N : ℝ)⁻¹ •
      ∑ k : Fin N,
        Matrix.vecMulVec
          (fun i => y k i - μ i)
          (fun i => y k i - μ i)
  have hY : Y.PosDef := by
    simpa [Y, μ] using hYpd
  let θstar : ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)) := (⟨Y, hY⟩, μ)
  have hTraceStar : Matrix.trace (Y⁻¹ * Y) = (Fintype.card (Fin n) : ℝ) := by
    -- The sample covariance is invertible, so its inverse product collapses to the identity.
    letI := hY.isUnit.invertible
    rw [Matrix.inv_mul_of_invertible, Matrix.trace_one]
  have hEllRewrite :
      ∀ θ : ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)),
        Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θ.1.1) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - θ.2 i)
                      (fun i => ∑ j : Fin n, (θ.1.1⁻¹) i j * (y k j - θ.2 j)))) =
          (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
            ((N : ℝ) / 2) *
              (Real.log (Matrix.det θ.1.1) + Matrix.trace (θ.1.1⁻¹ * Y) +
                dotProduct (fun i => μ i - θ.2 i)
                  (fun i => ∑ j : Fin n, (θ.1.1⁻¹) i j * (μ j - θ.2 j))) := by
    intro θ
    rcases θ with ⟨⟨R, hR⟩, a⟩
    -- Route correction: replace the earlier eigenbasis bookkeeping with the direct
    -- sample-mean split and the square-root sandwich covariance route.
    simpa [μ, Y] using gaussian_logLikelihood_rewrite hN y hR a
  have hCovGap :
      ∀ {R : Matrix (Fin n) (Fin n) ℝ}, R.PosDef →
        (Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ) ≤
            Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y)) ∧
          ((Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ) =
              Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y)) → R = Y) := by
    intro R hR
    -- The covariance gap is exactly the positive-definite log-det inequality for the sandwich.
    exact covariance_gap_nonneg_eq_zero_iff hY hR
  have hEllMax :
      ∀ θ : ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)),
        Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θ.1.1) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - θ.2 i)
                      (fun i => ∑ j : Fin n, (θ.1.1⁻¹) i j * (y k j - θ.2 j)))) ≤
          Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θstar.1.1) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - θstar.2 i)
                      (fun i => ∑ j : Fin n, (θstar.1.1⁻¹) i j * (y k j - θstar.2 j)))) := by
    intro θ
    rcases θ with ⟨⟨R, hR⟩, a⟩
    have hRewriteθ := hEllRewrite ((⟨R, hR⟩, a))
    have hRewriteStar := hEllRewrite θstar
    obtain ⟨hCovLe, _⟩ := hCovGap hR
    have hMeanLe :
        0 ≤ dotProduct (fun i => μ i - a i) (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)) := by
      -- The centered mean-gap is a positive-definite quadratic form.
      exact mean_gap_nonneg hR μ a
    have hStarSimp :
        Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θstar.1.1) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - θstar.2 i)
                      (fun i => ∑ j : Fin n, (θstar.1.1⁻¹) i j * (y k j - θstar.2 j)))) =
          (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
            ((N : ℝ) / 2) * (Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ)) := by
      -- At the true parameter, the mean gap vanishes and `trace (Y⁻¹ * Y)` is the dimension.
      simpa [θstar, hTraceStar] using hRewriteStar
    have hGapNonneg :
        0 ≤
          (Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) -
              (Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ))) +
            dotProduct (fun i => μ i - a i)
              (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)) := by
      exact add_nonneg (sub_nonneg.mpr hCovLe) hMeanLe
    let meanGap : ℝ :=
      dotProduct (fun i => μ i - a i) (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j))
    let covGap : ℝ :=
      Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) -
        (Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ))
    have hDiff :
        Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θstar.1.1) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - θstar.2 i)
                      (fun i => ∑ j : Fin n, (θstar.1.1⁻¹) i j * (y k j - θstar.2 j)))) -
          Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det R) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - a i)
                      (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)))) =
          ((N : ℝ) / 2) * (covGap + meanGap) := by
      dsimp [covGap, meanGap]
      calc
        Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θstar.1.1) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - θstar.2 i)
                      (fun i => ∑ j : Fin n, (θstar.1.1⁻¹) i j * (y k j - θstar.2 j)))) -
          Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det R) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - a i)
                      (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j))))
            =
            ((N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
                ((N : ℝ) / 2) *
                  (Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ))) -
              ((N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
                ((N : ℝ) / 2) *
                  (Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) +
                    dotProduct (fun i => μ i - a i)
                      (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)))) := by
              rw [hStarSimp, hRewriteθ]
        _ = ((N : ℝ) / 2) * (covGap + meanGap) := by
              ring
    have hDiffNonneg :
        0 ≤
          Real.log
              (∏ k : Fin N,
                ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θstar.1.1) ^ (-(1 : ℝ) / 2)) *
                  Real.exp
                    (-(1 / 2 : ℝ) *
                      dotProduct (fun i => y k i - θstar.2 i)
                        (fun i => ∑ j : Fin n, (θstar.1.1⁻¹) i j * (y k j - θstar.2 j)))) -
            Real.log
              (∏ k : Fin N,
                ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det R) ^ (-(1 : ℝ) / 2)) *
                  Real.exp
                    (-(1 / 2 : ℝ) *
                      dotProduct (fun i => y k i - a i)
                        (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)))) := by
      have hGapNonneg' : 0 ≤ covGap + meanGap := by
        simpa [covGap, meanGap] using hGapNonneg
      have hCoeffNonneg : 0 ≤ (N : ℝ) / 2 := by positivity
      rw [hDiff]
      exact mul_nonneg hCoeffNonneg hGapNonneg'
    -- The candidate's covariance gap and mean gap are both nonnegative, so it cannot exceed `θstar`.
    exact sub_nonneg.mp hDiffNonneg
  have hLMax :
      ∀ θ : ({R : Matrix (Fin n) (Fin n) ℝ // R.PosDef} × (Fin n → ℝ)),
        (∏ k : Fin N,
            ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θ.1.1) ^ (-(1 : ℝ) / 2)) *
              Real.exp
                (-(1 / 2 : ℝ) *
                  dotProduct (fun i => y k i - θ.2 i)
                    (fun i => ∑ j : Fin n, (θ.1.1⁻¹) i j * (y k j - θ.2 j)))) ≤
          ∏ k : Fin N,
            ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θstar.1.1) ^ (-(1 : ℝ) / 2)) *
              Real.exp
                (-(1 / 2 : ℝ) *
                  dotProduct (fun i => y k i - θstar.2 i)
                    (fun i => ∑ j : Fin n, (θstar.1.1⁻¹) i j * (y k j - θstar.2 j))) := by
    intro θ
    have hLogLe := hEllMax θ
    have hPosθ := hLpos θ
    have hPosStar := hLpos θstar
    -- Strict monotonicity of `log` on positive reals transfers log-likelihood maximality to the
    -- original likelihood.
    exact (Real.log_le_log_iff hPosθ hPosStar).mp <| by
      simpa [hLogEq θ, hLogEq θstar] using hLogLe
  constructor
  · refine ⟨hLpos, hLogEq, hLMax, hEllMax⟩
  · intro θ hMLE
    rcases θ with ⟨⟨R, hR⟩, a⟩
    have hLe : Real.log
        (∏ k : Fin N,
          ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det R) ^ (-(1 : ℝ) / 2)) *
            Real.exp
              (-(1 / 2 : ℝ) *
                dotProduct (fun i => y k i - a i)
                  (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)))) ≤
      Real.log
        (∏ k : Fin N,
          ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θstar.1.1) ^ (-(1 : ℝ) / 2)) *
            Real.exp
              (-(1 / 2 : ℝ) *
                dotProduct (fun i => y k i - θstar.2 i)
                  (fun i => ∑ j : Fin n, (θstar.1.1⁻¹) i j * (y k j - θstar.2 j)))) := by
      exact hEllMax ((⟨R, hR⟩, a))
    have hGe :
        Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θstar.1.1) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - θstar.2 i)
                      (fun i => ∑ j : Fin n, (θstar.1.1⁻¹) i j * (y k j - θstar.2 j)))) ≤
          Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det R) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - a i)
                      (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)))) := by
      -- Any other MLE also maximizes the log-likelihood, so `θstar` cannot be larger.
      simpa [θstar] using hMLE.2.2.2 θstar
    have hEqEll :
        Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det R) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - a i)
                      (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)))) =
          Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θstar.1.1) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - θstar.2 i)
                      (fun i => ∑ j : Fin n, (θstar.1.1⁻¹) i j * (y k j - θstar.2 j)))) := by
      exact le_antisymm hLe hGe
    have hRewriteθ := hEllRewrite ((⟨R, hR⟩, a))
    have hRewriteStar := hEllRewrite θstar
    have hStarSimp :
        Real.log
            (∏ k : Fin N,
              ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det θstar.1.1) ^ (-(1 : ℝ) / 2)) *
                Real.exp
                  (-(1 / 2 : ℝ) *
                    dotProduct (fun i => y k i - θstar.2 i)
                      (fun i => ∑ j : Fin n, (θstar.1.1⁻¹) i j * (y k j - θstar.2 j)))) =
          (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
            ((N : ℝ) / 2) * (Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ)) := by
      -- The true parameter has zero mean gap and covariance trace exactly equal to the dimension.
      simpa [θstar, hTraceStar] using hRewriteStar
    obtain ⟨hCovLe, hCovEq⟩ := hCovGap hR
    have hMeanLe :
        0 ≤ dotProduct (fun i => μ i - a i) (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)) := by
      -- The mean-gap term is again a positive-definite quadratic form.
      exact mean_gap_nonneg hR μ a
    have hGapEq :
        Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) +
            dotProduct (fun i => μ i - a i) (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)) =
          Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ) := by
      let meanGap : ℝ :=
        dotProduct (fun i => μ i - a i) (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j))
      let covGap : ℝ :=
        Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) -
          (Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ))
      have hGapScaled : ((N : ℝ) / 2) * (covGap + meanGap) = 0 := by
        dsimp [covGap, meanGap]
        calc
          ((N : ℝ) / 2) *
              ((Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) -
                    (Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ))) +
                dotProduct (fun i => μ i - a i)
                  (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)))
              =
              ((N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
                  ((N : ℝ) / 2) *
                    (Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ))) -
                ((N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
                  ((N : ℝ) / 2) *
                    (Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) +
                      dotProduct (fun i => μ i - a i)
                        (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)))) := by
                ring
          _ = 0 := by
                apply sub_eq_zero.mpr
                calc
                  (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
                      ((N : ℝ) / 2) *
                        (Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ))
                    = Real.log
                        (∏ k : Fin N,
                          ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
                              (Matrix.det θstar.1.1) ^ (-(1 : ℝ) / 2)) *
                            Real.exp
                              (-(1 / 2 : ℝ) *
                                dotProduct (fun i => y k i - θstar.2 i)
                                  (fun i => ∑ j : Fin n, (θstar.1.1⁻¹) i j * (y k j - θstar.2 j)))) := by
                        rw [hStarSimp]
                  _ = Real.log
                        (∏ k : Fin N,
                          ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (Matrix.det R) ^ (-(1 : ℝ) / 2)) *
                            Real.exp
                              (-(1 / 2 : ℝ) *
                                dotProduct (fun i => y k i - a i)
                                  (fun i => ∑ j : Fin n, R⁻¹ i j * (y k j - a j)))) := by
                        symm
                        exact hEqEll
                  _ = (N : ℝ) * Real.log (Real.rpow (2 * Real.pi) (-(n : ℝ) / 2)) -
                        ((N : ℝ) / 2) *
                          (Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) +
                            dotProduct (fun i => μ i - a i)
                              (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j))) := by
                        rw [hRewriteθ]
      have hGapZero : covGap + meanGap = 0 := by
        have hCoeffNe : (N : ℝ) / 2 ≠ 0 := by positivity
        rcases mul_eq_zero.mp hGapScaled with hCoeffZero | hGapZero
        · exact (hCoeffNe hCoeffZero).elim
        · exact hGapZero
      dsimp [covGap, meanGap] at hGapZero
      linarith
    have hCovEq' :
        Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ) =
          Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) := by
      -- Equality of log-likelihoods forces both nonnegative gaps to vanish.
      have hCovUpper :
          Real.log (Matrix.det R) + Matrix.trace (R⁻¹ * Y) ≤
            Real.log (Matrix.det Y) + (Fintype.card (Fin n) : ℝ) := by
        linarith [hGapEq, hMeanLe]
      exact le_antisymm hCovLe hCovUpper
    have hMeanZero :
        dotProduct (fun i => μ i - a i) (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)) = 0 := by
      have hMeanUpper :
          dotProduct (fun i => μ i - a i) (fun i => ∑ j : Fin n, R⁻¹ i j * (μ j - a j)) ≤ 0 := by
        linarith [hGapEq, hCovLe]
      exact le_antisymm hMeanUpper hMeanLe
    have ha : a = μ := by
      -- Vanishing of the centered quadratic form pins down the mean uniquely.
      exact mean_gap_eq_zero_implies_eq hR μ a hMeanZero
    have hReq : R = Y := by
      -- Equality in the covariance gap identifies the covariance matrix.
      exact hCovEq hCovEq'
    -- The two component equalities identify the maximizer uniquely.
    apply Prod.ext
    · apply Subtype.ext
      exact hReq
    · exact ha


end «problem-200»
