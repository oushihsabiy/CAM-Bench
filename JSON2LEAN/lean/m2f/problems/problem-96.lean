import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open scoped ComplexOrder
open Filter
open scoped BigOperators

namespace «problem-96»

/- [BLOCK Exercise 6.14-(d) | 19 | thm]
Let z₁, ..., zₙ ∈ ℂ be distinct and satisfy |zₖ| > 1 for k = 1, ..., n.
Define
F = {f : ℂ → ℂ | f is analytic on {z ∈ ℂ : |z| > 1}
and Re f(z) ≥ 0 for all |z| > 1}.
Define
K_PR = {y ∈ ℂ^n | ∃ f ∈ F such that f(zₖ) = yₖ, k = 1, ..., n}.
For y = (y₁, ..., yₙ) ∈ ℂ^n, define the Pick matrix P(y) by
P(y)_{kl} = (yₖ + conjugate(y_l)) / (zₖ * conjugate(z_l) - 1).
Prove that K_PR is exactly the set of y such that P(y) is positive semidefinite.
-/
/-- Points in the exterior disk invert into the open unit disk. -/
lemma norm_inv_lt_one_of_one_lt_norm {z : ℂ} (hz : 1 < ‖z‖) : ‖z⁻¹‖ < 1 := by
  -- Rewrite the norm of the inverse and apply the ordered inverse inequality on `ℝ`.
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ hz

/-- A point outside the closed unit disk is nonzero. -/
lemma ne_zero_of_one_lt_norm {z : ℂ} (hz : 1 < ‖z‖) : z ≠ 0 := by
  -- A zero point would have norm `0`, contradicting the strict lower bound `1 < ‖z‖`.
  apply norm_ne_zero_iff.mp
  linarith

/-- Exterior-disk nodes give nonvanishing Pick denominators. -/
lemma exterior_pick_denominator_ne_zero
    {n : ℕ} {z : Fin n → ℂ}
    (hz_unit : ∀ k : Fin n, 1 < ‖z k‖) (k l : Fin n) :
    z k * star (z l) - 1 ≠ 0 := by
  -- If the denominator vanished, its norm would be both `1` and strictly larger than `1`.
  intro hzero
  have hEq : z k * star (z l) = 1 := sub_eq_zero.mp hzero
  have hnormEq : ‖z k * star (z l)‖ = 1 := by
    calc
      ‖z k * star (z l)‖ = ‖(1 : ℂ)‖ := by rw [hEq]
      _ = 1 := by norm_num
  have hk : 1 < ‖z k‖ := hz_unit k
  have hl : 1 < ‖z l‖ := hz_unit l
  have hmul : 1 < ‖z k‖ * ‖z l‖ := by
    nlinarith
  have hnormMul : 1 < ‖z k * star (z l)‖ := by
    simpa [norm_mul, norm_star] using hmul
  linarith

/-- Inverted exterior-disk nodes give nonvanishing unit-disk Pick denominators. -/
lemma disk_pick_denominator_ne_zero
    {n : ℕ} {z : Fin n → ℂ}
    (hz_unit : ∀ k : Fin n, 1 < ‖z k‖) (k l : Fin n) :
    1 - (z k)⁻¹ * star (z l)⁻¹ ≠ 0 := by
  -- If the inverted denominator vanished, the unit-disk product would have norm `1`,
  -- contradicting the fact that both inverted nodes have norm strictly smaller than `1`.
  intro hzero
  have hEq : (z k)⁻¹ * star (z l)⁻¹ = 1 := by
    exact (sub_eq_zero.mp hzero).symm
  have hk : ‖(z k)⁻¹‖ < 1 := by
    -- Each inverted node lies strictly inside the unit disk.
    exact norm_inv_lt_one_of_one_lt_norm (hz_unit k)
  have hl : ‖(z l)⁻¹‖ < 1 := by
    -- The same bound holds for the second node.
    exact norm_inv_lt_one_of_one_lt_norm (hz_unit l)
  have hmul : ‖(z k)⁻¹‖ * ‖(z l)⁻¹‖ < 1 := by
    -- Multiplying two nonnegative numbers that are each `< 1` keeps the product `< 1`.
    exact mul_lt_one_of_nonneg_of_lt_one_right hk.le (norm_nonneg _) hl
  have hprod_eq : ‖(z k)⁻¹‖ * ‖(z l)⁻¹‖ = 1 := by
    -- The vanishing hypothesis forces the same product of norms to be exactly `1`.
    calc
      ‖(z k)⁻¹‖ * ‖(z l)⁻¹‖ = ‖(z k)⁻¹ * star (z l)⁻¹‖ := by simp
      _ = ‖(1 : ℂ)‖ := by rw [hEq]
      _ = 1 := by norm_num
  rw [hprod_eq] at hmul
  norm_num at hmul

/-- The exterior Pick kernel is the inverted unit-disk kernel scaled by the diagonal factors. -/
lemma exterior_pick_kernel_entry_eq_inverted_disk_kernel
    {n : ℕ} {z y : Fin n → ℂ}
    (hz_unit : ∀ k : Fin n, 1 < ‖z k‖) (k l : Fin n) :
    (y k + star (y l)) / (z k * star (z l) - 1) =
      (z k)⁻¹ * (((y k + star (y l)) / (1 - (z k)⁻¹ * star (z l)⁻¹))) * star (z l)⁻¹ := by
  -- Route correction: instead of the unavailable complex `PosSemidef` API, rewrite the scalar
  -- kernel entry directly as a diagonal scaling of the unit-disk kernel entry.
  have hk0 : z k ≠ 0 := ne_zero_of_one_lt_norm (hz_unit k)
  have hl0 : z l ≠ 0 := ne_zero_of_one_lt_norm (hz_unit l)
  have hfactor_exterior : z k * star (z l) - 1 = (z k - star (z l)⁻¹) * star (z l) := by
    -- Peel off the outer denominator as a linear factor in `z k`.
    have hone : (1 : ℂ) = star (z l)⁻¹ * star (z l) := by
      simpa using (inv_mul_cancel₀ (star_ne_zero.mpr hl0)).symm
    calc
      z k * star (z l) - 1 = z k * star (z l) - (star (z l)⁻¹ * star (z l)) := by rw [hone]
      _ = (z k - star (z l)⁻¹) * star (z l) := by ring
  have hfactor_disk : 1 - (z k)⁻¹ * star (z l)⁻¹ = (z k - star (z l)⁻¹) * (z k)⁻¹ := by
    -- The inverted denominator factors through the same linear term.
    calc
      1 - (z k)⁻¹ * star (z l)⁻¹ = (z k * (z k)⁻¹) - (z k)⁻¹ * star (z l)⁻¹ := by
        rw [mul_inv_cancel₀ hk0]
      _ = (z k - star (z l)⁻¹) * (z k)⁻¹ := by ring
  -- After factoring both denominators, the desired identity is a commutative-field simplification.
  rw [hfactor_exterior, hfactor_disk]
  simp [div_eq_mul_inv, mul_left_comm, mul_comm, hk0]

/-- Inversion preserves distinctness of the interpolation nodes. -/
lemma inverted_nodes_injective
    {n : ℕ} {z : Fin n → ℂ} (hz_distinct : Function.Injective z) :
    Function.Injective (fun k : Fin n => (z k)⁻¹) := by
  -- Undo inversion on both sides and fall back to the original injectivity hypothesis.
  intro k l hkl
  apply hz_distinct
  exact inv_inj.mp hkl

/-- For complex matrices, the explicit Hermitian quadratic-form condition is equivalent to
positive semidefiniteness in `ComplexOrder`. -/
lemma complex_matrix_condition_iff_posSemidef
    {n : Type*} [Fintype n] (P : Matrix n n ℂ) :
    (P.IsHermitian ∧
      ∀ x : n → ℂ, 0 ≤ Complex.re (dotProduct (fun i => star (x i)) (P.mulVec x))) ↔
      P.PosSemidef := by
  constructor
  · intro hP
    -- Promote the explicit real-part inequality to complex-order nonnegativity using that
    -- Hermitian quadratic forms are self-adjoint scalars.
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hP.1 ?_
    intro x
    have himag : Complex.im (star x ⬝ᵥ P.mulVec x) = 0 :=
      hP.1.im_star_dotProduct_mulVec_self x
    have hself : IsSelfAdjoint (star x ⬝ᵥ P.mulVec x) :=
      (Complex.im_eq_zero_iff_isSelfAdjoint _).mp himag
    exact (Complex.re_nonneg_iff_nonneg hself).mp (hP.2 x)
  · intro hP
    -- Forgetting back to real parts is immediate from complex-order nonnegativity.
    refine ⟨hP.1, ?_⟩
    intro x
    exact (RCLike.nonneg_iff.mp (hP.dotProduct_mulVec_nonneg x)).1

/-- A unit-disk witness pulls back along inversion to an exterior-disk witness. -/
private theorem disk_witness_implies_exterior_witness
    {n : ℕ} {z y : Fin n → ℂ} :
    (∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g {u : ℂ | ‖u‖ < 1} ∧
      (∀ u : ℂ, ‖u‖ < 1 → 0 ≤ Complex.re (g u)) ∧
      ∀ k : Fin n, g ((z k)⁻¹) = y k) →
    (∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f {w : ℂ | 1 < ‖w‖} ∧
      (∀ w : ℂ, 1 < ‖w‖ → 0 ≤ Complex.re (f w)) ∧
      ∀ k : Fin n, f (z k) = y k) := by
  -- Pull the unit-disk witness back by inversion on the exterior domain.
  rintro ⟨g, hg_analytic, hg_re, hg_nodes⟩
  refine ⟨fun w => g (w⁻¹), ?_, ?_, ?_⟩
  · -- Restrict the analytic inverse map to the exterior disk, then compose with `g`.
    have hinv :
        AnalyticOnNhd ℂ (fun w : ℂ => w⁻¹) {w : ℂ | 1 < ‖w‖} := by
      refine analyticOnNhd_inv.mono ?_
      intro w hw
      exact ne_zero_of_one_lt_norm hw
    have hmaps :
        Set.MapsTo (fun w : ℂ => w⁻¹) {w : ℂ | 1 < ‖w‖} {u : ℂ | ‖u‖ < 1} := by
      intro w hw
      exact norm_inv_lt_one_of_one_lt_norm hw
    simpa using hg_analytic.comp hinv hmaps
  · -- The positivity condition transports directly through the norm inequality for inversion.
    intro w hw
    exact hg_re (w⁻¹) (norm_inv_lt_one_of_one_lt_norm hw)
  · -- At the interpolation nodes, inversion cancels and recovers the prescribed values.
    intro k
    simpa [inv_inv] using hg_nodes k

/-- A complex number with nonnegative real part cannot equal `-1`. -/
lemma add_one_ne_zero_of_re_nonneg {u : ℂ} (hu : 0 ≤ Complex.re u) : u + 1 ≠ 0 := by
  -- If `u + 1 = 0`, then `u = -1`, contradicting the nonnegativity of the real part.
  intro hu1
  have hu_neg_one : u = (-1 : ℂ) := eq_neg_iff_add_eq_zero.mpr hu1
  have : 0 ≤ (-1 : ℝ) := by simpa [hu_neg_one] using hu
  norm_num at this

/-- The Cayley transform turns the transformed positive-real Pick matrix into the usual Schur
Pick matrix, up to an invertible diagonal congruence and a positive scalar factor. -/
private theorem positive_real_pick_posSemidef_iff_schur_pick_posSemidef
    {n : ℕ} (z y : Fin n → ℂ)
    (hz_unit : ∀ k : Fin n, 1 < ‖z k‖)
    (hy1 : ∀ k : Fin n, y k + 1 ≠ 0) :
    (let w : Fin n → ℂ := fun k => (z k)⁻¹
     let Q : Matrix (Fin n) (Fin n) ℂ :=
       fun k l : Fin n => (y k + star (y l)) / (1 - w k * star (w l))
     Q.PosSemidef) ↔
    (let w : Fin n → ℂ := fun k => (z k)⁻¹
     let σ : Fin n → ℂ := fun k => (y k - 1) / (y k + 1)
     let S : Matrix (Fin n) (Fin n) ℂ :=
       fun k l : Fin n => (1 - σ k * star (σ l)) / (1 - w k * star (w l))
     S.PosSemidef) := by
  -- Compare the two Pick matrices after conjugating `Q` by the diagonal matrix of `(y k + 1)⁻¹`.
  let w : Fin n → ℂ := fun k => (z k)⁻¹
  let Q : Matrix (Fin n) (Fin n) ℂ :=
    fun k l : Fin n => (y k + star (y l)) / (1 - w k * star (w l))
  let σ : Fin n → ℂ := fun k => (y k - 1) / (y k + 1)
  let S : Matrix (Fin n) (Fin n) ℂ :=
    fun k l : Fin n => (1 - σ k * star (σ l)) / (1 - w k * star (w l))
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun k => (y k + 1)⁻¹
  have hD_unit : IsUnit D := by
    -- Each diagonal entry is nonzero because the interpolation values avoid `-1`.
    rw [show D = Matrix.diagonal (fun k => (y k + 1)⁻¹) by rfl]
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro k
    refine isUnit_iff_ne_zero.mpr ?_
    exact inv_ne_zero (hy1 k)
  have hS_eq :
      S = (2 : ℂ) • (D * Q * Dᴴ) := by
    -- Entrywise, this is the standard Cayley-transform identity.
    ext k l
    have hk : y k + 1 ≠ 0 := hy1 k
    have hl : y l + 1 ≠ 0 := hy1 l
    have hstarl : star (y l + 1) ≠ 0 := by
      simpa using star_ne_zero.mpr hl
    have hden : 1 - w k * star (w l) ≠ 0 := by
      simpa [w] using disk_pick_denominator_ne_zero hz_unit k l
    have hD_entry :
        (D * Q * Dᴴ) k l =
          (y k + 1)⁻¹ * Q k l * star ((y l + 1)⁻¹) := by
      -- Diagonal multiplication isolates the row and column factors.
      rw [show Dᴴ = Matrix.diagonal (fun i => star ((y i + 1)⁻¹)) by
        ext i j <;> simp [D]]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp [D]
    rw [hD_entry, Q, S, σ]
    field_simp [hk, hl, hstarl, hden]
    ring
  have hDQ_psd_iff : (D * Q * Dᴴ).PosSemidef ↔ Q.PosSemidef := by
    -- Positive semidefiniteness is invariant under conjugation by an invertible matrix.
    simpa using (Matrix.IsUnit.posSemidef_star_right_conjugate_iff (U := D) (x := Q) hD_unit)
  have hS_psd_iff : S.PosSemidef ↔ (D * Q * Dᴴ).PosSemidef := by
    constructor
    · intro hS
      -- Multiply by the positive scalar `1 / 2` to undo the normalization in `hS_eq`.
      have hhalf : (0 : ℂ) ≤ (1 / 2 : ℂ) := by norm_num
      simpa [hS_eq, smul_smul] using hS.smul hhalf
    · intro hDQ
      -- Multiply back by the positive scalar `2`.
      have htwo : (0 : ℂ) ≤ (2 : ℂ) := by norm_num
      simpa [hS_eq] using hDQ.smul htwo
  -- Combining the conjugation invariance and the scalar rescaling gives the desired equivalence.
  change Q.PosSemidef ↔ S.PosSemidef
  exact hDQ_psd_iff.symm.trans hS_psd_iff.symm

/-- The remaining analytic content is the Schur-class interpolation theorem for the Cayley
transformed data on the unit disk. -/
private theorem exterior_positive_real_interpolation_iff_transformed_disk_schur_pick_psd
    {n : ℕ} (z y : Fin n → ℂ)
    (hz_distinct : Function.Injective z)
    (hz_unit : ∀ k : Fin n, 1 < ‖z k‖)
    (hy1 : ∀ k : Fin n, y k + 1 ≠ 0) :
    (∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f {w : ℂ | 1 < ‖w‖} ∧
      (∀ w : ℂ, 1 < ‖w‖ → 0 ≤ Complex.re (f w)) ∧
      ∀ k : Fin n, f (z k) = y k) ↔
    (let w : Fin n → ℂ := fun k => (z k)⁻¹
     let σ : Fin n → ℂ := fun k => (y k - 1) / (y k + 1)
     let S : Matrix (Fin n) (Fin n) ℂ :=
       fun k l : Fin n => (1 - σ k * star (σ l)) / (1 - w k * star (w l))
     S.PosSemidef) := by
  -- Route correction: the missing ingredient is no longer a positive-real Pick theorem.
  -- The remaining blocker is the finite Schur interpolation theorem for the Cayley-transformed
  -- disk data, together with the removable-singularity bridge from the exterior witness.
  -- TODO: prove the exterior-to-disk Cayley transport and the finite Schur interpolation theorem,
  -- then convert the Schur Pick matrix back to the positive-real Pick matrix via the lemma above.
  sorry

/-- The remaining missing ingredient is now isolated to the Schur interpolation step on the disk. -/
private theorem exterior_positive_real_interpolation_iff_transformed_disk_pick_psd
    {n : ℕ} (z y : Fin n → ℂ)
    (hz_distinct : Function.Injective z)
    (hz_unit : ∀ k : Fin n, 1 < ‖z k‖) :
    (∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f {w : ℂ | 1 < ‖w‖} ∧
      (∀ w : ℂ, 1 < ‖w‖ → 0 ≤ Complex.re (f w)) ∧
      ∀ k : Fin n, f (z k) = y k) ↔
    (let w : Fin n → ℂ := fun k => (z k)⁻¹
     let Q : Matrix (Fin n) (Fin n) ℂ :=
       fun k l : Fin n => (y k + star (y l)) / (1 - w k * star (w l))
     Q.PosSemidef) := by
  classical
  by_cases hy1 : ∀ k : Fin n, y k + 1 ≠ 0
  · -- In the generic case, reduce to the Schur Pick matrix for the Cayley-transformed values.
    have hSchur :
        (∃ f : ℂ → ℂ,
          AnalyticOnNhd ℂ f {w : ℂ | 1 < ‖w‖} ∧
          (∀ w : ℂ, 1 < ‖w‖ → 0 ≤ Complex.re (f w)) ∧
          ∀ k : Fin n, f (z k) = y k) ↔
        (let w : Fin n → ℂ := fun k => (z k)⁻¹
         let σ : Fin n → ℂ := fun k => (y k - 1) / (y k + 1)
         let S : Matrix (Fin n) (Fin n) ℂ :=
           fun k l : Fin n => (1 - σ k * star (σ l)) / (1 - w k * star (w l))
         S.PosSemidef) :=
      exterior_positive_real_interpolation_iff_transformed_disk_schur_pick_psd
        z y hz_distinct hz_unit hy1
    have hMatrix :
        (let w : Fin n → ℂ := fun k => (z k)⁻¹
         let Q : Matrix (Fin n) (Fin n) ℂ :=
           fun k l : Fin n => (y k + star (y l)) / (1 - w k * star (w l))
         Q.PosSemidef) ↔
        (let w : Fin n → ℂ := fun k => (z k)⁻¹
         let σ : Fin n → ℂ := fun k => (y k - 1) / (y k + 1)
         let S : Matrix (Fin n) (Fin n) ℂ :=
           fun k l : Fin n => (1 - σ k * star (σ l)) / (1 - w k * star (w l))
         S.PosSemidef) :=
      positive_real_pick_posSemidef_iff_schur_pick_posSemidef z y hz_unit hy1
    exact hSchur.trans hMatrix.symm
  · -- If some target value is `-1`, both sides are impossible.
    push_neg at hy1
    rcases hy1 with ⟨k, hk⟩
    have hyk : y k = (-1 : ℂ) := eq_neg_iff_add_eq_zero.mpr hk
    constructor
    · rintro ⟨f, _hf_analytic, hf_re, hf_nodes⟩
      -- Evaluating the positivity condition at the offending node contradicts `y k = -1`.
      have hy_nonneg : 0 ≤ Complex.re (y k) := by
        simpa [hf_nodes k] using hf_re (z k) (hz_unit k)
      have : 0 ≤ (-1 : ℝ) := by simpa [hyk] using hy_nonneg
      norm_num at this
    · intro hQ
      -- A positive semidefinite matrix cannot have the negative diagonal entry forced by `y k = -1`.
      let w : Fin n → ℂ := fun i => (z i)⁻¹
      let Q : Matrix (Fin n) (Fin n) ℂ :=
        fun i j : Fin n => (y i + star (y j)) / (1 - w i * star (w j))
      change Q.PosSemidef at hQ
      have hwk : ‖w k‖ < 1 := by
        simpa [w] using norm_inv_lt_one_of_one_lt_norm (hz_unit k)
      have hdiag_nonneg : 0 ≤ Complex.re (Q k k) := by
        exact (RCLike.nonneg_iff.mp (hQ.diag_nonneg)).1
      have hden_eq : (1 - w k * star (w k) : ℂ) = (1 - ‖w k‖ ^ 2 : ℝ) := by
        calc
          (1 - w k * star (w k) : ℂ) = (1 - Complex.normSq (w k) : ℝ) := by
            simp [Complex.mul_conj]
          _ = (1 - ‖w k‖ ^ 2 : ℝ) := by
            simp [Complex.normSq_eq_norm_sq]
      have hdiag_eq : Q k k = (((-2 : ℝ) / (1 - ‖w k‖ ^ 2)) : ℂ) := by
        rw [Q, hyk, hden_eq]
        norm_num
      have hsq_lt : ‖w k‖ ^ 2 < 1 := by
        nlinarith [hwk]
      rw [hdiag_eq] at hdiag_nonneg
      norm_num at hdiag_nonneg
      nlinarith

theorem positive_real_interpolation_iff_psd_pick_matrix
    {n : ℕ} (z y : Fin n → ℂ)
    (hz_distinct : Function.Injective z)
    (hz_unit : ∀ k : Fin n, 1 < ‖z k‖) :
    (∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f {w : ℂ | 1 < ‖w‖} ∧
      (∀ w : ℂ, 1 < ‖w‖ → 0 ≤ Complex.re (f w)) ∧
      ∀ k : Fin n, f (z k) = y k) ↔
    (let P : Matrix (Fin n) (Fin n) ℂ :=
      fun k l : Fin n => (y k + star (y l)) / (z k * star (z l) - 1)
     P.IsHermitian ∧
       ∀ x : Fin n → ℂ,
         0 ≤ Complex.re (dotProduct (fun i => star (x i)) (P.mulVec x))) := by
  -- Route correction: the matrix side does admit a clean `PosSemidef` reformulation once we work
  -- in the scoped complex order, so we reduce the explicit quadratic condition to that API first.
  have hz_inv : ∀ k : Fin n, ‖(z k)⁻¹‖ < 1 := by
    -- Inversion carries each interpolation node from the exterior disk into the unit disk.
    intro k
    exact norm_inv_lt_one_of_one_lt_norm (hz_unit k)
  have hdenom : ∀ k l : Fin n, z k * star (z l) - 1 ≠ 0 := by
    -- The Pick kernel is algebraically well-defined at all interpolation nodes.
    intro k l
    exact exterior_pick_denominator_ne_zero hz_unit k l
  have hdiskDenom : ∀ k l : Fin n, 1 - (z k)⁻¹ * star (z l)⁻¹ ≠ 0 := by
    -- The inverted unit-disk kernel is also well-defined at all interpolation nodes.
    intro k l
    exact disk_pick_denominator_ne_zero hz_unit k l
  have hkernelTransport :
      ∀ k l : Fin n,
        (y k + star (y l)) / (z k * star (z l) - 1) =
          (z k)⁻¹ * (((y k + star (y l)) / (1 - (z k)⁻¹ * star (z l)⁻¹))) * star (z l)⁻¹ := by
    -- This is the entrywise diagonal-congruence identity between the exterior and disk kernels.
    intro k l
    exact exterior_pick_kernel_entry_eq_inverted_disk_kernel hz_unit k l
  let w : Fin n → ℂ := fun k => (z k)⁻¹
  have hw_distinct : Function.Injective w := by
    -- Inversion preserves pairwise distinctness of the interpolation nodes.
    simpa [w] using inverted_nodes_injective hz_distinct
  have hw_unit : ∀ k : Fin n, ‖w k‖ < 1 := by
    -- The transformed interpolation nodes lie in the open unit disk.
    intro k
    simpa [w] using hz_inv k
  let Q : Matrix (Fin n) (Fin n) ℂ :=
    fun k l : Fin n => (y k + star (y l)) / (1 - w k * star (w l))
  let P : Matrix (Fin n) (Fin n) ℂ :=
    fun k l : Fin n => (y k + star (y l)) / (z k * star (z l) - 1)
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal w
  have hQ_transport :
      ∀ k l : Fin n,
        P k l = w k * Q k l * star (w l) := by
    -- Rewrite the kernel transport identity in the notation of the transformed nodes `w`.
    intro k l
    simpa [w, Q, P] using hkernelTransport k l
  have hP_eq : P = D * Q * Dᴴ := by
    -- The exterior Pick matrix is the diagonal congruence of the inverted disk Pick matrix.
    ext k l
    calc
      P k l = w k * Q k l * star (w l) := by
        simpa [P] using hQ_transport k l
      _ = (D * Q * Dᴴ) k l := by
        rw [show Dᴴ = Matrix.diagonal (star w) by simp [D]]
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
        rfl
  have hD_unit : IsUnit D := by
    -- The diagonal congruence matrix is invertible because every exterior node is nonzero.
    rw [show D = Matrix.diagonal w by rfl]
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro k
    refine isUnit_iff_ne_zero.mpr ?_
    simp [w, ne_zero_of_one_lt_norm (hz_unit k)]
  have hP_psd_iff : P.PosSemidef ↔ Q.PosSemidef := by
    -- Positive semidefiniteness is invariant under conjugation by an invertible diagonal matrix.
    rw [hP_eq]
    change (D * Q * star D).PosSemidef ↔ Q.PosSemidef
    simpa using (Matrix.IsUnit.posSemidef_star_right_conjugate_iff (U := D) (x := Q) hD_unit)
  have hMatrixSide :
      (let P : Matrix (Fin n) (Fin n) ℂ :=
        fun k l : Fin n => (y k + star (y l)) / (z k * star (z l) - 1)
       P.IsHermitian ∧
         ∀ x : Fin n → ℂ,
           0 ≤ Complex.re (dotProduct (fun i => star (x i)) (P.mulVec x))) ↔
      Q.PosSemidef := by
    -- This packages the original right-hand side as the positivity of the transformed disk matrix.
    change (P.IsHermitian ∧
        ∀ x : Fin n → ℂ,
          0 ≤ Complex.re (dotProduct (fun i => star (x i)) (P.mulVec x))) ↔
      Q.PosSemidef
    rw [complex_matrix_condition_iff_posSemidef]
    exact hP_psd_iff
  suffices
      (∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f {w : ℂ | 1 < ‖w‖} ∧
        (∀ w : ℂ, 1 < ‖w‖ → 0 ≤ Complex.re (f w)) ∧
        ∀ k : Fin n, f (z k) = y k) ↔
      Q.PosSemidef by
    -- Once the analytic side is transported to the unit disk theorem, the matrix side is done.
    exact Iff.trans this hMatrixSide.symm
  -- The matrix reduction above isolates the remaining analytic content as a transformed disk theorem.
  simpa [Q, w] using
    exterior_positive_real_interpolation_iff_transformed_disk_pick_psd z y hz_distinct hz_unit

end «problem-96»
