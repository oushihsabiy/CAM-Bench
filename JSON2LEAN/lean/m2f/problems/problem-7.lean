import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators
open WithLp

namespace «problem-7»

/-- The frame of eigenvectors corresponding to the last `k` eigenvalues is admissible and realizes
the target product exactly. -/
lemma tail_eigenvector_frame_attains_value
    (n k : ℕ)
    (hkn : k ≤ n)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hXsymm : X.IsSymm) :
    let hXHerm : X.IsHermitian := by
      simpa using hXsymm
    let e : Fin k ↪ Fin n := Fin.natAdd_castLEEmb hkn
    let σ : Fin k ↪ Fin n := {
      toFun := fun j => (Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.cast (by simp) (e j))
      inj' := by
        intro i j hij
        apply e.injective
        have hcast :
            Fin.cast (Fintype.card_fin n).symm (e i) = Fin.cast (Fintype.card_fin n).symm (e j) := by
          simpa using (Fintype.equivOfCardEq (Fintype.card_fin _)).injective hij
        exact Fin.cast_injective (Fintype.card_fin n).symm hcast }
    let V : Matrix (Fin n) (Fin k) ℝ := fun i j => hXHerm.eigenvectorBasis (σ j) i
    V.transpose * V = 1 ∧
      (∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i))) =
        ∏ i : Fin k,
          hXHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)) := by
  classical
  let hXHerm : X.IsHermitian := by
    simpa using hXsymm
  let e : Fin k ↪ Fin n := Fin.natAdd_castLEEmb hkn
  let σ : Fin k ↪ Fin n := {
    toFun := fun j => (Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.cast (by simp) (e j))
    inj' := by
      intro i j hij
      apply e.injective
      have hcast :
          Fin.cast (Fintype.card_fin n).symm (e i) = Fin.cast (Fintype.card_fin n).symm (e j) := by
        simpa using (Fintype.equivOfCardEq (Fintype.card_fin _)).injective hij
      exact Fin.cast_injective (Fintype.card_fin n).symm hcast }
  let V : Matrix (Fin n) (Fin k) ℝ := fun i j => hXHerm.eigenvectorBasis (σ j) i
  refine ⟨?_, ?_⟩
  · -- The columns of `V` are the selected orthonormal eigenvectors.
    have hOrtho : Orthonormal ℝ (fun j : Fin k => hXHerm.eigenvectorBasis (σ j)) :=
      (hXHerm.eigenvectorBasis.orthonormal.comp σ) σ.injective
    ext i j
    -- Translate orthonormality into the matrix identity `Vᵀ V = I`.
    simpa [V, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, eq_comm] using
      (orthonormal_iff_ite.mp hOrtho j i)
  · -- Each quadratic factor reduces to the corresponding eigenvalue on its eigenvector.
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hcol :
        (V · i) = (hXHerm.eigenvectorBasis (σ i) : Fin n → ℝ) := by
      ext a
      simp [V]
    -- Switch to the eigenvector-basis formula for the quadratic value of an eigenvector.
    simpa [hcol, Matrix.IsHermitian.eigenvalues, σ, e] using (hXHerm.eigenvalues_eq (σ i)).symm

/-- The diagonal entry of a compression is the quadratic factor attached to the corresponding
column. -/
lemma compression_diagonal_entry_eq_quadratic_factor
    (n k : ℕ)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (i : Fin k) :
    (V.transpose * X * V) i i = dotProduct (V · i) (X.mulVec (V · i)) := by
  -- Expand the compressed diagonal entry and the matrix-vector product into the same double sum.
  simp only [Matrix.mul_apply, Matrix.mulVec, Matrix.transpose_apply, dotProduct]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- The product of the diagonal entries of a compression is the product of the corresponding
quadratic factors. -/
lemma compression_diagonal_prod_eq_prod_quadratic_factor
    (n k : ℕ)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ) :
    (∏ i : Fin k, (V.transpose * X * V) i i) =
      ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i)) := by
  -- Rewrite each factor using the diagonal-entry identity proved above.
  refine Finset.prod_congr rfl ?_
  intro i hi
  exact compression_diagonal_entry_eq_quadratic_factor n k X V i

/-- An orthonormal frame has an injective synthesis map. -/
lemma orthonormal_frame_mulVec_injective
    (n k : ℕ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (hVorth : V.transpose * V = 1) :
    Function.Injective V.mulVec := by
  intro x y hxy
  -- Apply `Vᵀ` to both sides and simplify using the frame identity `Vᵀ V = I`.
  have hxy' := congrArg (fun z => V.transpose *ᵥ z) hxy
  simpa [Matrix.mulVec_mulVec, hVorth] using hxy'

/-- Every column of an orthonormal frame is nonzero. -/
lemma orthonormal_frame_column_ne_zero
    (n k : ℕ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (hVorth : V.transpose * V = 1)
    (i : Fin k) :
    (V · i) ≠ 0 := by
  -- The `i`th column is the image of the nonzero coordinate vector under the injective synthesis
  -- map attached to the orthonormal frame.
  have hVinj : Function.Injective V.mulVec := orthonormal_frame_mulVec_injective n k V hVorth
  intro hzero
  have hmul : V *ᵥ (Pi.single i (1 : ℝ)) = 0 := by
    simpa [Matrix.mulVec_single_one] using hzero
  have hsingle : (Pi.single i (1 : ℝ) : Fin k → ℝ) = 0 := by
    apply hVinj
    simpa [Matrix.mulVec_zero] using hmul
  have := congrFun hsingle i
  simp at this

/-- Positive definiteness makes each quadratic factor of an orthonormal frame strictly positive. -/
lemma orthonormal_frame_quadratic_factor_pos
    (n k : ℕ)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (hXpd : X.PosDef)
    (hVorth : V.transpose * V = 1)
    (i : Fin k) :
    0 < dotProduct (V · i) (X.mulVec (V · i)) := by
  -- Route correction: isolate the column-nonzero step once so later spectral arguments can reuse
  -- the strict positivity of each frame factor directly.
  exact hXpd.dotProduct_mulVec_pos (orthonormal_frame_column_ne_zero n k V hVorth i)

/-- Compressing a positive-definite matrix along an orthonormal frame preserves positive
definiteness. -/
lemma orthonormal_frame_compression_posDef
    (n k : ℕ)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (hXpd : X.PosDef)
    (hVorth : V.transpose * V = 1) :
    (V.transpose * X * V).PosDef := by
  -- Route correction: use the standard conjugation lemma after proving the frame map is injective.
  have hVinj : Function.Injective V.mulVec := orthonormal_frame_mulVec_injective n k V hVorth
  simpa using hXpd.conjTranspose_mul_mul_same (B := V) hVinj

/-- The complement of the projection onto an orthonormal frame is positive semidefinite. -/
lemma one_sub_mul_transpose_self_posSemidef
    (n k : ℕ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (hVorth : V.transpose * V = 1) :
    Matrix.PosSemidef ((1 : Matrix (Fin n) (Fin n) ℝ) - V * V.transpose) := by
  let P : Matrix (Fin n) (Fin n) ℝ := V * V.transpose
  have hP_sq : P * P = P := by
    -- Route correction: package the standard `VVᵀ` projection argument once so later row-sum
    -- bounds can come from diagonal nonnegativity instead of a bespoke Bessel calculation.
    calc
      P * P = V * (V.transpose * V) * V.transpose := by
        simp only [P, Matrix.mul_assoc]
      _ = V * (1 : Matrix (Fin k) (Fin k) ℝ) * V.transpose := by rw [hVorth]
      _ = P := by simp [P]
  have hP_symm : P.IsSymm := by
    -- The Gram-type projection `VVᵀ` is symmetric by construction.
    change P.transpose = P
    simpa [P] using (transpose_mul V V.transpose)
  have hcomp_eq :
      ((1 : Matrix (Fin n) (Fin n) ℝ) - P) * (((1 : Matrix (Fin n) (Fin n) ℝ) - P)ᴴ) =
        (1 : Matrix (Fin n) (Fin n) ℝ) - P := by
    -- The orthogonal complement projector is again idempotent.
    change ((1 : Matrix (Fin n) (Fin n) ℝ) - P) * (((1 : Matrix (Fin n) (Fin n) ℝ) - P)ᵀ) =
      (1 : Matrix (Fin n) (Fin n) ℝ) - P
    calc
      ((1 : Matrix (Fin n) (Fin n) ℝ) - P) * (((1 : Matrix (Fin n) (Fin n) ℝ) - P)ᵀ)
          = ((1 : Matrix (Fin n) (Fin n) ℝ) - P) * ((1 : Matrix (Fin n) (Fin n) ℝ) - P) := by
              rw [Matrix.transpose_sub, Matrix.transpose_one, hP_symm]
      _ = ((1 : Matrix (Fin n) (Fin n) ℝ) - P) - (((1 : Matrix (Fin n) (Fin n) ℝ) - P) * P) := by
            rw [Matrix.mul_sub, Matrix.mul_one]
      _ = ((1 : Matrix (Fin n) (Fin n) ℝ) - P) - (P - P * P) := by
            rw [Matrix.sub_mul, Matrix.one_mul]
      _ = (1 : Matrix (Fin n) (Fin n) ℝ) - P := by simp [hP_sq]
  -- A projection is a Gram matrix, hence positive semidefinite.
  have hpsd := Matrix.posSemidef_self_mul_conjTranspose ((1 : Matrix (Fin n) (Fin n) ℝ) - P)
  exact hcomp_eq ▸ hpsd

/-- The squared entries of a column of an orthonormal frame sum to one. -/
lemma orthonormal_frame_column_square_sum
    (n k : ℕ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (hVorth : V.transpose * V = 1)
    (i : Fin k) :
    ∑ j : Fin n, V j i ^ 2 = 1 := by
  -- Reading the `i,i` entry of `VᵀV = I` gives the column-mass identity.
  have hdiag := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M i i) hVorth
  simpa [Matrix.mul_apply, pow_two] using hdiag

/-- The squared entries of a row of an orthonormal frame sum to at most one. -/
lemma orthonormal_frame_row_square_sum_le_one
    (n k : ℕ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (hVorth : V.transpose * V = 1)
    (j : Fin n) :
    ∑ i : Fin k, V j i ^ 2 ≤ 1 := by
  let e : Fin n → ℝ := Pi.single j 1
  have hpsd : Matrix.PosSemidef ((1 : Matrix (Fin n) (Fin n) ℝ) - V * V.transpose) :=
    one_sub_mul_transpose_self_posSemidef n k V hVorth
  have hdiag_nonneg :
      0 ≤ dotProduct e (((1 : Matrix (Fin n) (Fin n) ℝ) - V * V.transpose).mulVec e) := by
    -- Evaluate the positive-semidefinite form on the `j`th basis vector.
    exact hpsd.dotProduct_mulVec_nonneg e
  have hdiag_eq :
      dotProduct e (((1 : Matrix (Fin n) (Fin n) ℝ) - V * V.transpose).mulVec e) =
        1 - ∑ i : Fin k, V j i ^ 2 := by
    -- The diagonal entry of `I - VVᵀ` is `1` minus the row square mass.
    simp [e, Matrix.mulVec, Matrix.mul_apply, Matrix.one_apply, dotProduct, Pi.single_apply,
      eq_comm, pow_two]
  linarith [hdiag_nonneg.trans_eq hdiag_eq]

/-- A positive-definite real matrix satisfies Hadamard's determinant bound by the product of its
diagonal entries. -/
lemma posDef_det_le_prod_diag
    (k : ℕ)
    (B : Matrix (Fin k) (Fin k) ℝ)
    (hB : B.PosDef) :
    B.det ≤ ∏ i : Fin k, B i i := by
  classical
  obtain ⟨C, -, hBC⟩ := Matrix.posDef_iff_eq_conjTranspose_mul_self.mp hB
  have hBC' : B = C.transpose * C := by
    simpa using hBC
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k) := ⟨by simp⟩
  let o : Orientation ℝ (EuclideanSpace ℝ (Fin k)) (Fin k) :=
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.orientation
  have hdet_abs : |C.det| ≤ ∏ i : Fin k, ‖toLp (p := 2) (C.transpose i)‖ := by
    -- View the columns of `C` as vectors in Euclidean space and apply the volume-form bound.
    have hvol := o.abs_volumeForm_apply_le (fun i : Fin k => toLp (p := 2) (C.transpose i))
    have hrobust := o.volumeForm_robust' (EuclideanSpace.basisFun (Fin k) ℝ)
      (fun i : Fin k => toLp (p := 2) (C.transpose i))
    have hdet_eq :
        ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis.det
          (fun i : Fin k => toLp (p := 2) (C.transpose i))) = C.det := by
      -- In the standard orthonormal basis, the determinant of the column family is `det C`.
      rw [Module.Basis.det_apply, EuclideanSpace.basisFun_toBasis]
      have hto :
          ((PiLp.basisFun 2 ℝ (Fin k)).toMatrix
            (fun i : Fin k => toLp (p := 2) (C.transpose i))) = C := by
        ext i j
        simp [Module.Basis.toMatrix_apply]
      rw [hto]
    rw [hrobust, hdet_eq] at hvol
    simpa using hvol
  have hnorm_sq :
      ∏ i : Fin k, ‖toLp (p := 2) (C.transpose i)‖ ^ 2 =
        ∏ i : Fin k, (C.transpose * C) i i := by
    -- The squared norm of each column is the corresponding diagonal entry of `Cᵀ C`.
    refine Finset.prod_congr rfl ?_
    intro i hi
    simpa using (inner_matrix_col_col C C i i)
  have hsquare : C.det ^ 2 ≤ (∏ i : Fin k, ‖toLp (p := 2) (C.transpose i)‖) ^ 2 := by
    -- Squaring the absolute-value bound gives the determinant estimate we need.
    nlinarith [abs_le.mp hdet_abs |>.1, abs_le.mp hdet_abs |>.2]
  rw [hBC', Matrix.det_mul, Matrix.det_transpose]
  have hsquare' : C.det * C.det ≤ ∏ i : Fin k, ‖toLp (p := 2) (C.transpose i)‖ ^ 2 := by
    simpa [pow_two, Finset.prod_mul_distrib] using hsquare
  exact hsquare'.trans_eq hnorm_sq

/-- An antitone sequence is maximized on the first `k` entries among all mass vectors with entries
in `[0,1]` and total mass `k`. -/
lemma weighted_sum_le_head_sum_of_unit_interval_mass
    {N k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ N)
    (lam z : Fin N → ℝ)
    (hlam : Antitone lam)
    (hz_nonneg : ∀ i, 0 ≤ z i)
    (hz_le_one : ∀ i, z i ≤ 1)
    (hz_sum : ∑ i, z i = k) :
    ∑ i, lam i * z i ≤ ∑ j : Fin k, lam (Fin.castLE hkn j) := by
  let j0 : Fin k := ⟨k - 1, Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk1) Nat.zero_lt_one⟩
  let t : ℝ := lam (Fin.castLE hkn j0)
  have ht_tail : ∀ i : Fin N, k ≤ i.1 → lam i - t ≤ 0 := by
    intro i hi
    -- Every tail entry lies below the threshold chosen from the `k`th head coordinate.
    have hcast_le : (Fin.castLE hkn j0 : Fin N) ≤ i := by
      change (Fin.castLE hkn j0).1 ≤ i.1
      exact le_trans (Nat.sub_le _ _) hi
    exact sub_nonpos.mpr (hlam hcast_le)
  have hpointwise :
      ∀ i : Fin N,
        (lam i - t) * z i ≤ if hi : i.1 < k then lam i - t else 0 := by
    intro i
    by_cases hi : i.1 < k
    · -- On the head, the coefficient is nonnegative and `z i ≤ 1`.
      have hnonneg : 0 ≤ lam i - t := by
        refine sub_nonneg.mpr ?_
        have hcast_le : i ≤ Fin.castLE hkn j0 := by
          change i.1 ≤ (Fin.castLE hkn j0).1
          exact Nat.le_pred_of_lt hi
        exact hlam hcast_le
      have hmul := mul_le_mul_of_nonneg_left (hz_le_one i) hnonneg
      simpa [hi] using hmul
    · -- On the tail, the coefficient is nonpositive and `z i` is nonnegative.
      have hnonpos : lam i - t ≤ 0 := ht_tail i (Nat.le_of_not_gt hi)
      have hmul : (lam i - t) * z i ≤ 0 := by
        nlinarith [hz_nonneg i, hnonpos]
      simpa [hi] using hmul
  have hsum_pointwise :
      ∑ i, (lam i - t) * z i ≤ ∑ i, if hi : i.1 < k then lam i - t else 0 := by
    exact Finset.sum_le_sum (fun i _ => hpointwise i)
  have hhead_sum :
      (∑ i, if hi : i.1 < k then lam i - t else 0) =
        ∑ j : Fin k, (lam (Fin.castLE hkn j) - t) := by
    -- Reindex the head-only sum along the canonical split `N = k + (N - k)`.
    have hcast :
        (∑ i : Fin N, if hi : i.1 < k then lam i - t else 0) =
          ∑ i : Fin (k + (N - k)),
            if hi : (finCongr (Nat.add_sub_of_le hkn) i).1 < k then
              lam (finCongr (Nat.add_sub_of_le hkn) i) - t
            else 0 := by
      symm
      simpa using
        (Equiv.sum_comp (finCongr (Nat.add_sub_of_le hkn))
          (fun i : Fin N => if hi : i.1 < k then lam i - t else 0))
    rw [hcast, Fin.sum_univ_add]
    have hhead_cast :
        ∀ j : Fin k,
          finCongr (Nat.add_sub_of_le hkn) (Fin.castAdd (N - k) j) = Fin.castLE hkn j := by
      intro j
      ext
      simp [finCongr, Fin.castLE]
    have htail_zero :
        ∀ j : Fin (N - k),
          (if hi : (finCongr (Nat.add_sub_of_le hkn) (Fin.natAdd k j)).1 < k then
              lam (finCongr (Nat.add_sub_of_le hkn) (Fin.natAdd k j)) - t
            else 0) = 0 := by
      intro j
      have hnot : ¬ (finCongr (Nat.add_sub_of_le hkn) (Fin.natAdd k j)).1 < k := by
        change ¬ k + j.1 < k
        omega
      simp [hnot]
    have hfirst :
        (∑ j : Fin k,
          if hi : (finCongr (Nat.add_sub_of_le hkn) (Fin.castAdd (N - k) j)).1 < k then
            lam (finCongr (Nat.add_sub_of_le hkn) (Fin.castAdd (N - k) j)) - t
          else 0) =
          ∑ j : Fin k, (lam (Fin.castLE hkn j) - t) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hlt : (finCongr (Nat.add_sub_of_le hkn) (Fin.castAdd (N - k) j)).1 < k := by
        rw [hhead_cast j]
        exact j.2
      simp [hhead_cast j, hlt]
    have hsecond :
        (∑ j : Fin (N - k),
          if hi : (finCongr (Nat.add_sub_of_le hkn) (Fin.natAdd k j)).1 < k then
            lam (finCongr (Nat.add_sub_of_le hkn) (Fin.natAdd k j)) - t
          else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      exact htail_zero j
    rw [hfirst, hsecond, add_zero]
  have hsum_z : t * (∑ i, z i) = t * k := by
    rw [hz_sum]
  -- Subtract the threshold, control the head by `z i ≤ 1`, and discard the nonpositive tail.
  calc
    ∑ i, lam i * z i = ∑ i, ((lam i - t) * z i + t * z i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    _ = ∑ i, (lam i - t) * z i + t * (∑ i, z i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ ∑ j : Fin k, (lam (Fin.castLE hkn j) - t) + t * k := by
      exact add_le_add (hsum_pointwise.trans_eq hhead_sum) (le_of_eq hsum_z)
    _ = ∑ j : Fin k, lam (Fin.castLE hkn j) := by
      calc
        ∑ j : Fin k, (lam (Fin.castLE hkn j) - t) + t * k
            = (∑ j : Fin k, lam (Fin.castLE hkn j)) - ∑ _ : Fin k, t + t * k := by
                rw [Finset.sum_sub_distrib]
        _ = (∑ j : Fin k, lam (Fin.castLE hkn j)) - k * t + t * k := by simp
        _ = ∑ j : Fin k, lam (Fin.castLE hkn j) := by ring

/-- Taking complements of a boxed mass vector turns the head-control lemma into a tail lower bound
for logarithms of a decreasing positive sequence. -/
lemma tail_log_sum_le_weighted_log_of_unit_interval_mass
    {N k : ℕ} (hkn : k ≤ N)
    (lam z : Fin N → ℝ)
    (hlam : Antitone lam)
    (hlam_pos : ∀ i, 0 < lam i)
    (hz_nonneg : ∀ i, 0 ≤ z i)
    (hz_le_one : ∀ i, z i ≤ 1)
    (hz_sum : ∑ i, z i = k) :
    ∑ j : Fin k, Real.log (lam (Fin.natAdd_castLEEmb hkn j)) ≤
      ∑ i : Fin N, z i * Real.log (lam i) := by
  let w : Fin N → ℝ := fun i => 1 - z i
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    dsimp [w]
    linarith [hz_le_one i]
  have hw_le_one : ∀ i, w i ≤ 1 := by
    intro i
    dsimp [w]
    linarith [hz_nonneg i]
  have hw_sum : ∑ i, w i = N - k := by
    -- The complement mass is exactly the missing amount to reach total mass `N`.
    calc
      ∑ i : Fin N, w i = ∑ i : Fin N, (1 - z i) := by rfl
      _ = ∑ _ : Fin N, (1 : ℝ) - ∑ i : Fin N, z i := by
            rw [Finset.sum_sub_distrib]
      _ = N - k := by simp [hz_sum]
  have hsplit :
      (∑ i : Fin N, Real.log (lam i)) =
        (∑ j : Fin (N - k), Real.log (lam (Fin.castLE (Nat.sub_le N k) j))) +
        ∑ j : Fin k, Real.log (lam (Fin.natAdd_castLEEmb hkn j)) := by
    -- Split the ordered sum into its head and tail pieces.
    have hcast :
        (∑ i : Fin N, Real.log (lam i)) =
          ∑ i : Fin ((N - k) + k), Real.log (lam (finCongr (Nat.sub_add_cancel hkn) i)) := by
      symm
      simpa using
        (Equiv.sum_comp (finCongr (Nat.sub_add_cancel hkn))
          (fun i : Fin N => Real.log (lam i)))
    rw [hcast, Fin.sum_univ_add]
    have hhead_cast :
        ∀ j : Fin (N - k),
          finCongr (Nat.sub_add_cancel hkn) (Fin.castAdd k j) =
            Fin.castLE (Nat.sub_le N k) j := by
      intro j
      ext
      simp [finCongr, Fin.castLE]
    have htail_cast :
        ∀ j : Fin k,
          finCongr (Nat.sub_add_cancel hkn) (Fin.natAdd (N - k) j) =
            Fin.natAdd_castLEEmb hkn j := by
      intro j
      ext
      simp [Fin.natAdd_castLEEmb, Nat.add_comm]
    rw [show (∑ j : Fin (N - k), Real.log (lam (finCongr (Nat.sub_add_cancel hkn)
          (Fin.castAdd k j)))) =
        ∑ j : Fin (N - k), Real.log (lam (Fin.castLE (Nat.sub_le N k) j)) by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [hhead_cast j]]
    rw [show (∑ j : Fin k, Real.log (lam (finCongr (Nat.sub_add_cancel hkn)
          (Fin.natAdd (N - k) j)))) =
        ∑ j : Fin k, Real.log (lam (Fin.natAdd_castLEEmb hkn j)) by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [htail_cast j]]
  by_cases hNk : N - k = 0
  · have hkN : k = N := by omega
    subst k
    have hw_zero : ∀ i, w i = 0 := by
      intro i
      have hsum_zero :
          ∑ i : Fin N, w i = 0 := by
        simpa using hw_sum
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hw_nonneg j).mp hsum_zero i (by simp)
    have hz_one : ∀ i, z i = 1 := by
      intro i
      dsimp [w] at hw_zero
      linarith [hw_zero i]
    -- When `k = N`, the tail is the whole list and every mass must be `1`.
    have hweighted :
        ∑ i : Fin N, z i * Real.log (lam i) = ∑ i : Fin N, Real.log (lam i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hz_one i]
      ring
    have htail_all :
        ∑ j : Fin N, Real.log (lam (Fin.natAdd_castLEEmb (Nat.le_refl N) j)) =
          ∑ i : Fin N, Real.log (lam i) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hnatadd_id : Fin.natAdd_castLEEmb (Nat.le_refl N) j = j := by
        ext
        simp [Fin.natAdd_castLEEmb]
      rw [hnatadd_id]
    rw [htail_all, hweighted]
  · have hk1 : 1 ≤ N - k := Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mpr hNk)
    have hw_sum_nat : ∑ i, w i = ((N - k : ℕ) : ℝ) := by
      calc
        ∑ i, w i = (N : ℝ) - k := hw_sum
        _ = ((N - k : ℕ) : ℝ) := by exact (Nat.cast_sub hkn).symm
    have hlog_antitone : Antitone (fun i : Fin N => Real.log (lam i)) := by
      intro i j hij
      exact Real.log_le_log (hlam_pos j) (hlam hij)
    have hhead_comp :
        ∑ i : Fin N, Real.log (lam i) * w i ≤
          ∑ j : Fin (N - k), Real.log (lam (Fin.castLE (Nat.sub_le N k) j)) := by
      exact weighted_sum_le_head_sum_of_unit_interval_mass hk1 (Nat.sub_le N k)
        (fun i => Real.log (lam i)) w hlog_antitone hw_nonneg hw_le_one hw_sum_nat
    have hweighted_split :
        ∑ i : Fin N, z i * Real.log (lam i) =
          (∑ i : Fin N, Real.log (lam i)) - ∑ i : Fin N, Real.log (lam i) * w i := by
      calc
        ∑ i : Fin N, z i * Real.log (lam i)
            = ∑ i : Fin N, (Real.log (lam i) - Real.log (lam i) * w i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                dsimp [w]
                ring
        _ = (∑ i : Fin N, Real.log (lam i)) - ∑ i : Fin N, Real.log (lam i) * w i := by
              rw [Finset.sum_sub_distrib]
    -- Subtract the complement estimate from the full sum to isolate the tail.
    have htail_total :
        ∑ j : Fin k, Real.log (lam (Fin.natAdd_castLEEmb hkn j)) =
          (∑ i : Fin N, Real.log (lam i)) -
            ∑ j : Fin (N - k), Real.log (lam (Fin.castLE (Nat.sub_le N k) j)) := by
      linarith [hsplit]
    rw [hweighted_split]
    have hsub :
        (∑ i : Fin N, Real.log (lam i)) -
            ∑ j : Fin (N - k), Real.log (lam (Fin.castLE (Nat.sub_le N k) j)) ≤
          (∑ i : Fin N, Real.log (lam i)) -
            ∑ i : Fin N, Real.log (lam i) * w i := by
      exact sub_le_sub_left hhead_comp _
    linarith [htail_total, hsub]

/- [BLOCK Exercise 3.26-(c) | 35 | thm]
Let n ∈ ℕ and let k satisfy 1 ≤ k ≤ n. Let S_{++}^n denote the set of all real symmetric positive
definite n × n matrices. For X ∈ S_{++}^n, let λ_1(X) ≥ λ_2(X) ≥ ·s ≥ λ_n(X) > 0 denote the
eigenvalues of X. Prove that for every X ∈ S_{++}^n,
prod_{i=n-k+1}^{n} λ_i(X)
=
∈f ≤ft{ prod_{i=1}^{k} vᵢ^{T} X vᵢ |dle| V=[v₁\ ·s\ vₖ] ∈ ℝ^{n × k}, V^{T}V=Iₖ },
where Iₖ is the k × k identity matrix.
-/
theorem inf_prod_quadratic_forms_eq_prod_smallest_eigenvalues
    (n k : ℕ)
    (hk1 : 1 ≤ k)
    (hkn : k ≤ n) :
    ∀ X : Matrix (Fin n) (Fin n) ℝ,
      (hXsymm : X.IsSymm) →
      X.PosDef →
      let hXHerm : X.IsHermitian := by
        simpa using hXsymm
      (∏ i : Fin k,
        hXHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i))) =
        sInf
          {r : ℝ |
            ∃ V : Matrix (Fin n) (Fin k) ℝ,
              V.transpose * V = 1 ∧
              r = ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i))} := by
  classical
  intro X hXsymm hXpd
  let hXHerm : X.IsHermitian := by
    simpa using hXsymm
  let e : Fin k ↪ Fin n := Fin.natAdd_castLEEmb hkn
  let S : Set ℝ :=
    {r : ℝ |
      ∃ V : Matrix (Fin n) (Fin k) ℝ,
        V.transpose * V = 1 ∧
        r = ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i))}
  have hFrame := tail_eigenvector_frame_attains_value n k hkn X hXsymm
  have hFrame_mem :
      (∏ i : Fin k,
        hXHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i))) ∈ S := by
    -- The eigenvector frame from the previous lemma gives an explicit feasible point in `S`.
    rcases hFrame with ⟨Vh, hValue⟩
    refine ⟨_, Vh, hValue.symm⟩
  have hS_nonempty : S.Nonempty := ⟨_, hFrame_mem⟩
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨V, hVorth, rfl⟩
    -- Each orthonormal-frame factor is strictly positive, hence nonnegative.
    refine Finset.prod_nonneg fun i _ ↦
      (orthonormal_frame_quadratic_factor_pos n k X V hXpd hVorth i).le
  -- Route correction: the witness side is complete, so the only missing ingredient is now the
  -- universal lower bound for arbitrary feasible frames.
  apply le_antisymm
  · -- The remaining hard direction is the global lower bound over all feasible frames.
    -- Route correction: the determinant detour is no longer the issue; the remaining blocker is
    -- aligning `spectral_theorem`'s arbitrary eigenbasis order with the theorem statement's sorted
    -- `eigenvalues₀` tail.
    refine le_csInf hS_nonempty ?_
    intro r hr
    rcases hr with ⟨V, hVorth, rfl⟩
    let U : Matrix (Fin n) (Fin n) ℝ := hXHerm.eigenvectorUnitary
    let W : Matrix (Fin n) (Fin k) ℝ := U.transpose * V
    let ι := Fin (Fintype.card (Fin n))
    let ρ : ι ≃ Fin n := by
      refine Fintype.equivOfCardEq ?_
      simp [ι]
    let W₀ : Matrix ι (Fin k) ℝ := fun a i => W (ρ a) i
    let lam : ι → ℝ := hXHerm.eigenvalues₀
    let β : ι → ℝ := fun a => ∑ i : Fin k, W₀ a i ^ 2
    have hkn₀ : k ≤ Fintype.card (Fin n) := by simpa using hkn
    have hUorth : U * U.transpose = 1 := by
      -- The eigenvector matrix is orthogonal, so rotating by `Uᵀ` preserves orthonormal frames.
      change (hXHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
          (star hXHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1
      simpa [U] using Unitary.coe_mul_star_self hXHerm.eigenvectorUnitary
    have hWorth : W.transpose * W = 1 := by
      -- The rotated frame still has orthonormal columns.
      calc
        W.transpose * W = V.transpose * (U * U.transpose) * V := by
          simp [W, Matrix.transpose_mul, Matrix.mul_assoc]
        _ = V.transpose * (1 : Matrix (Fin n) (Fin n) ℝ) * V := by rw [hUorth]
        _ = 1 := by simpa [Matrix.mul_assoc] using hVorth
    have hlam : Antitone lam := by
      -- Reindexing the ordered eigenvalue list preserves antitonicity.
      intro a b hab
      simpa [lam] using hXHerm.eigenvalues₀_antitone hab
    have hlam_pos : ∀ a : ι, 0 < lam a := by
      -- Positive definiteness makes every reindexed eigenvalue strictly positive.
      intro a
      have hpos' : 0 < hXHerm.eigenvalues (ρ a) := hXpd.eigenvalues_pos (ρ a)
      have hpos := hpos'
      rw [Matrix.IsHermitian.eigenvalues] at hpos
      have hρa : ρ.symm (ρ a) = a := ρ.symm_apply_apply a
      have hlam_a : 0 < hXHerm.eigenvalues₀ a := hρa ▸ hpos
      simpa [lam] using hlam_a
    have hspec : X = U * Matrix.diagonal hXHerm.eigenvalues * U.transpose := by
      -- This is the real-matrix form of the spectral theorem for `X`.
      simpa [Unitary.conjStarAlgAut_apply, U, Matrix.mul_assoc] using hXHerm.spectral_theorem
    have hquad :
        ∀ i : Fin k, dotProduct (V · i) (X.mulVec (V · i)) = ∑ a : ι, lam a * (W₀ a i) ^ 2 := by
      intro i
      have hcompress :
          V.transpose * X * V = W.transpose * Matrix.diagonal hXHerm.eigenvalues * W := by
        -- Rewrite the compression in the eigenbasis of `X`.
        calc
          V.transpose * X * V
              = V.transpose * (U * Matrix.diagonal hXHerm.eigenvalues * U.transpose) * V := by
                  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => V.transpose * M * V) hspec
          _ = (V.transpose * U) * Matrix.diagonal hXHerm.eigenvalues * (U.transpose * V) := by
                simp [Matrix.mul_assoc]
          _ = W.transpose * Matrix.diagonal hXHerm.eigenvalues * W := by
                simp [W, Matrix.transpose_mul, Matrix.mul_assoc]
      -- Read the `i`th diagonal entry of the rotated diagonal compression.
      calc
        dotProduct (V · i) (X.mulVec (V · i)) = (V.transpose * X * V) i i := by
          symm
          exact compression_diagonal_entry_eq_quadratic_factor n k X V i
        _ = (W.transpose * Matrix.diagonal hXHerm.eigenvalues * W) i i := by rw [hcompress]
        _ = dotProduct (W · i) ((Matrix.diagonal hXHerm.eigenvalues).mulVec (W · i)) := by
          exact compression_diagonal_entry_eq_quadratic_factor n k
            (Matrix.diagonal hXHerm.eigenvalues) W i
        _ = ∑ j : Fin n, hXHerm.eigenvalues j * (W j i) ^ 2 := by
          simp [Matrix.mulVec, Matrix.diagonal, dotProduct, pow_two, mul_assoc, mul_left_comm,
            mul_comm]
        _ = ∑ a : ι, hXHerm.eigenvalues (ρ a) * (W (ρ a) i) ^ 2 := by
          simpa using (Equiv.sum_comp ρ (fun j : Fin n => hXHerm.eigenvalues j * (W j i) ^ 2)).symm
        _ = ∑ a : ι, lam a * (W₀ a i) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          change hXHerm.eigenvalues₀ (ρ.symm (ρ a)) * W (ρ a) i ^ 2 =
            hXHerm.eigenvalues₀ a * W (ρ a) i ^ 2
          rw [ρ.symm_apply_apply]
    have hW₀_col_mass : ∀ i : Fin k, ∑ a : ι, (W₀ a i) ^ 2 = 1 := by
      intro i
      -- Reindexing the rotated column preserves its total square mass.
      calc
        ∑ a : ι, (W₀ a i) ^ 2 = ∑ j : Fin n, (W j i) ^ 2 := by
          simpa [W₀] using (Equiv.sum_comp ρ (fun j : Fin n => (W j i) ^ 2))
        _ = 1 := orthonormal_frame_column_square_sum n k W hWorth i
    have hcol_log :
        ∀ i : Fin k,
          ∑ a : ι, (W₀ a i) ^ 2 * Real.log (lam a) ≤
            Real.log (dotProduct (V · i) (X.mulVec (V · i))) := by
      intro i
      have hjensen :
          ∑ a : ι, (W₀ a i) ^ 2 * Real.log (lam a) ≤
            Real.log (∑ a : ι, (W₀ a i) ^ 2 * lam a) := by
        -- Apply Jensen's inequality to `log` with the column-square weights.
        simpa [smul_eq_mul] using
          (strictConcaveOn_log_Ioi.concaveOn.le_map_sum
            (t := Finset.univ)
            (w := fun a : ι => (W₀ a i) ^ 2)
            (p := lam)
            (h₀ := by
              intro a ha
              exact sq_nonneg (W₀ a i))
            (h₁ := hW₀_col_mass i)
            (hmem := by
              intro a ha
              simpa [Set.mem_Ioi] using hlam_pos a))
      -- Replace the weighted eigenvalue average by the original quadratic factor.
      calc
        ∑ a : ι, (W₀ a i) ^ 2 * Real.log (lam a)
            ≤ Real.log (∑ a : ι, (W₀ a i) ^ 2 * lam a) := hjensen
        _ = Real.log (∑ a : ι, lam a * (W₀ a i) ^ 2) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro a ha
              ring
        _ = Real.log (dotProduct (V · i) (X.mulVec (V · i))) := by rw [hquad i]
    have hβ_nonneg : ∀ a : ι, 0 ≤ β a := by
      intro a
      -- The row masses are sums of squares.
      exact Finset.sum_nonneg fun i hi => sq_nonneg (W₀ a i)
    have hβ_le_one : ∀ a : ι, β a ≤ 1 := by
      intro a
      -- Each rotated row satisfies the orthonormal-frame Bessel bound.
      simpa [β, W₀] using orthonormal_frame_row_square_sum_le_one n k W hWorth (ρ a)
    have hβ_sum : ∑ a : ι, β a = k := by
      -- Swapping the sums shows that the total row mass equals the number of columns.
      calc
        ∑ a : ι, β a = ∑ a : ι, ∑ i : Fin k, (W₀ a i) ^ 2 := by rfl
        _ = ∑ i : Fin k, ∑ a : ι, (W₀ a i) ^ 2 := by rw [Finset.sum_comm]
        _ = ∑ i : Fin k, (1 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hW₀_col_mass i
        _ = k := by simp
    have hswap :
        ∑ i : Fin k, ∑ a : ι, (W₀ a i) ^ 2 * Real.log (lam a) =
          ∑ a : ι, β a * Real.log (lam a) := by
      -- Exchange the finite sums and package the row masses as coefficients.
      calc
        ∑ i : Fin k, ∑ a : ι, (W₀ a i) ^ 2 * Real.log (lam a)
            = ∑ a : ι, ∑ i : Fin k, (W₀ a i) ^ 2 * Real.log (lam a) := by
                rw [Finset.sum_comm]
        _ = ∑ a : ι, β a * Real.log (lam a) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              simp [β, ← Finset.sum_mul]
    have hsum_cols :
        ∑ i : Fin k, ∑ a : ι, (W₀ a i) ^ 2 * Real.log (lam a) ≤
          ∑ i : Fin k, Real.log (dotProduct (V · i) (X.mulVec (V · i))) := by
      -- Sum the columnwise Jensen bounds.
      exact Finset.sum_le_sum fun i hi => hcol_log i
    have htail :
        ∑ i : Fin k, Real.log (lam (Fin.natAdd_castLEEmb hkn₀ i)) ≤
          ∑ a : ι, β a * Real.log (lam a) := by
      -- The row masses satisfy exactly the boxed constraints needed for the tail-log lemma.
      exact tail_log_sum_le_weighted_log_of_unit_interval_mass hkn₀ lam β
        hlam hlam_pos hβ_nonneg hβ_le_one hβ_sum
    have hlog :
        ∑ i : Fin k, Real.log (lam (Fin.natAdd_castLEEmb hkn₀ i)) ≤
          ∑ i : Fin k, Real.log (dotProduct (V · i) (X.mulVec (V · i))) := by
      -- Combine the tail-log majorization with the summed columnwise bounds.
      exact htail.trans <| by simpa [hswap] using hsum_cols
    have hleft_pos : 0 < ∏ i : Fin k, lam (Fin.natAdd_castLEEmb hkn₀ i) := by
      -- The target tail eigenvalue product is strictly positive.
      exact Finset.prod_pos fun i hi => hlam_pos (Fin.natAdd_castLEEmb hkn₀ i)
    have hright_pos :
        0 < ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i)) := by
      -- Every quadratic factor of a feasible frame is strictly positive.
      exact Finset.prod_pos fun i hi =>
        orthonormal_frame_quadratic_factor_pos n k X V hXpd hVorth i
    have hlog_prod :
        Real.log (∏ i : Fin k, lam (Fin.natAdd_castLEEmb hkn₀ i)) ≤
          Real.log (∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i))) := by
      -- Convert the additive logarithmic inequality back into a product inequality.
      rw [Real.log_prod, Real.log_prod]
      · exact hlog
      · intro i hi
        exact (orthonormal_frame_quadratic_factor_pos n k X V hXpd hVorth i).ne'
      · intro i hi
        exact (hlam_pos (Fin.natAdd_castLEEmb hkn₀ i)).ne'
    have hprod :
        ∏ i : Fin k, lam (Fin.natAdd_castLEEmb hkn₀ i) ≤
          ∏ i : Fin k, dotProduct (V · i) (X.mulVec (V · i)) := by
      exact (Real.log_le_log_iff hleft_pos hright_pos).mp hlog_prod
    have htail_eq :
        (∏ i : Fin k, lam (Fin.natAdd_castLEEmb hkn₀ i)) =
          ∏ i : Fin k,
            hXHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      apply congrArg hXHerm.eigenvalues₀
      ext
      simp [Fin.natAdd_castLEEmb]
    rw [htail_eq] at hprod
    exact hprod
  · -- The witness frame shows the infimum is at most the claimed product.
    exact csInf_le hS_bddBelow hFrame_mem

/- [BLOCK Exercise 3.26-(c) | 36 | thm]
Let n ∈ ℕ and let k satisfy 1 ≤ k ≤ n. Let S_{++}^n denote the set of all real symmetric positive
definite n × n matrices. For X ∈ S_{++}^n, let λ_1(X) ≥ λ_2(X) ≥ ·s ≥ λ_n(X) > 0 denote the
eigenvalues of X. Prove that the function
X mapsto sum_{i=n-k+1}^{n} log λ_i(X)
is concave on S_{++}^n, i.e., for all X,Y ∈ S_{++}^n and all θ ∈ [0,1],
sum_{i=n-k+1}^{n} log λ_i(θ X + (1-θ)Y)
≥
θ sum_{i=n-k+1}^{n} log λ_i(X)
+ (1-θ) sum_{i=n-k+1}^{n} log λ_i(Y).
-/
theorem sum_log_smallest_eigenvalues_concave
    (n k : ℕ)
    (hk1 : 1 ≤ k)
    (hkn : k ≤ n) :
    ∀ X Y : Matrix (Fin n) (Fin n) ℝ,
      (hXsymm : X.IsSymm) →
      X.PosDef →
      (hYsymm : Y.IsSymm) →
      Y.PosDef →
      ∀ θ : ℝ,
        0 ≤ θ →
        θ ≤ 1 →
        let hXHerm : X.IsHermitian := by
          simpa using hXsymm
        let hYHerm : Y.IsHermitian := by
          simpa using hYsymm
        let hZSymm : (θ • X + (1 - θ) • Y).IsSymm := by
          simpa [Matrix.IsSymm] using
            (Matrix.IsSymm.add (Matrix.IsSymm.smul hXsymm θ)
              (Matrix.IsSymm.smul hYsymm (1 - θ)))
        let hZHerm : (θ • X + (1 - θ) • Y).IsHermitian := by
          simpa using hZSymm
        (∑ i : Fin k,
          Real.log (hZHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) ≥
          θ *
            (∑ i : Fin k,
              Real.log
                (hXHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) +
            (1 - θ) *
              (∑ i : Fin k,
                Real.log
                  (hYHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) := by
  classical
  intro X Y hXsymm hXpd hYsymm hYpd θ hθ0 hθ1
  let hXHerm : X.IsHermitian := by
    simpa using hXsymm
  let hYHerm : Y.IsHermitian := by
    simpa using hYsymm
  let Z : Matrix (Fin n) (Fin n) ℝ := θ • X + (1 - θ) • Y
  have hZsymm : Z.IsSymm := by
    -- The affine combination of symmetric matrices is symmetric.
    simpa [Z, Matrix.IsSymm] using
      (Matrix.IsSymm.add (Matrix.IsSymm.smul hXsymm θ)
        (Matrix.IsSymm.smul hYsymm (1 - θ)))
  let hZHerm : Z.IsHermitian := by
    simpa [Z] using hZsymm
  have heigenvalues₀_pos :
      ∀ {A : Matrix (Fin n) (Fin n) ℝ},
        A.PosDef → (hAHerm : A.IsHermitian) →
          ∀ j : Fin (Fintype.card (Fin n)), 0 < hAHerm.eigenvalues₀ j := by
    intro A hApd hAHerm j
    let j' : Fin n := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))) j
    have hpos : 0 < hAHerm.eigenvalues j' := by
      simpa [j'] using hApd.eigenvalues_pos j'
    simpa [Matrix.IsHermitian.eigenvalues, j'] using hpos
  suffices
      (∑ i : Fin k,
        Real.log (hZHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) ≥
        θ *
          (∑ i : Fin k,
            Real.log (hXHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) +
          (1 - θ) *
            (∑ i : Fin k,
              Real.log (hYHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) by
    simpa [Z, hXHerm, hYHerm, hZHerm]
  have hZpd : Z.PosDef := by
    -- Positive definiteness survives the convex combination because each quadratic form stays a
    -- convex combination of two strictly positive scalars on nonzero vectors.
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hZHerm ?_
    intro x hx
    have hqx : 0 < dotProduct x (X.mulVec x) := hXpd.dotProduct_mulVec_pos hx
    have hqy : 0 < dotProduct x (Y.mulVec x) := hYpd.dotProduct_mulVec_pos hx
    have hsplit :
        dotProduct x (Z.mulVec x) =
          θ * dotProduct x (X.mulVec x) + (1 - θ) * dotProduct x (Y.mulVec x) := by
      -- Expand `Z` and use bilinearity of matrix multiplication and `dotProduct`.
      simp [Z, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
    change 0 < dotProduct x (Z.mulVec x)
    rw [hsplit]
    have hθ1nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    by_cases hθeq : θ = 0
    · simp [hθeq] at *
      exact hqy
    have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθeq)
    by_cases hθeq1 : θ = 1
    · simp [hθeq1] at *
      exact hqx
    have hθlt1 : θ < 1 := lt_of_le_of_ne hθ1 hθeq1
    have hθ1pos : 0 < 1 - θ := sub_pos.mpr hθlt1
    nlinarith [hqx, hqy, hθpos, hθ1pos]
  let e : Fin k ↪ Fin n := Fin.natAdd_castLEEmb hkn
  let σ : Fin k ↪ Fin n := {
    toFun := fun j => (Fintype.equivOfCardEq (Fintype.card_fin _)) (Fin.cast (by simp) (e j))
    inj' := by
      intro i j hij
      apply e.injective
      have hcast :
          Fin.cast (Fintype.card_fin n).symm (e i) = Fin.cast (Fintype.card_fin n).symm (e j) := by
        simpa using (Fintype.equivOfCardEq (Fintype.card_fin _)).injective hij
      exact Fin.cast_injective (Fintype.card_fin n).symm hcast }
  let V : Matrix (Fin n) (Fin k) ℝ := fun i j => hZHerm.eigenvectorBasis (σ j) i
  have hVframe :
      V.transpose * V = 1 ∧
        (∏ i : Fin k, dotProduct (V · i) (Z.mulVec (V · i))) =
          ∏ i : Fin k,
            hZHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)) := by
    -- Choose the orthonormal frame formed by the eigenvectors of the smallest `k` eigenvalues of
    -- `Z`; this frame realizes the exact tail product.
    simpa [e, σ, V, hZHerm] using tail_eigenvector_frame_attains_value n k hkn Z hZsymm
  have hVorth : V.transpose * V = 1 := hVframe.1
  have hVprod :
      (∏ i : Fin k, dotProduct (V · i) (Z.mulVec (V · i))) =
        ∏ i : Fin k,
          hZHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)) :=
    hVframe.2
  have htail_log_le_frame_log :
      ∀ {A : Matrix (Fin n) (Fin n) ℝ},
        (hAsymm : A.IsSymm) →
        A.PosDef →
        (hAHerm : A.IsHermitian) →
        ∀ (W : Matrix (Fin n) (Fin k) ℝ),
          W.transpose * W = 1 →
          (∑ i : Fin k,
            Real.log (hAHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) ≤
            ∑ i : Fin k, Real.log (dotProduct (W · i) (A.mulVec (W · i))) := by
    intro A hAsymm hApd hAHerm W hWorth
    let S : Set ℝ :=
      {r : ℝ |
        ∃ U : Matrix (Fin n) (Fin k) ℝ,
          U.transpose * U = 1 ∧
          r = ∏ i : Fin k, dotProduct (U · i) (A.mulVec (U · i))}
    have hInfEq :
        (∏ i : Fin k,
          hAHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i))) = sInf S := by
      -- Reuse the previously established variational characterization of the tail product.
      simpa [S, hAHerm] using
        inf_prod_quadratic_forms_eq_prod_smallest_eigenvalues n k hk1 hkn A hAsymm hApd
    have hS_bddBelow : BddBelow S := by
      refine ⟨0, ?_⟩
      intro r hr
      rcases hr with ⟨U, hUorth, rfl⟩
      exact Finset.prod_nonneg fun i _ =>
        (orthonormal_frame_quadratic_factor_pos n k A U hApd hUorth i).le
    have hW_mem : (∏ i : Fin k, dotProduct (W · i) (A.mulVec (W · i))) ∈ S := by
      exact ⟨W, hWorth, rfl⟩
    have hprod_le :
        (∏ i : Fin k,
          hAHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i))) ≤
          ∏ i : Fin k, dotProduct (W · i) (A.mulVec (W · i)) := by
      rw [hInfEq]
      exact csInf_le hS_bddBelow hW_mem
    have hleft_pos :
        0 < ∏ i : Fin k,
          hAHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)) := by
      -- Positive definiteness makes each tail eigenvalue strictly positive.
      exact Finset.prod_pos fun i _ => by
        exact heigenvalues₀_pos hApd hAHerm
          (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i))
    have hlog_prod_le :
        Real.log
            (∏ i : Fin k,
              hAHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i))) ≤
          Real.log (∏ i : Fin k, dotProduct (W · i) (A.mulVec (W · i))) := by
      exact Real.log_le_log hleft_pos hprod_le
    -- Convert the product comparison into the additive log inequality needed by the main proof.
    rw [Real.log_prod, Real.log_prod] at hlog_prod_le
    · exact hlog_prod_le
    · intro i hi
      exact (orthonormal_frame_quadratic_factor_pos n k A W hApd hWorth i).ne'
    · intro i hi
      have hpos :
          0 <
            hAHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)) := by
        exact heigenvalues₀_pos hApd hAHerm
          (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i))
      exact hpos.ne'
  have hframe_log_concave :
      θ * (∑ i : Fin k, Real.log (dotProduct (V · i) (X.mulVec (V · i)))) +
          (1 - θ) * (∑ i : Fin k, Real.log (dotProduct (V · i) (Y.mulVec (V · i)))) ≤
        ∑ i : Fin k, Real.log (dotProduct (V · i) (Z.mulVec (V · i))) := by
    have hpointwise :
        ∀ i : Fin k,
          θ * Real.log (dotProduct (V · i) (X.mulVec (V · i))) +
              (1 - θ) * Real.log (dotProduct (V · i) (Y.mulVec (V · i))) ≤
            Real.log (dotProduct (V · i) (Z.mulVec (V · i))) := by
      intro i
      have hqX :
          0 < dotProduct (V · i) (X.mulVec (V · i)) :=
        orthonormal_frame_quadratic_factor_pos n k X V hXpd hVorth i
      have hqY :
          0 < dotProduct (V · i) (Y.mulVec (V · i)) :=
        orthonormal_frame_quadratic_factor_pos n k Y V hYpd hVorth i
      have hmix :
          θ * Real.log (dotProduct (V · i) (X.mulVec (V · i))) +
              (1 - θ) * Real.log (dotProduct (V · i) (Y.mulVec (V · i))) ≤
            Real.log
              (θ * dotProduct (V · i) (X.mulVec (V · i)) +
                (1 - θ) * dotProduct (V · i) (Y.mulVec (V · i))) := by
        -- Apply scalar concavity of `log` to the two positive quadratic values.
        simpa [Set.mem_Ioi, smul_eq_mul] using
          (strictConcaveOn_log_Ioi.concaveOn.2 hqX hqY hθ0 (sub_nonneg.mpr hθ1)
            (show θ + (1 - θ) = 1 by ring))
      have hsplit :
          dotProduct (V · i) (Z.mulVec (V · i)) =
            θ * dotProduct (V · i) (X.mulVec (V · i)) +
              (1 - θ) * dotProduct (V · i) (Y.mulVec (V · i)) := by
        -- Expand the quadratic form of the affine matrix combination on the fixed frame vector.
        simp [Z, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
      simpa [hsplit] using hmix
    -- Sum the pointwise scalar concavity inequalities over the chosen frame.
    calc
      θ * (∑ i : Fin k, Real.log (dotProduct (V · i) (X.mulVec (V · i)))) +
          (1 - θ) * (∑ i : Fin k, Real.log (dotProduct (V · i) (Y.mulVec (V · i))))
          =
            ∑ i : Fin k,
              (θ * Real.log (dotProduct (V · i) (X.mulVec (V · i))) +
                (1 - θ) * Real.log (dotProduct (V · i) (Y.mulVec (V · i)))) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      _ ≤ ∑ i : Fin k, Real.log (dotProduct (V · i) (Z.mulVec (V · i))) := by
            exact Finset.sum_le_sum fun i _ => hpointwise i
  have hZlog_eq :
      (∑ i : Fin k,
        Real.log (hZHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) =
        ∑ i : Fin k, Real.log (dotProduct (V · i) (Z.mulVec (V · i))) := by
    have hlog_eq :
        Real.log (∏ i : Fin k, dotProduct (V · i) (Z.mulVec (V · i))) =
          Real.log
            (∏ i : Fin k,
              hZHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i))) := by
      exact congrArg Real.log hVprod
    -- Rewrite the exact product identity for the minimizing frame into an equality of log sums.
    rw [Real.log_prod, Real.log_prod] at hlog_eq
    · simpa using hlog_eq.symm
    · intro i hi
      have hpos :
          0 <
            hZHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)) := by
        exact heigenvalues₀_pos hZpd hZHerm
          (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i))
      exact hpos.ne'
    · intro i hi
      exact (orthonormal_frame_quadratic_factor_pos n k Z V hZpd hVorth i).ne'
  have hXlower :
      (∑ i : Fin k,
        Real.log (hXHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) ≤
        ∑ i : Fin k, Real.log (dotProduct (V · i) (X.mulVec (V · i))) :=
    htail_log_le_frame_log hXsymm hXpd hXHerm V hVorth
  have hYlower :
      (∑ i : Fin k,
        Real.log (hYHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) ≤
        ∑ i : Fin k, Real.log (dotProduct (V · i) (Y.mulVec (V · i))) :=
    htail_log_le_frame_log hYsymm hYpd hYHerm V hVorth
  have htail_to_frame :
      θ *
          (∑ i : Fin k,
            Real.log (hXHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) +
        (1 - θ) *
          (∑ i : Fin k,
            Real.log (hYHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) ≤
        θ * (∑ i : Fin k, Real.log (dotProduct (V · i) (X.mulVec (V · i)))) +
          (1 - θ) * (∑ i : Fin k, Real.log (dotProduct (V · i) (Y.mulVec (V · i)))) := by
    -- Scale the two variational lower bounds by the nonnegative coefficients `θ` and `1 - θ`.
    exact add_le_add
      (mul_le_mul_of_nonneg_left hXlower hθ0)
      (mul_le_mul_of_nonneg_left hYlower (sub_nonneg.mpr hθ1))
  -- Chain the exact frame identity, scalar log concavity on that frame, and the variational lower
  -- bounds for `X` and `Y`.
  calc
    (∑ i : Fin k,
      Real.log (hZHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) =
        ∑ i : Fin k, Real.log (dotProduct (V · i) (Z.mulVec (V · i))) := hZlog_eq
    _ ≥ θ * (∑ i : Fin k, Real.log (dotProduct (V · i) (X.mulVec (V · i)))) +
          (1 - θ) * (∑ i : Fin k, Real.log (dotProduct (V · i) (Y.mulVec (V · i)))) :=
        hframe_log_concave
    _ ≥ θ *
          (∑ i : Fin k,
            Real.log (hXHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) +
        (1 - θ) *
          (∑ i : Fin k,
            Real.log (hYHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.natAdd_castLEEmb hkn i)))) :=
        htail_to_frame

end «problem-7»
