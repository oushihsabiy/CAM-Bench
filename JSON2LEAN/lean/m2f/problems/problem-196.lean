import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-196»

/- [BLOCK Exercise 15.2-(c) | 5 | thm]
Let n ∈ ℕ with n ≥ 1. Let W ∈ S^n satisfy w_{ij} ≥ 0 for all i,j and w_{ii}=0 for i=1,dots,n, where
S^n is the set of real symmetric n × n matrices. Let 1 ∈ ℝ^n be the all-one vector, and for v ∈
ℝ^n, let diag(v) be the diagonal matrix with diagonal entries v₁,dots,vₙ. Define L(W) = -W +
diag(W1). Prove the standard SDP reformulation for algebraic connectivity:
inf_{x ⟂ 1, ‖x‖₂ = 1} xᵀLx = sup { t | L - t(I - (1/n)11ᵀ) ⪰ 0 }.
-/
set_option maxHeartbeats 400000 in
theorem eigenvalue_minimization_sdp_reformulation {n : ℕ} (hn : 2 ≤ n)
    (W : Matrix (Fin n) (Fin n) ℝ)
    (hW_symm : Wᵀ = W)
    (hW_nonneg : ∀ i j, 0 ≤ W i j)
    (hW_diag : ∀ i : Fin n, W i i = 0) :
    let one : Fin n → ℝ := fun _ => 1
    let L : Matrix (Fin n) (Fin n) ℝ :=
      -W + Matrix.diagonal (fun i => ∑ j : Fin n, W i j * one j)
    sInf {r : ℝ | ∃ x : Fin n → ℝ,
      (∑ i : Fin n, x i) = 0 ∧
      (∑ i : Fin n, x i ^ 2) = 1 ∧
      r = ∑ i : Fin n, ∑ j : Fin n, x i * L i j * x j} =
    sSup {t : ℝ |
      Matrix.PosSemidef
        (L - t • ((1 : Matrix (Fin n) (Fin n) ℝ) -
          ((1 / (n : ℝ)) • Matrix.vecMulVec one one)))} := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  let one : Fin (2 + k) → ℝ := fun _ => 1
  let d : Fin (2 + k) → ℝ := fun i => ∑ j : Fin (2 + k), W i j * one j
  let L : Matrix (Fin (2 + k)) (Fin (2 + k)) ℝ := -W + Matrix.diagonal d
  let P : Matrix (Fin (2 + k)) (Fin (2 + k)) ℝ :=
    (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) ℝ) -
      ((1 / (2 + k : ℝ)) • Matrix.vecMulVec one one)
  let q : Matrix (Fin (2 + k)) (Fin (2 + k)) ℝ → (Fin (2 + k) → ℝ) → ℝ :=
    fun M x => Matrix.toLinearMap₂' ℝ M x x
  let S : Set ℝ := {r : ℝ | ∃ x : Fin (2 + k) → ℝ,
    (∑ i : Fin (2 + k), x i) = 0 ∧
    (∑ i : Fin (2 + k), x i ^ 2) = 1 ∧
    r = q L x}
  let T : Set ℝ := {t : ℝ | Matrix.PosSemidef (L - t • P)}
  have hk_pos_nat : 0 < 2 + k := by omega
  have hk_pos : (0 : ℝ) < (2 + k : ℝ) := by positivity
  have hk_ne : (2 + k : ℝ) ≠ 0 := by positivity
  have hW_apply : ∀ i j : Fin (2 + k), W j i = W i j := by
    intro i j
    simpa [Matrix.transpose_apply] using congr_fun₂ hW_symm i j
  have hW_isSymm : W.IsSymm := Matrix.IsSymm.ext hW_apply
  have hL_diag_sub : L = Matrix.diagonal d - W := by
    ext i j
    simp [L, sub_eq_add_neg, add_comm]
  -- Symmetric real matrices are Hermitian, which is the matrix-side condition for PSD.
  have symmetric_to_hermitian :
      ∀ {M : Matrix (Fin (2 + k)) (Fin (2 + k)) ℝ}, M.IsSymm → M.IsHermitian := by
    intro M hM
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hM.eq
  -- This is the bilinear algebra identity used whenever we shift by the centering matrix.
  have quadratic_form_sub_smul :
      ∀ (M N : Matrix (Fin (2 + k)) (Fin (2 + k)) ℝ) (x : Fin (2 + k) → ℝ) (a : ℝ),
        q (M - a • N) x = q M x - a * q N x := by
    intro M N x a
    have h :
        Matrix.toLinearMap₂' ℝ (M - a • N) x x =
          Matrix.toLinearMap₂' ℝ M x x - a * Matrix.toLinearMap₂' ℝ N x x := by
      simp [Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Finset.mul_sum,
        sub_eq_add_neg, mul_left_comm]
    simpa [q] using h
  -- This is the scaling rule needed for the normalization step in the reverse implication.
  have quadratic_form_smul :
      ∀ (M : Matrix (Fin (2 + k)) (Fin (2 + k)) ℝ) (x : Fin (2 + k) → ℝ) (a : ℝ),
        q M (a • x) = a ^ 2 * q M x := by
    intro M x a
    have h :
        Matrix.toLinearMap₂' ℝ M (a • x) (a • x) =
          a ^ 2 * Matrix.toLinearMap₂' ℝ M x x := by
      simp [Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Finset.mul_sum, sq,
        mul_left_comm]
      ring_nf
    simpa [q] using h
  -- Route correction: the robust path is to express the Laplacian quadratic form as a sum of
  -- weighted squares, rather than to search for a spectral API.
  have weighted_laplacian_quadratic_form :
      ∀ x : Fin (2 + k) → ℝ,
        q L x = (∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * (x i - x j) ^ 2) / 2 := by
    intro x
    -- First rewrite the quadratic form into a row-sum term minus the off-diagonal coupling term.
    have hquadratic :
        q L x =
          (∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * x i ^ 2) -
            (∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * (x i * x j)) := by
      have hsub :
          Matrix.mulVec (Matrix.diagonal d - W) x = (fun i => d i * x i) - Matrix.mulVec W x := by
        ext i
        change (((fun j => Matrix.diagonal d i j) - fun j => W i j) ⬝ᵥ x) =
          ((fun i => d i * x i) - Matrix.mulVec W x) i
        rw [sub_dotProduct]
        congr
        · simp [d, one]
      change Matrix.toLinearMap₂' ℝ L x x = _
      rw [hL_diag_sub, Matrix.toLinearMap₂'_apply']
      rw [hsub, dotProduct_sub]
      congr
      · simpa [dotProduct, d, one, Finset.mul_sum, sq, mul_assoc, mul_left_comm, mul_comm]
      · simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm]
    -- Next use symmetry to replace the second copy of the diagonal part by the swapped version.
    have hswap :
        (∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * x j ^ 2) =
          ∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * x i ^ 2 := by
      calc
        (∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * x j ^ 2)
            = ∑ j : Fin (2 + k), ∑ i : Fin (2 + k), W i j * x j ^ 2 := by
                rw [Finset.sum_comm]
        _ = ∑ j : Fin (2 + k), ∑ i : Fin (2 + k), W j i * x j ^ 2 := by
              congr 1 with j
              congr 1 with i
              rw [show W i j = W j i by
                simpa [Matrix.transpose_apply] using congr_fun₂ hW_symm j i]
        _ = ∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * x i ^ 2 := by
              rfl
    -- Finally expand `(x i - x j)^2` pointwise and reassemble the two double sums.
    have hsum_expand :
        ((∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * x i ^ 2) -
            (∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * (x i * x j))) +
          ((∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * x j ^ 2) -
            (∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * (x i * x j))) =
          ∑ i : Fin (2 + k), ∑ j : Fin (2 + k),
            (W i j * x i ^ 2 - W i j * (x i * x j) +
              (W i j * x j ^ 2 - W i j * (x i * x j))) := by
      calc
        ((∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * x i ^ 2) -
              (∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * (x i * x j))) +
            ((∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * x j ^ 2) -
              (∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * (x i * x j)))
            = ∑ i : Fin (2 + k),
                (((∑ j : Fin (2 + k), W i j * x i ^ 2) -
                    (∑ j : Fin (2 + k), W i j * (x i * x j))) +
                  ((∑ j : Fin (2 + k), W i j * x j ^ 2) -
                    (∑ j : Fin (2 + k), W i j * (x i * x j)))) := by
                rw [sub_eq_add_neg, sub_eq_add_neg, ← Finset.sum_neg_distrib,
                  ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                congr 1 with i
        _ = ∑ i : Fin (2 + k), ∑ j : Fin (2 + k),
              (W i j * x i ^ 2 - W i j * (x i * x j) +
                (W i j * x j ^ 2 - W i j * (x i * x j))) := by
              congr 1 with i
              rw [sub_eq_add_neg, sub_eq_add_neg, ← Finset.sum_neg_distrib,
                ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              congr 1 with j
    have hsquare_expand :
        (∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * (x i - x j) ^ 2) =
          ∑ i : Fin (2 + k), ∑ j : Fin (2 + k),
            (W i j * x i ^ 2 - W i j * (x i * x j) +
              (W i j * x j ^ 2 - W i j * (x i * x j))) := by
      congr
      congr 1 with i
      congr 1 with j
      ring
    have htwice :
        (∑ i : Fin (2 + k), ∑ j : Fin (2 + k), W i j * (x i - x j) ^ 2) = 2 * q L x := by
      nlinarith [hquadratic, hswap, hsum_expand, hsquare_expand]
    linarith
  -- The weighted Laplacian is PSD because it is a sum of nonnegative weighted squares.
  have hL_symm : L.IsSymm := by
    have hdiag_symm : (Matrix.diagonal d).IsSymm := Matrix.isSymm_diagonal d
    rw [hL_diag_sub]
    exact hdiag_symm.sub hW_isSymm
  have hL_hermitian : L.IsHermitian := symmetric_to_hermitian hL_symm
  have weighted_laplacian_posSemidef : Matrix.PosSemidef L := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hL_hermitian ?_
    intro x
    have hnonneg : 0 ≤ q L x := by
      rw [weighted_laplacian_quadratic_form]
      refine div_nonneg ?_ (by positivity)
      refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
      exact mul_nonneg (hW_nonneg i j) (sq_nonneg (x i - x j))
    simpa [q, Matrix.toLinearMap₂'_apply'] using hnonneg
  -- This computes the quadratic form of the centering projector.
  have centering_matrix_quadratic_form :
      ∀ x : Fin (2 + k) → ℝ,
        q P x = (∑ i : Fin (2 + k), x i ^ 2) -
          ((∑ i : Fin (2 + k), x i) ^ 2) / (2 + k : ℝ) := by
    intro x
    have hsub : Matrix.mulVec P x = x - (1 / (2 + k : ℝ)) • fun _ => ∑ i : Fin (2 + k), x i := by
      have hvec : Matrix.mulVec (Matrix.vecMulVec one one) x = fun _ => ∑ i : Fin (2 + k), x i := by
        ext i
        simp [Matrix.mulVec, Matrix.vecMulVec, one, dotProduct]
      ext i
      change (((fun j => (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) ℝ) i j) -
          fun j => ((1 / (2 + k : ℝ)) • Matrix.vecMulVec one one) i j) ⬝ᵥ x) =
        x i - (1 / (2 + k : ℝ)) * (∑ i : Fin (2 + k), x i)
      rw [sub_dotProduct]
      congr
      · simp [dotProduct, Matrix.one_apply]
      · have hscaled :=
          congrArg (fun t : ℝ => (1 / (2 + k : ℝ)) * t) (congr_fun hvec i)
        simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
          using hscaled
    change Matrix.toLinearMap₂' ℝ P x x = _
    rw [Matrix.toLinearMap₂'_apply', hsub, dotProduct_sub]
    simp [dotProduct, sq]
    have hsum_mul :
        (∑ i : Fin (2 + k), x i * (((2 + k : ℝ)⁻¹) * (∑ j : Fin (2 + k), x j))) =
          ((((2 + k : ℝ)⁻¹) * (∑ j : Fin (2 + k), x j))) * (∑ j : Fin (2 + k), x j) := by
      symm
      simpa [mul_comm] using
        (Finset.mul_sum (s := Finset.univ)
          (a := (((2 + k : ℝ)⁻¹) * (∑ j : Fin (2 + k), x j))) (f := x))
    rw [hsum_mul]
    ring_nf
  -- Centering subtracts the mean, so the centered vector has zero sum.
  have centered_vector_sum :
      ∀ (x : Fin (2 + k) → ℝ) (μ : ℝ) (z : Fin (2 + k) → ℝ),
        μ = (∑ i : Fin (2 + k), x i) / (2 + k : ℝ) →
        z = (fun i => x i - μ) →
        (∑ i : Fin (2 + k), z i) = 0 := by
    intro x μ z hμ hz
    subst hμ hz
    simp [Finset.sum_sub_distrib, Finset.sum_const]
    field_simp [hk_ne]
    ring
  -- This upgrades the projector formula from a variance identity to the centered norm identity.
  have centering_matrix_centered_quadratic_form :
      ∀ (x : Fin (2 + k) → ℝ) (μ : ℝ) (z : Fin (2 + k) → ℝ),
        μ = (∑ i : Fin (2 + k), x i) / (2 + k : ℝ) →
        z = (fun i => x i - μ) →
        q P x = ∑ i : Fin (2 + k), z i ^ 2 := by
    intro x μ z hμ hz
    have hzsum : (∑ i : Fin (2 + k), z i) = 0 := centered_vector_sum x μ z hμ hz
    have hx : x = z + μ • one := by
      ext i
      subst hz
      simp [one]
    have hzvec : Matrix.mulVec P x = z := by
      subst hμ hz
      have hvec : Matrix.mulVec (Matrix.vecMulVec one one) x = fun _ => ∑ i : Fin (2 + k), x i := by
        ext i
        simp [Matrix.mulVec, Matrix.vecMulVec, one, dotProduct]
      ext i
      change (((fun j => (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) ℝ) i j) -
          fun j => ((1 / (2 + k : ℝ)) • Matrix.vecMulVec one one) i j) ⬝ᵥ x) =
        x i - ((∑ i : Fin (2 + k), x i) / (2 + k : ℝ))
      rw [sub_dotProduct]
      congr
      · simp [dotProduct, Matrix.one_apply]
      · have hscaled :=
          congrArg (fun t : ℝ => (1 / (2 + k : ℝ)) * t) (congr_fun hvec i)
        simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm,
          div_eq_mul_inv] using hscaled
    change Matrix.toLinearMap₂' ℝ P x x = _
    rw [Matrix.toLinearMap₂'_apply', hzvec, hx, add_dotProduct, smul_dotProduct]
    simp [dotProduct, one, hzsum, sq]
  -- Subtracting a constant vector does not change the Laplacian quadratic form.
  have weighted_laplacian_centering_invariance :
      ∀ (x : Fin (2 + k) → ℝ) (μ : ℝ) (z : Fin (2 + k) → ℝ),
        z = (fun i => x i - μ) →
        q L x = q L z := by
    intro x μ z hz
    rw [weighted_laplacian_quadratic_form x, weighted_laplacian_quadratic_form z]
    subst hz
    congr
    congr 1 with i
    congr 1 with j
    ring
  have hP_symm : P.IsSymm := by
    have houter_symm : (Matrix.vecMulVec one one).IsSymm := by
      refine Matrix.IsSymm.ext ?_
      intro i j
      simp [Matrix.vecMulVec, one, mul_comm]
    exact Matrix.isSymm_one.sub (houter_symm.smul (1 / (2 + k : ℝ)))
  have hP_hermitian : P.IsHermitian := symmetric_to_hermitian hP_symm
  -- The Rayleigh-quotient set is nonempty; we use the standard `(+1,-1,0,...) / √2` witness.
  have rayleigh_set_nonempty : S.Nonempty := by
    have hk_swap : 2 + k = k + 2 := by omega
    let x0 : Fin (k + 2) → ℝ :=
      Fin.cons (1 / Real.sqrt 2) (Fin.cons (-(1 / Real.sqrt 2)) (fun _ : Fin k => 0))
    let e : Fin (2 + k) ≃ Fin (k + 2) := finCongr hk_swap
    let x : Fin (2 + k) → ℝ := fun i => x0 (e i)
    refine ⟨q L x, x, ?_, ?_, rfl⟩
    · have hxsum : (∑ i : Fin (2 + k), x i) = ∑ j : Fin (k + 2), x0 j := by
        simpa [x] using
          (Fintype.sum_equiv e x x0 (by intro i; rfl))
      rw [hxsum]
      have hxsum0 : (∑ i : Fin (k + 2), x0 i) = 0 := by
        simp [x0, Fin.sum_univ_succ]
      exact hxsum0
    · have hsqrt2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
      have hxnorm : (∑ i : Fin (2 + k), x i ^ 2) = ∑ j : Fin (k + 2), x0 j ^ 2 := by
        simpa [x] using
          (Fintype.sum_equiv e (fun i => x i ^ 2) (fun j => x0 j ^ 2) (by intro i; rfl))
      rw [hxnorm]
      have hxnorm0 : (∑ i : Fin (k + 2), x0 i ^ 2) = 1 := by
        simp [x0, Fin.sum_univ_succ, hsqrt2]
        norm_num
      exact hxnorm0
  -- The weighted square formula also gives a uniform lower bound `0` on the feasible set.
  have rayleigh_set_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨x, -, -, rfl⟩
    have hnonneg := weighted_laplacian_posSemidef.dotProduct_mulVec_nonneg x
    simpa [q, Matrix.toLinearMap₂'_apply'] using hnonneg
  -- This is the main identification: the SDP-feasible shifts are exactly the lower bounds of `S`.
  have sdp_set_eq_lowerBounds : T = lowerBounds S := by
    ext t
    constructor
    · intro ht
      intro r hr
      rcases hr with ⟨x, hxsum, hxnorm, rfl⟩
      have hnonneg : 0 ≤ q (L - t • P) x := by
        simpa [q, Matrix.toLinearMap₂'_apply'] using ht.dotProduct_mulVec_nonneg x
      have hqP : q P x = 1 := by
        rw [centering_matrix_quadratic_form]
        simp [hxsum, hxnorm]
      rw [quadratic_form_sub_smul L P x t, hqP] at hnonneg
      linarith
    · intro ht
      have hLP_symm : (L - t • P).IsSymm := hL_symm.sub (hP_symm.smul t)
      have hLP_hermitian : (L - t • P).IsHermitian := symmetric_to_hermitian hLP_symm
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hLP_hermitian ?_
      intro x
      -- Center the arbitrary test vector and then normalize the nonzero case.
      let μ : ℝ := (∑ i : Fin (2 + k), x i) / (2 + k : ℝ)
      let z : Fin (2 + k) → ℝ := fun i => x i - μ
      have hzsum : (∑ i : Fin (2 + k), z i) = 0 := centered_vector_sum x μ z rfl rfl
      have hqP : q P x = ∑ i : Fin (2 + k), z i ^ 2 := centering_matrix_centered_quadratic_form x μ z rfl rfl
      have hqL : q L x = q L z := weighted_laplacian_centering_invariance x μ z rfl
      have hquadratic_nonneg : 0 ≤ q (L - t • P) x := by
        by_cases hzzero : (∑ i : Fin (2 + k), z i ^ 2) = 0
        · -- If the centered norm vanishes, then the centered vector is zero, so the form vanishes.
          have hzsq_each :
              ∀ i : Fin (2 + k), z i ^ 2 = 0 := by
            have hsum_zero :=
              (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (z i)).mp hzzero
            intro i
            exact hsum_zero i (Finset.mem_univ i)
          have hz_zero : z = 0 := by
            funext i
            exact sq_eq_zero_iff.mp (hzsq_each i)
          have hqLz : q L z = 0 := by
            simp [q, hz_zero, Matrix.toLinearMap₂'_apply']
          rw [quadratic_form_sub_smul L P x t, hqL, hqP, hzzero, hqLz]
          simpa using (show (0 : ℝ) ≤ 0 by positivity)
        · -- Otherwise, normalize the centered vector and use the lower-bound hypothesis on `S`.
          have hzpos : 0 < ∑ i : Fin (2 + k), z i ^ 2 := by
            exact lt_of_le_of_ne (by positivity) (Ne.symm hzzero)
          let s : ℝ := Real.sqrt (∑ i : Fin (2 + k), z i ^ 2)
          let u : Fin (2 + k) → ℝ := s⁻¹ • z
          have hspos : 0 < s := by
            simpa [s] using Real.sqrt_pos.mpr hzpos
          have hu_sum : (∑ i : Fin (2 + k), u i) = 0 := by
            simpa [u, Finset.mul_sum] using congrArg (fun r : ℝ => s⁻¹ * r) hzsum
          have hu_norm : (∑ i : Fin (2 + k), u i ^ 2) = 1 := by
            have hu_scale :
                (∑ i : Fin (2 + k), u i ^ 2) = s⁻¹ ^ 2 * (∑ i : Fin (2 + k), z i ^ 2) := by
              have h :
                  (∑ i : Fin (2 + k), (s⁻¹ • z) i ^ 2) =
                    s⁻¹ ^ 2 * (∑ i : Fin (2 + k), z i ^ 2) := by
                simp [sq, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
              simpa [u] using h
            have hs_scale : s⁻¹ ^ 2 * (∑ i : Fin (2 + k), z i ^ 2) = 1 := by
              have hs2 : s ^ 2 = ∑ i : Fin (2 + k), z i ^ 2 := by
                simpa [s] using
                  (Real.sq_sqrt (show (0 : ℝ) ≤ ∑ i : Fin (2 + k), z i ^ 2 by positivity))
              field_simp [hspos.ne']
              nlinarith [hs2]
            rw [hu_scale, hs_scale]
          have hu_mem : q L u ∈ S := ⟨u, hu_sum, hu_norm, rfl⟩
          have ht_le : t ≤ q L u := ht hu_mem
          have hz_eq : z = s • u := by
            ext i
            simp [u, s, hspos.ne']
          have hs2 : s ^ 2 = ∑ i : Fin (2 + k), z i ^ 2 := by
            simpa [s] using
              (Real.sq_sqrt (show (0 : ℝ) ≤ ∑ i : Fin (2 + k), z i ^ 2 by positivity))
          have hcore : 0 ≤ q L z - t * (∑ i : Fin (2 + k), z i ^ 2) := by
            have hscaled0 : q L z = s ^ 2 * q L u := by
              simpa [hz_eq] using quadratic_form_smul L u s
            have hscaled : q L z = (∑ i : Fin (2 + k), z i ^ 2) * q L u := by
              rw [hscaled0, hs2]
            have hfactor_nonneg :
                0 ≤ (∑ i : Fin (2 + k), z i ^ 2) * (q L u - t) := by
              exact mul_nonneg hzpos.le (sub_nonneg.mpr ht_le)
            nlinarith [hscaled, hfactor_nonneg]
          rw [quadratic_form_sub_smul L P x t, hqL, hqP]
          linarith
      simpa [q, Matrix.toLinearMap₂'_apply'] using hquadratic_nonneg
  -- Finish by replacing the SDP set with the lower-bounds set and invoking the lattice theorem.
  have hmain : sInf S = sSup T := by
    rw [sdp_set_eq_lowerBounds,
      (csSup_lowerBounds_eq_csInf rayleigh_set_bddBelow rayleigh_set_nonempty).symm]
  simpa [S, T, q, P, L, d, one, Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec,
    Finset.mul_sum, mul_assoc]
    using hmain

end «problem-196»
