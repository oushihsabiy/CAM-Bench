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

namespace «problem-50»
/- [BLOCK Exercise 2.26-(a) | 30 | thm]
Let Y and Z be real symmetric matrices of the same size. For symmetric matrices A and B, A preceq B
means that B-A is positive semidefinite, and A prec B means that B-A is positive definite. Prove the
following auxiliary claim: if 0 prec Y preceq Z, then det Y ≤ det Z.
-/
open Matrix

/-- The determinant of `1 + Cᴴ * C` is at least `1`. -/
lemma det_one_add_conjTranspose_mul_self_ge_one
    {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n ℝ) :
    1 ≤ (1 + Cᴴ * C).det := by
  -- Rewrite `1 + Cᴴ * C` as a functional calculus of the Hermitian Gram matrix.
  have hcfc : 1 + Cᴴ * C = cfc (fun x : ℝ => x + 1) (Cᴴ * C) := by
    symm
    calc
      cfc (fun x : ℝ => x + 1) (Cᴴ * C) = cfc (fun x : ℝ => x) (Cᴴ * C) + 1 :=
        cfc_add_const (R := ℝ) 1 (fun x : ℝ => x) (Cᴴ * C)
          (ha := by simpa using (isHermitian_conjTranspose_mul_self C))
      _ = Cᴴ * C + 1 := by
        rw [cfc_id' (R := ℝ) (Cᴴ * C) (ha := by
          simpa using (isHermitian_conjTranspose_mul_self C))]
      _ = 1 + Cᴴ * C := by simp [add_comm]
  -- Evaluate the determinant on the eigenvalues and bound each factor below by `1`.
  rw [hcfc, (isHermitian_conjTranspose_mul_self C).cfc_eq]
  simp only [IsHermitian.cfc, det_map, det_diagonal, Function.comp_apply]
  refine Finset.one_le_prod (s := Finset.univ)
    (f := fun i : n => ((isHermitian_conjTranspose_mul_self C).eigenvalues i : ℝ) + 1) ?_
  intro i
  have hi := eigenvalues_conjTranspose_mul_self_nonneg (A := C) i
  linarith

/-- Normal form for adding a Gram term after factoring an invertible Cholesky-type factor. -/
lemma conjTranspose_square_plus_gram_normal_form
    {n : Type*} [Fintype n] [DecidableEq n]
    (B Y Z S C : Matrix n n ℝ)
    (hBunit : IsUnit B)
    (hYeq : Y = Bᴴ * B)
    (hZY : Z - Y = Sᴴ * S)
    (hC : C = S * B⁻¹) :
    Z = Bᴴ * (1 + Cᴴ * C) * B := by
  -- Cancel the inverse of `B` inside `C * B` using invertibility of `B`.
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det (A := B)).mp hBunit
  have hCB : C * B = S := by
    calc
      C * B = (S * B⁻¹) * B := by rw [hC]
      _ = S * (B⁻¹ * B) := by rw [Matrix.mul_assoc]
      _ = S := by rw [Matrix.nonsing_inv_mul B hBdet, Matrix.mul_one]
  -- Rewrite the Gram correction through the product `C * B = S`.
  have hGram : Bᴴ * (Cᴴ * C) * B = Sᴴ * S := by
    calc
      Bᴴ * (Cᴴ * C) * B = Bᴴ * (Cᴴ * (C * B)) := by simp [Matrix.mul_assoc]
      _ = (C * B)ᴴ * (C * B) := by rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Sᴴ * S := by simp [hCB]
  have hZY' : Z - Bᴴ * B = Sᴴ * S := by simpa [hYeq] using hZY
  have hZsplit : Z = Bᴴ * B + Sᴴ * S := by
    have : Z = Sᴴ * S + Bᴴ * B := sub_eq_iff_eq_add.mp hZY'
    simpa [add_comm] using this
  -- Factor the common `Bᴴ` and `B` terms to reach the normal form.
  calc
    Z = Bᴴ * B + Sᴴ * S := hZsplit
    _ = Bᴴ * B + Bᴴ * (Cᴴ * C) * B := by rw [hGram]
    _ = Bᴴ * (1 + Cᴴ * C) * B := by
      calc
        Bᴴ * B + Bᴴ * (Cᴴ * C) * B = Bᴴ * B + Bᴴ * ((Cᴴ * C) * B) := by
          rw [Matrix.mul_assoc]
        _ = Bᴴ * (B + (Cᴴ * C) * B) := by rw [Matrix.mul_add]
        _ = Bᴴ * ((1 + Cᴴ * C) * B) := by rw [Matrix.add_mul, one_mul]
        _ = Bᴴ * (1 + Cᴴ * C) * B := by rw [Matrix.mul_assoc]

theorem det_le_of_posDef_and_loewner
    {n : Type*} [Fintype n] [DecidableEq n]
    (Y Z : Matrix n n ℝ)
    (hYsymm : Y.IsSymm)
    (hZsymm : Z.IsSymm)
    (hpos : Y.PosDef)
    (hYZ : (Z - Y).PosSemidef) :
    Y.det ≤ Z.det := by
  -- Route correction: factor the positive definite part and the Loewner slack into Gram terms,
  -- then compare determinants through the normal form `Bᴴ * (1 + Cᴴ * C) * B`.
  obtain ⟨B, hBunit, hYeq⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hpos.isStrictlyPositive
  obtain ⟨S, hZYeq⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hYZ.nonneg
  let C : Matrix n n ℝ := S * B⁻¹
  let _ := hYsymm
  let _ := hZsymm
  have hZeq : Z = Bᴴ * (1 + Cᴴ * C) * B := by
    exact conjTranspose_square_plus_gram_normal_form B Y Z S C hBunit hYeq hZYeq rfl
  have hdetC : 1 ≤ (1 + Cᴴ * C).det := det_one_add_conjTranspose_mul_self_ge_one C
  have hdetY : Y.det = B.det * B.det := by
    -- Compute the determinant of the positive definite factorization of `Y`.
    have hstar : (star B).det = B.det := by
      rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
      simp
    rw [hYeq, Matrix.det_mul, hstar]
  have hdetZ : Z.det = (1 + Cᴴ * C).det * (B.det * B.det) := by
    -- Compute the determinant of the normalized expression for `Z`.
    rw [hZeq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    simp
    ring_nf
  -- Compare both determinants after extracting the common nonnegative square factor.
  rw [hdetY, hdetZ]
  have hsq : 0 ≤ B.det * B.det := mul_self_nonneg B.det
  have hmul := mul_le_mul_of_nonneg_right hdetC hsq
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

end «problem-50»
