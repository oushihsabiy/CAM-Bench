import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-159»

/- [BLOCK Exercise 16.12 | 15 | thm]
Let H ∈ ℝ^{n×n}. Let Z ∈ ℝ^{n × k} have full column rank, and assume that its columns form a basis
of a k-dimensional null space. Assume that Zᵀ H Z is invertible, and define P = Z(Zᵀ H Z)^{-1}Zᵀ.
Show that P is independent of the choice of basis Z for this null space. In particular, any such
basis Z can be written as Z = QB, where Q ∈ ℝ^{n × k} has orthonormal columns spanning the same null
space, so QᵀQ = Iₖ, and B ∈ ℝ^{k × k} is nonsingular.
-/
open Matrix

/-- Expanding the reduced Hessian after the basis change `Z = Q * B` isolates the square factor `B`
on both sides of `Qᵀ * H * Q`. -/
lemma basis_change_hessian_factorization
    {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    (H : Matrix n n ℝ) (Q : Matrix n k ℝ) (B : Matrix k k ℝ) :
    (Q * B)ᵀ * H * (Q * B) = Bᵀ * (Qᵀ * H * Q) * B := by
  -- Expand the transpose of the product and reassociate the matrix multiplications.
  rw [Matrix.transpose_mul]
  simp [Matrix.mul_assoc]

/-- Conjugating by an invertible basis-change matrix does not alter the nonsingular inverse
sandwich. -/
lemma basis_change_inverse_sandwich
    {k : Type*} [Fintype k] [DecidableEq k]
    (M B : Matrix k k ℝ) (hB : IsUnit B.det) :
    B * (Bᵀ * M * B)⁻¹ * Bᵀ = M⁻¹ := by
  -- Rewrite the inverse of the triple product in reverse order.
  calc
    B * (Bᵀ * M * B)⁻¹ * Bᵀ
        = B * (B⁻¹ * (M⁻¹ * (Bᵀ)⁻¹)) * Bᵀ := by
            rw [show Bᵀ * M * B = (Bᵀ * M) * B by simp [Matrix.mul_assoc]]
            rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    _ = (B * B⁻¹) * (M⁻¹ * (Bᵀ)⁻¹) * Bᵀ := by
          simp [Matrix.mul_assoc]
    _ = M⁻¹ * ((Bᵀ)⁻¹ * Bᵀ) := by
          rw [Matrix.mul_nonsing_inv B hB, Matrix.one_mul]
          simp [Matrix.mul_assoc]
    _ = M⁻¹ := by
          rw [Matrix.nonsing_inv_mul Bᵀ (Matrix.isUnit_det_transpose B hB), Matrix.mul_one]

/-- The projector built from `Q * B` has the same normal form as the projector built from `Q`. -/
lemma projector_normal_form_under_basis_change
    {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    (H : Matrix n n ℝ) (Q : Matrix n k ℝ) (B : Matrix k k ℝ) (hB : IsUnit B.det) :
    (Q * B) * (((Q * B)ᵀ * H * (Q * B))⁻¹) * (Q * B)ᵀ = Q * (Qᵀ * H * Q)⁻¹ * Qᵀ := by
  -- Normalize the inner reduced Hessian so the basis-change matrix appears in a cancellable form.
  calc
    (Q * B) * (((Q * B)ᵀ * H * (Q * B))⁻¹) * (Q * B)ᵀ
        = Q * (B * (Bᵀ * (Qᵀ * H * Q) * B)⁻¹ * Bᵀ) * Qᵀ := by
            rw [basis_change_hessian_factorization H Q B, Matrix.transpose_mul]
            simp [Matrix.mul_assoc]
    _ = Q * (Qᵀ * H * Q)⁻¹ * Qᵀ := by
          -- Cancel the basis-change matrix using its determinant-unit hypothesis.
          rw [basis_change_inverse_sandwich (Qᵀ * H * Q) B hB]

theorem reducedHessianProjector_independent_of_basis
    {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    (H : Matrix n n ℝ) (N : Submodule ℝ (n → ℝ))
    (Q Z₁ Z₂ : Matrix n k ℝ) (B₁ B₂ : Matrix k k ℝ)
    (hQ : Qᵀ * Q = 1)
    (hZ₁ : Z₁ = Q * B₁)
    (hZ₂ : Z₂ = Q * B₂)
    (hspan₁ :
      Submodule.span ℝ
        (Set.range fun j : k => Z₁.mulVec (fun j' => if j' = j then 1 else 0)) = N)
    (hspan₂ :
      Submodule.span ℝ
        (Set.range fun j : k => Z₂.mulVec (fun j' => if j' = j then 1 else 0)) = N)
    (hB₁ : IsUnit B₁.det)
    (hB₂ : IsUnit B₂.det)
    (hZ₁HZ₁_inv : IsUnit ((Z₁ᵀ * H * Z₁).det))
    (hZ₂HZ₂_inv : IsUnit ((Z₂ᵀ * H * Z₂).det)) :
    Z₁ * (Z₁ᵀ * H * Z₁)⁻¹ * Z₁ᵀ = Z₂ * (Z₂ᵀ * H * Z₂)⁻¹ * Z₂ᵀ := by
  -- Route correction: the span and orthonormality data are not needed once each basis is written as
  -- `Q * B`; the projector reduces to a basis-change normalization identity.
  calc
    Z₁ * (Z₁ᵀ * H * Z₁)⁻¹ * Z₁ᵀ
        = Q * (Qᵀ * H * Q)⁻¹ * Qᵀ := by
            -- Rewrite `Z₁` in terms of `Q` and its square basis-change factor.
            rw [hZ₁]
            exact projector_normal_form_under_basis_change H Q B₁ hB₁
    _ = Z₂ * (Z₂ᵀ * H * Z₂)⁻¹ * Z₂ᵀ := by
          -- Rewrite `Z₂` in the same normal form and close by symmetry.
          rw [hZ₂]
          exact (projector_normal_form_under_basis_change H Q B₂ hB₂).symm

end «problem-159»
