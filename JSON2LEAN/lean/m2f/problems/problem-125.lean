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

namespace «problem-125»

def SPDMatrix (n : ℕ) :=
  {A : Matrix (Fin n) (Fin n) ℝ //
    A.IsSymm ∧
      (∀ y : Fin n → ℝ, y ≠ 0 → 0 < dotProduct y (A.mulVec y)) ∧
      Nonempty (Invertible A)}

/- [BLOCK Exercise 8.12 | 14 | defn]
An ellipsoid ∈ ℝ^n is a set of the form E = {x ∈ ℝ^n : (x-c)ᵀ A^(-1) (x-c) <= 1}, where c ∈ ℝ^n and
A is symmetric positive definite.
-/
def ellipsoid (n : ℕ) (c : Fin n → ℝ) (A : SPDMatrix n) :
    Set (Fin n → ℝ) :=
  {x |
    let v : Fin n → ℝ := fun i => x i - c i
    dotProduct v ((A.1⁻¹).mulVec v) ≤ 1}

/- [BLOCK Exercise 8.12 | 15 | defn]
For S subset of ℝ^n, a Loewner-John ellipsoid of S is an ellipsoid contained in S with maximal
n-dimensional Lebesgue measure among all ellipsoids contained in S.
-/
def isLoewnerJohnEllipsoid (n : ℕ) (S : Set (Fin n → ℝ))
    (c : Fin n → ℝ) (A : SPDMatrix n) : Prop :=
  ellipsoid n c A ⊆ S ∧
    ∀ c' : Fin n → ℝ,
      ∀ A' : SPDMatrix n,
        ellipsoid n c' A' ⊆ S →
          MeasureTheory.volume (ellipsoid n c' A') ≤
            MeasureTheory.volume (ellipsoid n c A)

/-- An `SPDMatrix` is positive definite in the standard mathlib sense. -/
lemma spdMatrix_posDef
    {n : ℕ} (A : SPDMatrix n) :
    A.1.PosDef := by
  -- Repackage the custom symmetric/strictly-positive data into `Matrix.PosDef`.
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa using A.2.1
  · intro y hy
    simpa using A.2.2.1 y hy

/-- For a symmetric matrix, moving the matrix from the right slot of the dot product to the left
slot preserves the value. -/
lemma dotProduct_mulVec_eq_dotProduct_mulVec_of_isSymm
    {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.IsSymm) (a v : Fin n → ℝ) :
    dotProduct a (Q.mulVec v) = dotProduct (Q.mulVec a) v := by
  -- Rewrite both sides through the matrix dot-product identities and then use symmetry.
  rw [Matrix.dotProduct_mulVec]
  have hvec : a ᵥ* Q = Qᵀ.mulVec a := by
    simpa using (Matrix.vecMul_transpose Qᵀ a)
  rw [hvec, hQ.eq]

/-- A symmetric matrix with strictly positive quadratic form on nonzero vectors is invertible. -/
lemma isUnit_of_symmetric_positive
    {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ_symm : Q.IsSymm)
    (hQ_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (Q.mulVec v)) :
    IsUnit Q := by
  -- Promote the hypotheses to `PosDef` and use the standard invertibility theorem.
  have hQ_posDef : Q.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · simpa using hQ_symm
    · intro v hv
      simpa using hQ_pos v hv
  exact hQ_posDef.isUnit

/-- If `P = Q * Q` and `Q` is invertible, then the nonsingular inverse of `P` is `Q⁻¹ * Q⁻¹`. -/
lemma inv_eq_mul_inv_of_square
    {n : ℕ} {P Q : Matrix (Fin n) (Fin n) ℝ} (hQsq : Q * Q = P) (hQ_unit : IsUnit Q) :
    P⁻¹ = Q⁻¹ * Q⁻¹ := by
  let _ : Invertible Q := hQ_unit.invertible
  -- Show that `Q⁻¹ * Q⁻¹` is a left inverse of `P`, then use uniqueness of the inverse.
  apply Matrix.inv_eq_left_inv
  calc
    (Q⁻¹ * Q⁻¹) * P = (Q⁻¹ * Q⁻¹) * (Q * Q) := by rw [hQsq]
    _ = Q⁻¹ * (Q⁻¹ * (Q * Q)) := by rw [Matrix.mul_assoc]
    _ = Q⁻¹ * ((Q⁻¹ * Q) * Q) := by rw [Matrix.mul_assoc]
    _ = Q⁻¹ * (1 * Q) := by rw [Matrix.inv_mul_of_invertible]
    _ = Q⁻¹ * Q := by simp
    _ = 1 := by rw [Matrix.inv_mul_of_invertible]

/-- The Euclidean `L²` norm of a coordinate vector is the square root of its dot product with
itself. -/
lemma norm_toLp_eq_sqrt_dotProduct
    {n : ℕ} (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 v‖ = Real.sqrt (dotProduct v v) := by
  -- Translate the norm computation to the Euclidean inner product on `WithLp`.
  have hsq : ‖WithLp.toLp 2 v‖ ^ 2 = dotProduct v v := by
    calc
      ‖WithLp.toLp 2 v‖ ^ 2 = inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
        exact (real_inner_self_eq_norm_sq (WithLp.toLp 2 v)).symm
      _ = dotProduct v v := by
        exact EuclideanSpace.inner_toLp_toLp v v
  have hv_nonneg : 0 ≤ dotProduct v v := by
    rw [← hsq]
    positivity
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), hsq, Real.sq_sqrt hv_nonneg]

/-- The Euclidean dot product of a `WithLp` vector with itself is the square of its norm. -/
lemma dotProduct_ofLp_self
    {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    dotProduct u.ofLp u.ofLp = ‖u‖ ^ 2 := by
  -- Rewrite the coordinate dot product as the ambient Euclidean inner product.
  calc
    dotProduct u.ofLp u.ofLp = inner ℝ u u := by
      exact (EuclideanSpace.inner_toLp_toLp u.ofLp u.ofLp).symm
    _ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u

/-- Rewriting the inverse quadratic form through a symmetric square root turns it into the squared
Euclidean norm of the inverse-square-root coordinates. -/
lemma quadratic_form_eq_dotProduct_inv_sqrt
    {n : ℕ} {P Q : Matrix (Fin n) (Fin n) ℝ}
    (hQsq : Q * Q = P) (hQsymm : Q.IsSymm)
    (hQpos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (Q.mulVec v))
    (y : Fin n → ℝ) :
    dotProduct y (P⁻¹.mulVec y) = dotProduct (Q⁻¹.mulVec y) (Q⁻¹.mulVec y) := by
  let hQunit : IsUnit Q := isUnit_of_symmetric_positive hQsymm hQpos
  let _ : Invertible Q := hQunit.invertible
  have hQinv_symm : Q⁻¹.IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_nonsing_inv, hQsymm.eq]
  -- First rewrite `P⁻¹` as two inverse square-root factors, then move one factor across the dot
  -- product using symmetry of `Q⁻¹`.
  calc
    dotProduct y (P⁻¹.mulVec y)
      = dotProduct y ((Q⁻¹ * Q⁻¹).mulVec y) := by
          rw [inv_eq_mul_inv_of_square hQsq hQunit]
    _ = dotProduct y (Q⁻¹.mulVec (Q⁻¹.mulVec y)) := by
          rw [Matrix.mulVec_mulVec]
    _ = dotProduct (Q⁻¹.mulVec y) (Q⁻¹.mulVec y) := by
          simpa using
            dotProduct_mulVec_eq_dotProduct_mulVec_of_isSymm hQinv_symm y (Q⁻¹.mulVec y)

/-- Membership in the inverse-quadratic ellipsoid is equivalent to belonging to the affine image
of the Euclidean closed unit ball under the positive square root of the shape matrix. -/
lemma mem_ellipsoid_iff_exists_norm_le
    {n : ℕ} {c x : Fin n → ℝ} (A : SPDMatrix n) :
    x ∈ ellipsoid n c A ↔
      ∃ u : EuclideanSpace ℝ (Fin n),
        ‖u‖ ≤ 1 ∧
          x = c + (CFC.sqrt (A.1)).mulVec u.ofLp := by
  let Q : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (A.1)
  have hQsq : Q * Q = A.1 := by
    -- The positive square root squares back to the original SPD matrix.
    simpa [Q] using
      CFC.sqrt_mul_sqrt_self (A.1)
        (show 0 ≤ A.1 from (spdMatrix_posDef A).posSemidef.nonneg)
  have hQsymm : Q.IsSymm := by
    -- Over `ℝ`, the positive square root is self-adjoint, hence symmetric.
    have hself : IsSelfAdjoint Q := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (A.1))
    simpa [Q, Matrix.IsSymm, Matrix.IsHermitian] using hself
  have hQpd : Q.PosDef := by
    -- Positive definiteness is preserved by taking the principal square root.
    simpa [Q] using Matrix.IsStrictlyPositive.posDef (spdMatrix_posDef A).isStrictlyPositive.sqrt
  have hQpos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (Q.mulVec v) := by
    intro v hv
    simpa [Q] using hQpd.dotProduct_mulVec_pos hv
  let hQunit : IsUnit Q := isUnit_of_symmetric_positive hQsymm hQpos
  let _ : Invertible Q := hQunit.invertible
  constructor
  · intro hx
    let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Q⁻¹.mulVec (x - c))
    refine ⟨u, ?_, ?_⟩
    · -- The inverse-square-root coordinates satisfy the closed-unit-ball bound.
      have hu_sq : ‖u‖ ^ 2 ≤ 1 := by
        calc
          ‖u‖ ^ 2 = dotProduct (Q⁻¹.mulVec (x - c)) (Q⁻¹.mulVec (x - c)) := by
            simpa [u] using (dotProduct_ofLp_self u).symm
          _ = dotProduct (x - c) (A.1⁻¹.mulVec (x - c)) := by
            rw [← quadratic_form_eq_dotProduct_inv_sqrt hQsq hQsymm hQpos (x - c)]
          _ ≤ 1 := by
            change dotProduct (fun i => x i - c i) (((A.1)⁻¹).mulVec (fun i => x i - c i)) ≤ 1
            exact hx
      nlinarith [norm_nonneg u, hu_sq]
    · -- Multiplying the inverse coordinates back by `Q` reconstructs the original point.
      calc
        x = c + (x - c) := by
          ext i
          simp [sub_eq_add_neg]
        _ = c + Q.mulVec (Q⁻¹.mulVec (x - c)) := by
              rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
        _ = c + Q.mulVec u.ofLp := by
              simp [u]
  · rintro ⟨u, hu, hxu⟩
    have hxsub : x - c = Q.mulVec u.ofLp := by
      -- Subtract the center from the affine-image formula to isolate the linear part.
      rw [hxu]
      ext i
      simp [Q]
    -- Substitute the square-root parametrization and reduce the quadratic form to `‖u‖²`.
    calc
      dotProduct (x - c) (A.1⁻¹.mulVec (x - c))
        = dotProduct (Q⁻¹.mulVec (x - c)) (Q⁻¹.mulVec (x - c)) := by
            rw [quadratic_form_eq_dotProduct_inv_sqrt hQsq hQsymm hQpos (x - c)]
      _ = dotProduct u.ofLp u.ofLp := by
            rw [hxsub]
            simp [Matrix.mulVec_mulVec]
      _ = ‖u‖ ^ 2 := dotProduct_ofLp_self u
      _ ≤ 1 := by
            nlinarith [hu, norm_nonneg u]

/-- An ellipsoid is exactly the affine image of the Euclidean closed unit ball under the positive
square root of its shape matrix. -/
lemma ellipsoid_eq_image_closedUnitBall
    {n : ℕ} (c : Fin n → ℝ) (A : SPDMatrix n) :
    ellipsoid n c A =
      (fun u : EuclideanSpace ℝ (Fin n) => c + (CFC.sqrt (A.1)).mulVec u.ofLp) ''
        {u : EuclideanSpace ℝ (Fin n) | ‖u‖ ≤ 1} := by
  -- Unpack ellipsoid membership through the square-root coordinates on the unit ball.
  ext x
  constructor
  · intro hx
    rcases (mem_ellipsoid_iff_exists_norm_le A).1 hx with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact (mem_ellipsoid_iff_exists_norm_le A).2 ⟨u, hu, rfl⟩

/-- Every Loewner-John ellipsoid is, by definition, contained in the ambient set. -/
lemma isLoewnerJohnEllipsoid_subset
    {n : ℕ} {S : Set (Fin n → ℝ)}
    {c : Fin n → ℝ} {A : SPDMatrix n}
    (hA : isLoewnerJohnEllipsoid n S c A) :
    ellipsoid n c A ⊆ S :=
  hA.1

/-- Maximality of one Loewner-John ellipsoid bounds the volume of any other admissible ellipsoid. -/
lemma isLoewnerJohnEllipsoid_volume_le
    {n : ℕ} {S : Set (Fin n → ℝ)}
    {c₁ c₂ : Fin n → ℝ} {A₁ A₂ : SPDMatrix n}
    (h₁ : isLoewnerJohnEllipsoid n S c₁ A₁)
    (h₂ : isLoewnerJohnEllipsoid n S c₂ A₂) :
    MeasureTheory.volume (ellipsoid n c₂ A₂) ≤
      MeasureTheory.volume (ellipsoid n c₁ A₁) := by
  -- Apply the maximality clause of the first witness to the second admissible ellipsoid.
  exact h₁.2 c₂ A₂ h₂.1

/-- Two Loewner-John ellipsoids in the same set have the same maximal volume. -/
lemma isLoewnerJohnEllipsoid_volume_eq
    {n : ℕ} {S : Set (Fin n → ℝ)}
    {c₁ c₂ : Fin n → ℝ} {A₁ A₂ : SPDMatrix n}
    (h₁ : isLoewnerJohnEllipsoid n S c₁ A₁)
    (h₂ : isLoewnerJohnEllipsoid n S c₂ A₂) :
    MeasureTheory.volume (ellipsoid n c₁ A₁) =
      MeasureTheory.volume (ellipsoid n c₂ A₂) := by
  -- Each maximal ellipsoid bounds the other's volume, so antisymmetry gives equality.
  apply le_antisymm
  · exact isLoewnerJohnEllipsoid_volume_le h₂ h₁
  · exact isLoewnerJohnEllipsoid_volume_le h₁ h₂

/-- The midpoint of the two principal square roots is again positive definite. -/
lemma midpointRoot_posDef
    {n : ℕ} (A₁ A₂ : SPDMatrix n) :
    (((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1)) :
      Matrix (Fin n) (Fin n) ℝ).PosDef := by
  -- Each principal square root is positive definite, and the positive-definite cone is convex.
  have hsqrt₁ : (CFC.sqrt A₁.1).PosDef := by
    -- Positive definiteness is preserved by the principal square root.
    simpa using Matrix.IsStrictlyPositive.posDef (spdMatrix_posDef A₁).isStrictlyPositive.sqrt
  have hsqrt₂ : (CFC.sqrt A₂.1).PosDef := by
    -- The same square-root positivity statement holds for the second shape.
    simpa using Matrix.IsStrictlyPositive.posDef (spdMatrix_posDef A₂).isStrictlyPositive.sqrt
  have hsum :
      (CFC.sqrt A₁.1 + CFC.sqrt A₂.1).PosDef := by
    simpa using hsqrt₁.add hsqrt₂
  -- Scaling by the positive scalar `1 / 2` keeps the midpoint root positive definite.
  simpa using hsum.smul (show 0 < (1 / 2 : ℝ) by norm_num)

/-- The squared midpoint root is positive definite, hence defines a valid ellipsoid shape. -/
lemma midpointShape_posDef
    {n : ℕ} (A₁ A₂ : SPDMatrix n) :
    (( ((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1)) :
        Matrix (Fin n) (Fin n) ℝ) ^ 2).PosDef := by
  -- Conjugating the identity positive-definite matrix by the midpoint root produces its square.
  let Q : Matrix (Fin n) (Fin n) ℝ :=
    ((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1))
  have hQ : Q.PosDef := by
    -- This is exactly the previous midpoint-root positivity statement.
    simpa [Q] using midpointRoot_posDef A₁ A₂
  have hQ_inj : Function.Injective Q.mulVec := Matrix.mulVec_injective_of_isUnit hQ.isUnit
  have hI : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef := Matrix.PosDef.one
  have hQQ :
      (Qᴴ * (1 : Matrix (Fin n) (Fin n) ℝ) * Q).PosDef := by
    -- The general conjugation lemma applies with the identity matrix as the base form.
    simpa using hI.conjTranspose_mul_mul_same hQ_inj
  have hQ_symm : Q.IsSymm := by
    -- Over `ℝ`, Hermitian and symmetric coincide.
    simpa [Matrix.IsSymm, Matrix.IsHermitian] using hQ.1
  have hQ_transpose : Qᵀ = Q := hQ_symm.eq
  have hQsq : (Q ^ 2).PosDef := by
    -- Replace the transpose by `Q` itself before identifying the square.
    simpa [pow_two, hQ_transpose] using hQQ
  simpa [Q] using hQsq

/-- The midpoint-root square is symmetric. -/
lemma midpointShape_isSymm
    {n : ℕ} (A₁ A₂ : SPDMatrix n) :
    (((((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1)) :
        Matrix (Fin n) (Fin n) ℝ) ^ 2)).IsSymm := by
  -- Positive definiteness implies self-adjointness, which over `ℝ` is symmetry.
  simpa [Matrix.IsSymm, Matrix.IsHermitian] using (midpointShape_posDef A₁ A₂).1

/-- The midpoint-root square has strictly positive quadratic form on nonzero vectors. -/
lemma midpointShape_quadratic_pos
    {n : ℕ} (A₁ A₂ : SPDMatrix n) :
    ∀ y : Fin n → ℝ,
      y ≠ 0 →
        0 <
          dotProduct y
            (((((((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1)) :
                Matrix (Fin n) (Fin n) ℝ) ^ 2))).mulVec y) := by
  intro y hy
  -- The squared midpoint root is already positive definite, so its quadratic form is positive.
  simpa using (midpointShape_posDef A₁ A₂).dotProduct_mulVec_pos hy

/-- The midpoint-root square is invertible because it is positive definite. -/
lemma midpointShape_invertible
    {n : ℕ} (A₁ A₂ : SPDMatrix n) :
    Nonempty
      (Invertible
        (((((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1)) :
            Matrix (Fin n) (Fin n) ℝ) ^ 2))) := by
  -- Positive-definite matrices are invertible.
  exact ⟨(midpointShape_posDef A₁ A₂).isUnit.invertible⟩

/-- The ellipsoid shape obtained by midpointing the square roots of two SPD matrices. -/
def midpointShape
    {n : ℕ} (A₁ A₂ : SPDMatrix n) : SPDMatrix n :=
  ⟨((((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1)) :
      Matrix (Fin n) (Fin n) ℝ) ^ 2),
    midpointShape_isSymm A₁ A₂,
    midpointShape_quadratic_pos A₁ A₂,
    midpointShape_invertible A₁ A₂⟩

/-- The principal square root of the midpoint shape is the midpoint of the principal square roots. -/
lemma midpointShape_sqrt
    {n : ℕ} (A₁ A₂ : SPDMatrix n) :
    CFC.sqrt (midpointShape A₁ A₂).1 =
      (((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1)) :
        Matrix (Fin n) (Fin n) ℝ) := by
  -- The midpoint root is positive definite, so it is the principal square root of its own square.
  have hmid_nonneg :
      0 ≤
        ((((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1)) :
            Matrix (Fin n) (Fin n) ℝ)) := by
    exact (midpointRoot_posDef A₁ A₂).posSemidef.nonneg
  simpa [midpointShape] using
    (CFC.sqrt_sq
      ((((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1)) :
          Matrix (Fin n) (Fin n) ℝ)) (ha := hmid_nonneg))

/-- The ellipsoid built from the midpoint root stays inside a convex ambient set containing both
endpoint ellipsoids. -/
lemma midpoint_ellipsoid_subset
    {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS_convex : Convex ℝ S)
    {c₁ c₂ : Fin n → ℝ} (A₁ A₂ : SPDMatrix n)
    (hsubset₁ : ellipsoid n c₁ A₁ ⊆ S)
    (hsubset₂ : ellipsoid n c₂ A₂ ⊆ S) :
    ellipsoid n (fun i => (c₁ i + c₂ i) / 2) (midpointShape A₁ A₂) ⊆ S := by
  intro x hx
  rcases (mem_ellipsoid_iff_exists_norm_le (midpointShape A₁ A₂)).1 hx with ⟨u, hu, hx_eq⟩
  have hx₁ : c₁ + (CFC.sqrt A₁.1).mulVec u.ofLp ∈ S := by
    -- Reuse the same unit-ball coordinate to recover a point of the first ellipsoid.
    exact hsubset₁ ((mem_ellipsoid_iff_exists_norm_le A₁).2 ⟨u, hu, rfl⟩)
  have hx₂ : c₂ + (CFC.sqrt A₂.1).mulVec u.ofLp ∈ S := by
    -- And likewise for the second ellipsoid.
    exact hsubset₂ ((mem_ellipsoid_iff_exists_norm_le A₂).2 ⟨u, hu, rfl⟩)
  have hx_mid :
      x =
        (1 / 2 : ℝ) • (c₁ + (CFC.sqrt A₁.1).mulVec u.ofLp) +
          (1 / 2 : ℝ) • (c₂ + (CFC.sqrt A₂.1).mulVec u.ofLp) := by
    -- Rewrite the midpoint ellipsoid point using the explicit midpoint square root.
    rw [hx_eq, midpointShape_sqrt A₁ A₂]
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, div_eq_mul_inv, add_mul,
      Finset.sum_add_distrib]
    ring_nf
  -- Convexity now closes the admissibility argument by midpointing the two endpoint points.
  rw [hx_mid]
  exact hS_convex hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)

/-- The determinant of the rank-one update `I + uuᵀ` is `1 + ‖u‖²` in coordinates. -/
lemma det_one_add_vecMulVec_self
    {n : ℕ} [DecidableEq (Fin n)] (u : Fin n → ℝ) :
    Matrix.det (1 + Matrix.vecMulVec u u) = 1 + dotProduct u u := by
  -- Rewrite the rank-one matrix through a `1 × 1` replicate-column/row product and apply the
  -- matrix determinant lemma in its `A = I` form.
  simpa [Matrix.vecMulVec_eq Unit] using
    (Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) u u)

/-- The determinant of the rank-one update `I + uvᵀ` is `1 + v · u` in coordinates. -/
lemma det_one_add_vecMulVec
    {n : ℕ} [DecidableEq (Fin n)] (u v : Fin n → ℝ) :
    Matrix.det (1 + Matrix.vecMulVec u v) = 1 + dotProduct u v := by
  -- Rewrite the rank-one matrix through a `1 × 1` replicate-column/row product and apply the
  -- matrix determinant lemma in its `A = I` form.
  simpa [Matrix.vecMulVec_eq Unit, dotProduct_comm] using
    (Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) u v)

/-- Distinct positive-definite matrices with the same determinant have strictly larger determinant
after midpointing. -/
lemma det_midpoint_gt_of_posDef_of_ne_of_det_eq
    {n : ℕ} [DecidableEq (Fin n)] {Q₁ Q₂ : Matrix (Fin n) (Fin n) ℝ}
    (hQ₁_pos : Q₁.PosDef) (hQ₂_pos : Q₂.PosDef)
    (hQ_ne : Q₁ ≠ Q₂) (hdet_eq : Q₂.det = Q₁.det) :
    Q₁.det < Matrix.det ((1 / 2 : ℝ) • (Q₁ + Q₂)) := by
  let S : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt Q₁
  let Wnorm : Matrix (Fin n) (Fin n) ℝ := S⁻¹ᵀ * Q₂ * S⁻¹
  -- Normalize by the positive square root of `Q₁` so the comparison reduces to a determinant-one
  -- midpoint factor.
  have hS_pos : S.PosDef := by
    exact Matrix.isStrictlyPositive_iff_posDef.mp (hQ₁_pos.isStrictlyPositive.sqrt)
  have hS_unit : IsUnit S := hS_pos.isUnit
  letI : Invertible S := hS_unit.invertible
  have hS_t : Sᵀ = S := by
    -- Over `ℝ`, Hermitian square roots are symmetric.
    simpa [Matrix.IsHermitian, S] using hS_pos.1.eq
  have hSinv_t : S⁻¹ᵀ = S⁻¹ := by
    -- The inverse of a symmetric positive definite matrix is symmetric.
    simpa [Matrix.IsHermitian, S] using (Matrix.IsHermitian.inv hS_pos.1).eq
  have hSinv_unit : IsUnit (S⁻¹) := by
    exact isUnit_of_invertible (S⁻¹)
  have hWnorm_pos : Wnorm.PosDef := by
    -- Conjugating `Q₂` by the inverse square root preserves positive definiteness.
    have htmp : ((S⁻¹)ᴴ * Q₂ * S⁻¹).PosDef :=
      hQ₂_pos.conjTranspose_mul_mul_same (B := S⁻¹)
        (Matrix.mulVec_injective_of_isUnit hSinv_unit)
    simpa [Wnorm, hSinv_t] using htmp
  have hsqrt_self : CFC.sqrt Q₁ * CFC.sqrt Q₁ = Q₁ := by
    simpa using CFC.sqrt_mul_sqrt_self (a := Q₁) (ha := hQ₁_pos.isStrictlyPositive.nonneg)
  have hSdet_sq : S.det * S.det = Q₁.det := by
    -- The square-root identity transfers directly to determinants.
    simpa [S, Matrix.det_mul] using congrArg Matrix.det hsqrt_self
  have hWnorm_det : Wnorm.det = 1 := by
    -- The normalization makes the determinant equal to `det Q₂ / det Q₁`, hence `1`.
    calc
      Wnorm.det = (S.det)⁻¹ * Q₂.det * (S.det)⁻¹ := by
        simp [Wnorm, Matrix.det_mul, Matrix.det_nonsing_inv]
      _ = (S.det)⁻¹ * Q₁.det * (S.det)⁻¹ := by rw [hdet_eq]
      _ = 1 := by
        have hSdet_ne : S.det ≠ 0 := ne_of_gt (Matrix.PosDef.det_pos hS_pos)
        rw [← hSdet_sq]
        field_simp [hSdet_ne]
  have hWnorm_ne : Wnorm ≠ 1 := by
    -- If the normalized matrix were the identity, then `Q₂` would coincide with `Q₁`.
    intro hW1
    have htmpQ₁ : Sᵀ * S = Q₁ := by
      simpa [hS_t, S] using hsqrt_self
    have htmp := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => Sᵀ * M * S) hW1
    have hQeq : Q₂ = Q₁ := by
      have hQeqS : Q₂ = S * S := by
        simpa [Wnorm, Matrix.mul_assoc, hS_t, hSinv_t] using htmp
      simpa [← htmpQ₁, hS_t] using hQeqS
    exact hQ_ne hQeq.symm
  have hmid_eq :
      ((1 / 2 : ℝ) • (Q₁ + Q₂)) = Sᵀ * ((1 / 2 : ℝ) • (1 + Wnorm)) * S := by
    -- Rewrite the midpoint through the normalized matrix.
    have hQ₁eq : Q₁ = Sᵀ * S := by
      simpa [hS_t, S] using hsqrt_self.symm
    have hQ₂eq : Q₂ = Sᵀ * Wnorm * S := by
      have : Sᵀ * Wnorm * S = Q₂ := by
        simp [Wnorm, Matrix.mul_assoc, hS_t, hSinv_t]
      exact this.symm
    calc
      ((1 / 2 : ℝ) • (Q₁ + Q₂))
          = (1 / 2 : ℝ) • (Sᵀ * S + Sᵀ * Wnorm * S) := by rw [hQ₁eq, hQ₂eq]
      _ = (1 / 2 : ℝ) • (Sᵀ * (1 + Wnorm) * S) := by
            simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = Sᵀ * ((1 / 2 : ℝ) • (1 + Wnorm)) * S := by
            calc
              (1 / 2 : ℝ) • (Sᵀ * (1 + Wnorm) * S)
                  = (1 / 2 : ℝ) • (Sᵀ * ((1 + Wnorm) * S)) := by rw [Matrix.mul_assoc]
              _ = Sᵀ * (((1 / 2 : ℝ) • (1 + Wnorm)) * S) := by
                    rw [Matrix.smul_mul, Matrix.mul_smul]
              _ = Sᵀ * ((1 / 2 : ℝ) • (1 + Wnorm)) * S := by rw [Matrix.mul_assoc]
  have hmid_det :
      Matrix.det ((1 / 2 : ℝ) • (Q₁ + Q₂)) =
        Q₁.det * Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) := by
    -- Taking determinants isolates the strict growth in the normalized midpoint factor.
    calc
      Matrix.det ((1 / 2 : ℝ) • (Q₁ + Q₂))
          = Matrix.det (Sᵀ * ((1 / 2 : ℝ) • (1 + Wnorm)) * S) := by rw [hmid_eq]
      _ = S.det * Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) * S.det := by
            rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      _ = Q₁.det * Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) := by
            rw [← hSdet_sq]
            ring_nf
  have hfactor_gt :
      1 < Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) := by
    let eig : Fin n → ℝ := hWnorm_pos.1.eigenvalues
    have hmid_cfc :
        ((1 / 2 : ℝ) • (1 + Wnorm)) = hWnorm_pos.1.cfc (fun x : ℝ => (1 + x) / 2) := by
      let U := hWnorm_pos.1.eigenvectorUnitary
      let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal eig
      -- Route correction: rather than expand the midpoint entrywise, diagonalize the normalized
      -- matrix and transport the affine scalar map through the conjugation.
      have hspec : Wnorm = (Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) U) D := by
        simpa [D, U, eig] using hWnorm_pos.1.spectral_theorem
      conv_lhs => rw [hspec]
      change (1 / 2 : ℝ) • (1 + (Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) U) D) =
          (Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) U)
            (Matrix.diagonal ((fun x : ℝ => (1 + x) / 2) ∘ eig))
      rw [← map_one (Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) U), ← map_add,
        ← map_smul]
      congr 1
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [D, eig]
        ring_nf
      · simp [D, hij]
    have hdet_mid :
        Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) = ∏ i, ((1 + eig i) / 2 : ℝ) := by
      -- The determinant of the diagonalized midpoint is the product of scalar midpoint factors.
      rw [hmid_cfc]
      simp [Matrix.IsHermitian.cfc, eig, -Unitary.conjStarAlgAut_apply]
    have hprod_eig : ∏ i, eig i = 1 := by
      simpa [eig, hWnorm_pos.1.det_eq_prod_eigenvalues] using hWnorm_det
    have hexists : ∃ i, eig i ≠ 1 := by
      -- Nontriviality of `Wnorm` forces at least one eigenvalue away from `1`.
      by_contra hno
      apply hWnorm_ne
      have hvals : eig = fun _ : Fin n => 1 := by
        funext i
        exact by_contra fun hi => hno ⟨i, hi⟩
      simpa [eig, hvals] using hWnorm_pos.1.spectral_theorem
    have hsqrt_prod : ∏ i, Real.sqrt (eig i) = 1 := by
      -- The geometric mean of the eigenvalues is `1` because their product is `1`.
      calc
        ∏ i, Real.sqrt (eig i) = Real.sqrt (∏ i, eig i) := by
          have hsqrt_prod_finset :
              ∀ s : Finset (Fin n),
                (∏ i ∈ s, Real.sqrt (eig i)) = Real.sqrt (∏ i ∈ s, eig i) := by
            intro s
            refine Finset.induction_on s ?_ ?_
            · simp
            · intro i s hi hs
              rw [Finset.prod_insert hi, Finset.prod_insert hi, hs, Real.sqrt_mul]
              exact (hWnorm_pos.eigenvalues_pos i).le
          simpa using hsqrt_prod_finset Finset.univ
        _ = 1 := by
          rw [hprod_eig]
          norm_num
    have hscalar_amgm : ∀ x : ℝ, 0 ≤ x → Real.sqrt x ≤ (1 + x) / 2 := by
      -- Isolate the scalar inequality so `nlinarith` only sees one real variable.
      intro x hx
      have hsq : 0 ≤ (Real.sqrt x - 1) ^ 2 := sq_nonneg _
      nlinarith [hsq, Real.sq_sqrt hx]
    have hscalar_amgm_strict :
        ∀ x : ℝ, 0 ≤ x → x ≠ 1 → Real.sqrt x < (1 + x) / 2 := by
      -- Strictness comes from the square being strictly positive when `x ≠ 1`.
      intro x hx hx1
      have hsq_pos : 0 < (Real.sqrt x - 1) ^ 2 := by
        apply sq_pos_of_ne_zero
        intro hs
        apply hx1
        exact Real.sqrt_eq_one.mp (sub_eq_zero.mp hs)
      nlinarith [hsq_pos, Real.sq_sqrt hx]
    have hfactor_le : ∀ i, Real.sqrt (eig i) ≤ (1 + eig i) / 2 := by
      -- This is the scalar AM-GM inequality in the form `2√t ≤ 1 + t`.
      intro i
      have heig : 0 ≤ eig i := (hWnorm_pos.eigenvalues_pos i).le
      exact hscalar_amgm (eig i) heig
    have hfactor_lt : ∀ i, eig i ≠ 1 → Real.sqrt (eig i) < (1 + eig i) / 2 := by
      -- A non-unit eigenvalue gives a strict scalar AM-GM inequality.
      intro i hi
      have heig : 0 ≤ eig i := (hWnorm_pos.eigenvalues_pos i).le
      exact hscalar_amgm_strict (eig i) heig hi
    have hprod_lt : ∏ i, Real.sqrt (eig i) < ∏ i, ((1 + eig i) / 2 : ℝ) := by
      -- Multiply the scalar inequalities, using strictness at one eigenvalue.
      apply Finset.prod_lt_prod
      · intro i hi
        exact Real.sqrt_pos.2 (hWnorm_pos.eigenvalues_pos i)
      · intro i hi
        exact hfactor_le i
      · rcases hexists with ⟨i, hi⟩
        exact ⟨i, Finset.mem_univ i, hfactor_lt i hi⟩
    calc
      1 = ∏ i, Real.sqrt (eig i) := hsqrt_prod.symm
      _ < ∏ i, ((1 + eig i) / 2 : ℝ) := hprod_lt
      _ = Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) := hdet_mid.symm
  have hQ₁_det_pos : 0 < Q₁.det := Matrix.PosDef.det_pos hQ₁_pos
  have hmul :
      Q₁.det * 1 < Q₁.det * Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) :=
    mul_lt_mul_of_pos_left hfactor_gt hQ₁_det_pos
  -- Multiplying the strict normalized factor by the positive determinant of `Q₁` finishes.
  calc
    Q₁.det = Q₁.det * 1 := by ring_nf
    _ < Q₁.det * Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) := hmul
    _ = Matrix.det ((1 / 2 : ℝ) • (Q₁ + Q₂)) := hmid_det.symm

/-- Rewriting the Euclidean closed unit ball through `WithLp.ofLp` matches the coordinate model
used by the ellipsoid definition. -/
lemma ofLp_preimage_ellipsoid_eq_image_closedUnitBall
    {n : ℕ} (c : Fin n → ℝ) (A : SPDMatrix n) :
    WithLp.ofLp ⁻¹' ellipsoid n c A =
      (fun u : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 c + Matrix.toEuclideanLin (CFC.sqrt A.1) u) ''
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  -- Pass ellipsoid membership through the existing square-root parametrization and then convert the
  -- resulting affine formula into Euclidean coordinates via `toLp`.
  ext u
  constructor
  · intro hu
    rcases (mem_ellipsoid_iff_exists_norm_le A).1 hu with ⟨v, hv, huv⟩
    refine ⟨v, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hv
    · have huv' := congrArg (WithLp.toLp 2) huv
      simpa using huv'.symm
  · rintro ⟨v, hv, rfl⟩
    -- Rebuild the point in the function-space model and reuse the same closed-unit-ball witness.
    apply (mem_ellipsoid_iff_exists_norm_le A).2
    refine ⟨v, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hv
    · simp

/-- Ellipsoids are compact because they are continuous images of the Euclidean closed unit ball. -/
lemma ellipsoid_isCompact
    {n : ℕ} (c : Fin n → ℝ) (A : SPDMatrix n) :
    IsCompact (ellipsoid n c A) := by
  -- Rewrite the ellipsoid as the affine image of the compact Euclidean closed unit ball.
  let f : EuclideanSpace ℝ (Fin n) → Fin n → ℝ :=
    fun u => c + (CFC.sqrt A.1).mulVec u.ofLp
  have hf : Continuous f := by
    have hlin :
        Continuous fun u : EuclideanSpace ℝ (Fin n) =>
          Matrix.toEuclideanLin (CFC.sqrt A.1) u :=
      (Matrix.toEuclideanLin (CFC.sqrt A.1)).continuous_of_finiteDimensional
    have hof :
        Continuous fun u : EuclideanSpace ℝ (Fin n) =>
          (Matrix.toEuclideanLin (CFC.sqrt A.1) u).ofLp :=
      (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).comp hlin
    simpa [f] using continuous_const.add hof
  have hball :
      {u : EuclideanSpace ℝ (Fin n) | ‖u‖ ≤ 1} =
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    ext u
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [ellipsoid_eq_image_closedUnitBall c A, hball]
  exact (isCompact_closedBall _ _).image hf

/-- The volume of an ellipsoid is the determinant factor of its principal square root times the
volume of the Euclidean closed unit ball. -/
lemma ellipsoid_volume_via_sqrt_det
    {n : ℕ} (c : Fin n → ℝ) (A : SPDMatrix n) :
    MeasureTheory.volume (ellipsoid n c A) =
      ENNReal.ofReal (Matrix.det (CFC.sqrt A.1)) *
        MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  let Q : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt A.1
  have hs : MeasurableSet (ellipsoid n c A) := (ellipsoid_isCompact c A).measurableSet
  have hpre :=
    (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage hs.nullMeasurableSet
  rw [ofLp_preimage_ellipsoid_eq_image_closedUnitBall c A] at hpre
  have hsplit :
      (fun u : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 c + Matrix.toEuclideanLin Q u) ''
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 =
        (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 c + z) ''
          ((Matrix.toEuclideanLin Q) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    -- Separate the affine map into a translation after the linear image.
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨Matrix.toEuclideanLin Q u, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
  have htranslate :
      MeasureTheory.volume
        ((fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 c + z) ''
          ((Matrix.toEuclideanLin Q) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) =
        MeasureTheory.volume
          ((Matrix.toEuclideanLin Q) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    -- Translation invariance removes the center from the volume computation.
    rw [show
        (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 c + z) ''
            ((Matrix.toEuclideanLin Q) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) =
          (fun z : EuclideanSpace ℝ (Fin n) => -(WithLp.toLp 2 c) + z) ⁻¹'
            ((Matrix.toEuclideanLin Q) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            simpa using hy
          · intro hx
            refine ⟨-(WithLp.toLp 2 c) + x, hx, ?_⟩
            simp]
    exact
      MeasureTheory.measure_preimage_add MeasureTheory.volume (-(WithLp.toLp 2 c))
        ((Matrix.toEuclideanLin Q) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hQ_pos : Q.PosDef := by
    -- Positive definiteness is preserved by the principal square root.
    simpa [Q] using Matrix.IsStrictlyPositive.posDef (spdMatrix_posDef A).isStrictlyPositive.sqrt
  have hQdet :
      LinearMap.det (Matrix.toEuclideanLin Q) = Matrix.det Q := by
    -- The Euclidean linear map attached to a matrix has the same determinant as the matrix.
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    symm
    simp
  have hQdet_nonneg : 0 ≤ Matrix.det Q := le_of_lt (Matrix.PosDef.det_pos hQ_pos)
  calc
    MeasureTheory.volume (ellipsoid n c A)
        = MeasureTheory.volume
          ((fun u : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 c + Matrix.toEuclideanLin Q u) ''
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := hpre.symm
    _ = MeasureTheory.volume
          ((fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 c + z) ''
            ((Matrix.toEuclideanLin Q) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
          rw [hsplit]
    _ = MeasureTheory.volume
          ((Matrix.toEuclideanLin Q) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
          htranslate
    _ = ENNReal.ofReal (Matrix.det Q) *
          MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
          rw [show
            ENNReal.ofReal (Matrix.det Q) =
              ENNReal.ofReal |LinearMap.det (Matrix.toEuclideanLin Q)| by
                rw [hQdet, abs_of_nonneg hQdet_nonneg]]
          exact
            MeasureTheory.volume.addHaar_image_linearMap (Matrix.toEuclideanLin Q)
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- Moving a transposed matrix from the right slot of the dot product to the left slot preserves
the value. -/
lemma dotProduct_mulVec_transpose_left
    {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (a v : Fin n → ℝ) :
    dotProduct a (Qᵀ.mulVec v) = dotProduct (Q.mulVec a) v := by
  -- Rewrite the right-hand matrix action through `vecMul_transpose`.
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_transpose]

/-- The matrix `R * Rᵀ` is positive definite whenever `R` is invertible. -/
lemma linearImageShape_posDef
    {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} (hR_unit : IsUnit R) :
    (R * Rᵀ).PosDef := by
  -- Positive definiteness of `R * Rᵀ` is the standard Gram-matrix statement for an invertible
  -- square matrix.
  have hR_inj : Function.Injective R.vecMul := Matrix.vecMul_injective_of_isUnit hR_unit
  have hI : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef := Matrix.PosDef.one
  simpa using hI.mul_mul_conjTranspose_same (B := R) hR_inj

/-- The matrix `R * Rᵀ` is symmetric whenever `R` is invertible. -/
lemma linearImageShape_isSymm
    {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} (_hR_unit : IsUnit R) :
    (R * Rᵀ).IsSymm := by
  -- This is the standard symmetry of `R * Rᵀ`.
  exact Matrix.isSymm_mul_transpose_self R

/-- The quadratic form attached to `R * Rᵀ` is strictly positive away from the origin. -/
lemma linearImageShape_quadratic_pos
    {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} (hR_unit : IsUnit R) :
    ∀ y : Fin n → ℝ, y ≠ 0 → 0 < dotProduct y ((R * Rᵀ).mulVec y) := by
  intro y hy
  -- This is the defining positivity statement of the associated positive-definite matrix.
  simpa using (linearImageShape_posDef (R := R) hR_unit).dotProduct_mulVec_pos hy

/-- The matrix `R * Rᵀ` is invertible whenever `R` is invertible. -/
lemma linearImageShape_invertible
    {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} (hR_unit : IsUnit R) :
    Nonempty (Invertible (R * Rᵀ)) := by
  -- Positive-definite matrices are invertible.
  exact ⟨(linearImageShape_posDef (R := R) hR_unit).isUnit.invertible⟩

/-- The SPD matrix determined by an invertible linear image of the Euclidean unit ball. -/
def linearImageShape
    {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (hR_unit : IsUnit R) : SPDMatrix n :=
  ⟨R * Rᵀ,
    linearImageShape_isSymm hR_unit,
    linearImageShape_quadratic_pos hR_unit,
    linearImageShape_invertible hR_unit⟩

/-- The inverse of `R * Rᵀ` is `R⁻ᵀ * R⁻¹` when `R` is invertible. -/
lemma inv_mul_transpose_eq
    {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} (hR_unit : IsUnit R) :
    (R * Rᵀ)⁻¹ = R⁻¹ᵀ * R⁻¹ := by
  let _ : Invertible R := hR_unit.invertible
  -- Show that `R⁻ᵀ * R⁻¹` is a left inverse of `R * Rᵀ`.
  apply Matrix.inv_eq_left_inv
  calc
    (R⁻¹ᵀ * R⁻¹) * (R * Rᵀ) = R⁻¹ᵀ * (R⁻¹ * (R * Rᵀ)) := by rw [Matrix.mul_assoc]
    _ = R⁻¹ᵀ * ((R⁻¹ * R) * Rᵀ) := by rw [Matrix.mul_assoc]
    _ = R⁻¹ᵀ * (1 * Rᵀ) := by rw [Matrix.inv_mul_of_invertible]
    _ = R⁻¹ᵀ * Rᵀ := by simp
    _ = 1 := by
          rw [Matrix.transpose_nonsing_inv]
          simp

/-- Membership in the ellipsoid with shape matrix `R * Rᵀ` is equivalent to belonging to the
affine image of the Euclidean closed unit ball under `R`. -/
lemma mem_linearImageShape_iff_exists_norm_le
    {n : ℕ} {c x : Fin n → ℝ} {R : Matrix (Fin n) (Fin n) ℝ} (hR_unit : IsUnit R) :
    x ∈ ellipsoid n c (linearImageShape R hR_unit) ↔
      ∃ u : EuclideanSpace ℝ (Fin n),
        ‖u‖ ≤ 1 ∧
          x = c + R.mulVec u.ofLp := by
  let _ : Invertible R := hR_unit.invertible
  constructor
  · intro hx
    let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (R⁻¹.mulVec (x - c))
    refine ⟨u, ?_, ?_⟩
    · -- The inverse-image coordinates stay inside the closed unit ball.
      have hu_sq : ‖u‖ ^ 2 ≤ 1 := by
        calc
          ‖u‖ ^ 2 = dotProduct (R⁻¹.mulVec (x - c)) (R⁻¹.mulVec (x - c)) := by
            simpa [u] using (dotProduct_ofLp_self u).symm
          _ = dotProduct (x - c) (((R * Rᵀ)⁻¹).mulVec (x - c)) := by
            symm
            simpa [inv_mul_transpose_eq hR_unit, Matrix.mulVec_mulVec] using
              (dotProduct_mulVec_transpose_left (Q := R⁻¹) (a := x - c)
                (v := R⁻¹.mulVec (x - c)))
          _ ≤ 1 := by
            change dotProduct (fun i => x i - c i)
              (((R * Rᵀ)⁻¹).mulVec (fun i => x i - c i)) ≤ 1
            exact hx
      nlinarith [norm_nonneg u, hu_sq]
    · -- Multiplying back by `R` reconstructs the original point.
      calc
        x = c + (x - c) := by
          ext i
          simp [sub_eq_add_neg]
        _ = c + R.mulVec (R⁻¹.mulVec (x - c)) := by
              rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
        _ = c + R.mulVec u.ofLp := by simp [u]
  · rintro ⟨u, hu, hxu⟩
    have hxsub : x - c = R.mulVec u.ofLp := by
      -- Subtract the center from the affine-image formula to isolate the linear part.
      rw [hxu]
      ext i
      simp
    -- Substituting the linear-image parametrization reduces the quadratic form to `‖u‖²`.
    calc
      dotProduct (x - c) (((R * Rᵀ)⁻¹).mulVec (x - c))
        = dotProduct (R⁻¹.mulVec (x - c)) (R⁻¹.mulVec (x - c)) := by
            simpa [inv_mul_transpose_eq hR_unit, Matrix.mulVec_mulVec] using
              (dotProduct_mulVec_transpose_left (Q := R⁻¹) (a := x - c)
                (v := R⁻¹.mulVec (x - c)))
      _ = dotProduct u.ofLp u.ofLp := by
            rw [hxsub]
            simp [Matrix.mulVec_mulVec]
      _ = ‖u‖ ^ 2 := dotProduct_ofLp_self u
      _ ≤ 1 := by
            nlinarith [hu, norm_nonneg u]

/-- Rewriting the `WithLp.ofLp` preimage of a linear-image ellipsoid matches its Euclidean affine
model. -/
lemma ofLp_preimage_linearImageShape_eq_image_closedUnitBall
    {n : ℕ} (c : Fin n → ℝ) {R : Matrix (Fin n) (Fin n) ℝ} (hR_unit : IsUnit R) :
    WithLp.ofLp ⁻¹' ellipsoid n c (linearImageShape R hR_unit) =
      (fun u : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 c + Matrix.toEuclideanLin R u) ''
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  -- Pass ellipsoid membership through the explicit linear-image coordinates.
  ext u
  constructor
  · intro hu
    rcases (mem_linearImageShape_iff_exists_norm_le hR_unit).1 hu with ⟨v, hv, huv⟩
    refine ⟨v, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hv
    · have huv' := congrArg (WithLp.toLp 2) huv
      simpa using huv'.symm
  · rintro ⟨v, hv, rfl⟩
    -- Reuse the same closed-unit-ball witness in the coordinate model.
    apply (mem_linearImageShape_iff_exists_norm_le hR_unit).2
    refine ⟨v, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hv
    · simp

/-- The volume of the ellipsoid with shape `R * Rᵀ` is `|det R|` times the volume of the Euclidean
closed unit ball. -/
lemma linearImageShape_volume
    {n : ℕ} (c : Fin n → ℝ) {R : Matrix (Fin n) (Fin n) ℝ} (hR_unit : IsUnit R) :
    MeasureTheory.volume (ellipsoid n c (linearImageShape R hR_unit)) =
      ENNReal.ofReal |Matrix.det R| *
        MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have hs :
      MeasurableSet (ellipsoid n c (linearImageShape R hR_unit)) :=
    (ellipsoid_isCompact c (linearImageShape R hR_unit)).measurableSet
  have hpre :=
    (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage hs.nullMeasurableSet
  rw [ofLp_preimage_linearImageShape_eq_image_closedUnitBall c hR_unit] at hpre
  have hsplit :
      (fun u : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 c + Matrix.toEuclideanLin R u) ''
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 =
        (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 c + z) ''
          ((Matrix.toEuclideanLin R) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    -- Separate the affine map into a translation after the linear image.
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨Matrix.toEuclideanLin R u, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
  have htranslate :
      MeasureTheory.volume
        ((fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 c + z) ''
          ((Matrix.toEuclideanLin R) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) =
        MeasureTheory.volume
          ((Matrix.toEuclideanLin R) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    -- Translation invariance removes the center from the volume computation.
    rw [show
        (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 c + z) ''
            ((Matrix.toEuclideanLin R) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) =
          (fun z : EuclideanSpace ℝ (Fin n) => -(WithLp.toLp 2 c) + z) ⁻¹'
            ((Matrix.toEuclideanLin R) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            simpa using hy
          · intro hx
            refine ⟨-(WithLp.toLp 2 c) + x, hx, ?_⟩
            simp]
    exact
      MeasureTheory.measure_preimage_add MeasureTheory.volume (-(WithLp.toLp 2 c))
        ((Matrix.toEuclideanLin R) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hRdet :
      LinearMap.det (Matrix.toEuclideanLin R) = Matrix.det R := by
    -- The Euclidean linear map attached to a matrix has the same determinant as the matrix.
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    symm
    simp
  calc
    MeasureTheory.volume (ellipsoid n c (linearImageShape R hR_unit))
        = MeasureTheory.volume
          ((fun u : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 c + Matrix.toEuclideanLin R u) ''
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := hpre.symm
    _ = MeasureTheory.volume
          ((fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 c + z) ''
            ((Matrix.toEuclideanLin R) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
          rw [hsplit]
    _ = MeasureTheory.volume
          ((Matrix.toEuclideanLin R) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
          htranslate
    _ = ENNReal.ofReal |Matrix.det R| *
          MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
          rw [show
            ENNReal.ofReal |Matrix.det R| =
              ENNReal.ofReal |LinearMap.det (Matrix.toEuclideanLin R)| by rw [hRdet]]
          exact
            MeasureTheory.volume.addHaar_image_linearMap (Matrix.toEuclideanLin R)
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The Euclidean closed unit ball has positive volume, so determinant comparisons can be
recovered from ellipsoid volume comparisons. -/
lemma closedUnitBall_volume_pos
    {n : ℕ} :
    0 < MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  -- The open unit ball is nonempty and sits inside the closed unit ball.
  have hball_pos :
      0 < MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    exact IsOpen.measure_pos (μ := MeasureTheory.volume) Metric.isOpen_ball
      (Metric.nonempty_ball.2 zero_lt_one)
  have hsubset :
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro x hx
    have hx' : dist x (0 : EuclideanSpace ℝ (Fin n)) < 1 := by
      simpa [Metric.mem_ball] using hx
    simpa [Metric.mem_closedBall] using le_of_lt hx'
  exact hball_pos.trans_le (MeasureTheory.measure_mono hsubset)

/-- If the midpoint ellipsoid has no larger volume than the endpoints and the endpoint volumes
agree, then the two principal square roots must already coincide. -/
lemma midpoint_root_eq_of_volume_maximality
    {n : ℕ} {c₁ c₂ : Fin n → ℝ} {A₁ A₂ : SPDMatrix n}
    (hmid_volume_le :
      MeasureTheory.volume
          (ellipsoid n (fun i => (c₁ i + c₂ i) / 2) (midpointShape A₁ A₂)) ≤
        MeasureTheory.volume (ellipsoid n c₁ A₁))
    (hvolume :
      MeasureTheory.volume (ellipsoid n c₁ A₁) =
        MeasureTheory.volume (ellipsoid n c₂ A₂)) :
    CFC.sqrt A₁.1 = CFC.sqrt A₂.1 := by
  let V₀ : ENNReal := MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hV₀_ne_zero : V₀ ≠ 0 := by
    exact (closedUnitBall_volume_pos (n := n)).ne'
  have hV₀_ne_top : V₀ ≠ ⊤ := by
    exact (IsCompact.measure_lt_top (μ := MeasureTheory.volume) (isCompact_closedBall _ _)).ne
  have hA₁_vol := ellipsoid_volume_via_sqrt_det c₁ A₁
  have hA₂_vol := ellipsoid_volume_via_sqrt_det c₂ A₂
  have hmid_vol :=
    ellipsoid_volume_via_sqrt_det (fun i => (c₁ i + c₂ i) / 2) (midpointShape A₁ A₂)
  have hsqrt₁_pos : (CFC.sqrt A₁.1).PosDef := by
    -- The endpoint principal square roots stay positive definite.
    simpa using Matrix.IsStrictlyPositive.posDef (spdMatrix_posDef A₁).isStrictlyPositive.sqrt
  have hsqrt₂_pos : (CFC.sqrt A₂.1).PosDef := by
    -- The same positivity statement holds for the second endpoint.
    simpa using Matrix.IsStrictlyPositive.posDef (spdMatrix_posDef A₂).isStrictlyPositive.sqrt
  have hdet_eq :
      Matrix.det (CFC.sqrt A₂.1) = Matrix.det (CFC.sqrt A₁.1) := by
    -- Cancel the common positive closed-ball volume factor from the endpoint volume equality.
    rw [hA₁_vol, hA₂_vol] at hvolume
    have hroot_eq :
        ENNReal.ofReal (Matrix.det (CFC.sqrt A₁.1)) =
          ENNReal.ofReal (Matrix.det (CFC.sqrt A₂.1)) := by
      exact (ENNReal.mul_left_inj hV₀_ne_zero hV₀_ne_top).1 hvolume
    exact (ENNReal.ofReal_eq_ofReal_iff (le_of_lt (Matrix.PosDef.det_pos hsqrt₁_pos))
      (le_of_lt (Matrix.PosDef.det_pos hsqrt₂_pos))).1 hroot_eq |>.symm
  have hmid_det_le :
      Matrix.det (CFC.sqrt (midpointShape A₁ A₂).1) ≤ Matrix.det (CFC.sqrt A₁.1) := by
    -- The same cancellation turns midpoint maximality into a determinant inequality.
    rw [hmid_vol, hA₁_vol] at hmid_volume_le
    have hroot_le :
        ENNReal.ofReal (Matrix.det (CFC.sqrt (midpointShape A₁ A₂).1)) ≤
          ENNReal.ofReal (Matrix.det (CFC.sqrt A₁.1)) := by
      exact (ENNReal.mul_le_mul_iff_left hV₀_ne_zero hV₀_ne_top).1 hmid_volume_le
    exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt (Matrix.PosDef.det_pos hsqrt₁_pos))).1 hroot_le
  by_contra hsqrt_ne
  have hmid_det_gt :
      Matrix.det (CFC.sqrt A₁.1) <
        Matrix.det (((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1)) :
          Matrix (Fin n) (Fin n) ℝ) := by
    -- The strict midpoint determinant-growth lemma now applies directly to the endpoint roots.
    exact det_midpoint_gt_of_posDef_of_ne_of_det_eq hsqrt₁_pos hsqrt₂_pos hsqrt_ne hdet_eq
  have hmid_sqrt :
      CFC.sqrt (midpointShape A₁ A₂).1 =
        (((1 / 2 : ℝ) • (CFC.sqrt A₁.1 + CFC.sqrt A₂.1)) :
          Matrix (Fin n) (Fin n) ℝ) := midpointShape_sqrt A₁ A₂
  -- Rewriting the midpoint root identifies the contradiction between the determinant inequality and
  -- the maximality-derived determinant bound.
  rw [hmid_sqrt] at hmid_det_le
  exact (not_lt_of_ge hmid_det_le) hmid_det_gt

/- [BLOCK Exercise 8.12 | 16 | thm]
Let S be a subset of ℝ^n. Prove that if there exists an ellipsoid E contained in S with maximal
volume among all ellipsoids contained in S, then this maximal ellipsoid is unique.
-/
theorem loewnerJohnEllipsoid_unique
    (n : ℕ) (S : Set (Fin n → ℝ))
    (hS_convex : Convex ℝ S) :
    (∃ c : Fin n → ℝ, ∃ A : SPDMatrix n,
      isLoewnerJohnEllipsoid n S c A) →
    ∀ c₁ c₂ : Fin n → ℝ,
      ∀ A₁ A₂ : SPDMatrix n,
      isLoewnerJohnEllipsoid n S c₁ A₁ →
      isLoewnerJohnEllipsoid n S c₂ A₂ →
      ellipsoid n c₁ A₁ = ellipsoid n c₂ A₂ := by
  intro _hexists c₁ c₂ A₁ A₂ h₁ h₂
  have hsubset₁ : ellipsoid n c₁ A₁ ⊆ S := isLoewnerJohnEllipsoid_subset h₁
  have hsubset₂ : ellipsoid n c₂ A₂ ⊆ S := isLoewnerJohnEllipsoid_subset h₂
  have hvolume :
      MeasureTheory.volume (ellipsoid n c₁ A₁) =
        MeasureTheory.volume (ellipsoid n c₂ A₂) :=
    isLoewnerJohnEllipsoid_volume_eq h₁ h₂
  let cMid : Fin n → ℝ := fun i => (c₁ i + c₂ i) / 2
  let AMid : SPDMatrix n := midpointShape A₁ A₂
  have hsubset_mid : ellipsoid n cMid AMid ⊆ S := by
    -- The midpoint-root ellipsoid is admissible because both endpoint ellipsoids lie in the
    -- convex set `S`.
    simpa [cMid, AMid] using midpoint_ellipsoid_subset hS_convex A₁ A₂ hsubset₁ hsubset₂
  have hmid_volume_le₁ :
      MeasureTheory.volume (ellipsoid n cMid AMid) ≤
        MeasureTheory.volume (ellipsoid n c₁ A₁) := by
    -- Maximality of the first Loewner-John ellipsoid bounds every admissible midpoint candidate.
    exact h₁.2 cMid AMid hsubset_mid
  have hmid_volume_le₂ :
      MeasureTheory.volume (ellipsoid n cMid AMid) ≤
        MeasureTheory.volume (ellipsoid n c₂ A₂) := by
    -- The same midpoint candidate is also bounded by maximality of the second ellipsoid.
    exact h₂.2 cMid AMid hsubset_mid
  have hsqrt_eq : CFC.sqrt A₁.1 = CFC.sqrt A₂.1 := by
    -- The volume-to-determinant bridge and strict midpoint growth force the endpoint roots to
    -- agree.
    exact midpoint_root_eq_of_volume_maximality hmid_volume_le₁ hvolume
  have hA_eq : A₁.1 = A₂.1 := by
    -- Squaring the common principal square root recovers the original shape matrices.
    calc
      A₁.1 = CFC.sqrt A₁.1 * CFC.sqrt A₁.1 := by
        symm
        exact CFC.sqrt_mul_sqrt_self (A₁.1) (spdMatrix_posDef A₁).posSemidef.nonneg
      _ = CFC.sqrt A₂.1 * CFC.sqrt A₂.1 := by rw [hsqrt_eq]
      _ = A₂.1 := CFC.sqrt_mul_sqrt_self (A₂.1) (spdMatrix_posDef A₂).posSemidef.nonneg
  have hc_eq : c₁ = c₂ := by
    by_contra hcenter_ne
    let Q : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt A₁.1
    have hQ_pos : Q.PosDef := by
      -- The common principal square root is positive definite.
      simpa [Q] using Matrix.IsStrictlyPositive.posDef (spdMatrix_posDef A₁).isStrictlyPositive.sqrt
    have hQ_unit : IsUnit Q := hQ_pos.isUnit
    letI : Invertible Q := hQ_unit.invertible
    let cMid : Fin n → ℝ := fun i => (c₁ i + c₂ i) / 2
    let u : Fin n → ℝ := Q⁻¹.mulVec ((1 / 2 : ℝ) • (c₁ - c₂))
    have hQu : Q.mulVec u = (1 / 2 : ℝ) • (c₁ - c₂) := by
      -- Undo the inverse-square-root coordinates defining the center displacement.
      simp [u, Matrix.mulVec_mulVec]
    have hc₁ : c₁ = cMid + Q.mulVec u := by
      -- The first center is the midpoint plus the normalized displacement.
      rw [hQu]
      ext i
      simp [cMid]
      ring_nf
    have hc₂ : c₂ = cMid - Q.mulVec u := by
      -- The second center is the midpoint minus the same normalized displacement.
      rw [hQu]
      ext i
      simp [cMid]
      ring_nf
    have hu_ne : u ≠ 0 := by
      intro hu
      apply hcenter_ne
      apply sub_eq_zero.mp
      have hdiff_zero : (1 / 2 : ℝ) • (c₁ - c₂) = 0 := by
        calc
          (1 / 2 : ℝ) • (c₁ - c₂) = Q.mulVec u := hQu.symm
          _ = 0 := by simp [hu]
      exact (smul_eq_zero.mp hdiff_zero).resolve_left (by norm_num)
    have hu_sq_pos : 0 < dotProduct u u := by
      -- A nonzero Euclidean vector has strictly positive self-dot-product.
      have hu_norm_pos : 0 < ‖WithLp.toLp 2 u‖ := by
        simpa using norm_pos_iff.mpr hu_ne
      rw [norm_toLp_eq_sqrt_dotProduct] at hu_norm_pos
      exact Real.sqrt_pos.mp hu_norm_pos
    set r : ℝ := dotProduct u u with hr
    have hr_pos : 0 < r := by simpa [r] using hu_sq_pos
    have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
    let β : ℝ := (Real.sqrt (1 + r) - 1) / r
    let B : Matrix (Fin n) (Fin n) ℝ := 1 + β • Matrix.vecMulVec u u
    have hB_det : B.det = Real.sqrt (1 + r) := by
      -- The determinant lemma turns the rank-one update into a scalar factor.
      calc
        B.det = Matrix.det (1 + Matrix.vecMulVec (β • u) u) := by
          simp [B, Matrix.smul_vecMulVec]
        _ = 1 + dotProduct (β • u) u := det_one_add_vecMulVec (β • u) u
        _ = 1 + r * β := by
          rw [hr, dotProduct]
          calc
            1 + ∑ x, (β • u) x * u x = 1 + ∑ x, β * (u x * u x) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              simp [mul_assoc, mul_comm]
            _ = 1 + β * ∑ x, u x * u x := by
              rw [← Finset.mul_sum]
            _ = 1 + (∑ x, u x * u x) * β := by ring_nf
        _ = 1 + β * r := by ring_nf
        _ = Real.sqrt (1 + r) := by
          have hr_ne : r ≠ 0 := ne_of_gt hr_pos
          unfold β
          field_simp [hr_ne]
          ring_nf
    have hB_det_gt_one : 1 < B.det := by
      -- The rank-one correction is nontrivial because the centers are distinct.
      rw [hB_det]
      have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + r) := Real.sqrt_nonneg (1 + r)
      nlinarith [hr_pos, Real.sq_sqrt (by positivity : 0 ≤ 1 + r)]
    have hB_det_pos : 0 < B.det := lt_trans zero_lt_one hB_det_gt_one
    have hB_unit : IsUnit B := by
      exact (Matrix.isUnit_iff_isUnit_det (A := B)).2 (isUnit_iff_ne_zero.2 hB_det_pos.ne')
    let R : Matrix (Fin n) (Fin n) ℝ := Q * B
    have hR_unit : IsUnit R := hQ_unit.mul hB_unit
    let APlus : SPDMatrix n := linearImageShape R hR_unit
    have hsubset_plus : ellipsoid n cMid APlus ⊆ S := by
      intro x hx
      rcases (mem_linearImageShape_iff_exists_norm_le hR_unit).1 hx with ⟨w, hw, hxw⟩
      let t : ℝ := β * dotProduct u w.ofLp
      have hx₁ : c₁ + Q.mulVec w.ofLp ∈ S := by
        -- Reuse the same unit-ball coordinate in the first endpoint ellipsoid.
        exact hsubset₁ ((mem_ellipsoid_iff_exists_norm_le A₁).2 ⟨w, hw, by simp [Q]⟩)
      have hx₂ : c₂ + Q.mulVec w.ofLp ∈ S := by
        -- The same unit-ball coordinate also belongs to the second endpoint ellipsoid.
        have : c₂ + (CFC.sqrt A₂.1).mulVec w.ofLp ∈ S :=
          hsubset₂ ((mem_ellipsoid_iff_exists_norm_le A₂).2 ⟨w, hw, rfl⟩)
        simpa [Q, hsqrt_eq] using this
      have hdot_le :
          |dotProduct u w.ofLp| ≤ Real.sqrt r := by
        -- Cauchy-Schwarz bounds the scalar coefficient of the rank-one perturbation.
        have hinner :
            |inner ℝ (WithLp.toLp 2 u) w| ≤ ‖WithLp.toLp 2 u‖ * ‖w‖ := by
          exact abs_real_inner_le_norm (WithLp.toLp 2 u) w
        have hdot_inner : dotProduct u w.ofLp = inner ℝ (WithLp.toLp 2 u) w := by
          symm
          simpa [dotProduct_comm] using (EuclideanSpace.inner_toLp_toLp u w.ofLp)
        have hmul_le : ‖WithLp.toLp 2 u‖ * ‖w‖ ≤ ‖WithLp.toLp 2 u‖ := by
          nlinarith [norm_nonneg (WithLp.toLp 2 u), hw]
        rw [hdot_inner]
        exact hinner.trans (by simpa [r, norm_toLp_eq_sqrt_dotProduct u] using hmul_le)
      have hbeta_nonneg : 0 ≤ β := by
        -- The scalar coefficient of the rank-one update is nonnegative.
        have hsqrt_ge_one : 1 ≤ Real.sqrt (1 + r) := by
          have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + r) := Real.sqrt_nonneg (1 + r)
          nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1 + r)]
        unfold β
        have hnum_nonneg : 0 ≤ Real.sqrt (1 + r) - 1 := by
          linarith
        exact div_nonneg hnum_nonneg hr_nonneg
      have hbeta_le : β * Real.sqrt r ≤ 1 := by
        -- The chosen coefficient keeps the convex-combination parameter inside `[-1, 1]`.
        have hsqrt_bound : Real.sqrt (1 + r) ≤ 1 + Real.sqrt r := by
          refine Real.sqrt_le_iff.mpr ?_
          constructor
          · positivity
          · nlinarith [Real.sq_sqrt hr_nonneg, Real.sqrt_nonneg r]
        have hnum_le : Real.sqrt (1 + r) - 1 ≤ Real.sqrt r := by
          linarith
        have hineq : (Real.sqrt (1 + r) - 1) * Real.sqrt r ≤ r := by
          nlinarith [hnum_le, Real.sqrt_nonneg r, Real.sq_sqrt hr_nonneg]
        unfold β
        field_simp [ne_of_gt hr_pos]
        exact hineq
      have ht_abs : |t| ≤ 1 := by
        -- The convex-combination parameter lies in `[-1, 1]`.
        have ht_le : |t| ≤ β * Real.sqrt r := by
          simp [t, abs_mul, abs_of_nonneg hbeta_nonneg]
          exact mul_le_mul_of_nonneg_left hdot_le hbeta_nonneg
        exact ht_le.trans hbeta_le
      have ht₁ : 0 ≤ (1 + t) / 2 := by
        have := (abs_le.mp ht_abs).1
        nlinarith
      have ht₂ : 0 ≤ (1 - t) / 2 := by
        have := (abs_le.mp ht_abs).2
        nlinarith
      have htsum : (1 + t) / 2 + (1 - t) / 2 = 1 := by ring_nf
      have hBw : B.mulVec w.ofLp = w.ofLp + t • u := by
        -- The rank-one factor acts by adding the scalar multiple `t u`.
        calc
          B.mulVec w.ofLp = w.ofLp + (β • Matrix.vecMulVec u u).mulVec w.ofLp := by
            change (1 + β • Matrix.vecMulVec u u).mulVec w.ofLp =
              w.ofLp + (β • Matrix.vecMulVec u u).mulVec w.ofLp
            rw [Matrix.add_mulVec, Matrix.one_mulVec]
          _ = w.ofLp + β • ((Matrix.vecMulVec u u).mulVec w.ofLp) := by
            rw [Matrix.smul_mulVec]
          _ = w.ofLp + β • (dotProduct u w.ofLp • u) := by
            simp [Matrix.vecMulVec_mulVec]
          _ = w.ofLp + t • u := by
            simp [t, smul_smul]
      have hx_mid :
          x =
            ((1 + t) / 2 : ℝ) • (c₁ + Q.mulVec w.ofLp) +
              ((1 - t) / 2 : ℝ) • (c₂ + Q.mulVec w.ofLp) := by
        -- Expanding the rank-one midpoint image reveals an explicit convex combination of the two
        -- endpoint ellipsoid points.
        rw [hxw, hc₁, hc₂]
        have hRw : R.mulVec w.ofLp = Q.mulVec (w.ofLp + t • u) := by
          calc
            R.mulVec w.ofLp = Q.mulVec (B.mulVec w.ofLp) := by
              simp [R, Matrix.mulVec_mulVec]
            _ = Q.mulVec (w.ofLp + t • u) := by rw [hBw]
        rw [hRw]
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
        ext i
        simp [cMid]
        ring_nf
      rw [hx_mid]
      exact hS_convex hx₁ hx₂ ht₁ ht₂ htsum
    let V₀ : ENNReal := MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    have hV₀_ne_zero : V₀ ≠ 0 := (closedUnitBall_volume_pos (n := n)).ne'
    have hV₀_ne_top : V₀ ≠ ⊤ :=
      (IsCompact.measure_lt_top (μ := MeasureTheory.volume) (isCompact_closedBall _ _)).ne
    have hA₁_vol := ellipsoid_volume_via_sqrt_det c₁ A₁
    have hplus_vol := linearImageShape_volume cMid hR_unit
    have hplus_le :
        MeasureTheory.volume (ellipsoid n cMid APlus) ≤
          MeasureTheory.volume (ellipsoid n c₁ A₁) := by
      -- Maximality of the first ellipsoid bounds every admissible enlargement candidate.
      exact h₁.2 cMid APlus hsubset_plus
    have hdet_le :
        |R.det| ≤ Matrix.det Q := by
      -- Cancel the common positive closed-ball volume factor from the volume inequality.
      rw [hplus_vol, hA₁_vol] at hplus_le
      have hroot_le :
          ENNReal.ofReal |R.det| ≤ ENNReal.ofReal (Matrix.det Q) := by
        exact (ENNReal.mul_le_mul_iff_left hV₀_ne_zero hV₀_ne_top).1 hplus_le
      exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt (Matrix.PosDef.det_pos hQ_pos))).1 hroot_le
    have hR_det : R.det = Q.det * B.det := by
      simp [R, Matrix.det_mul]
    have hR_det_pos : 0 < R.det := by
      rw [hR_det]
      have hQ_det_pos : 0 < Q.det := Matrix.PosDef.det_pos hQ_pos
      nlinarith [hQ_det_pos, hB_det_pos]
    have hdet_gt : Q.det < |R.det| := by
      -- The determinant of the enlarged midpoint root is strictly bigger than the endpoint one.
      rw [abs_of_pos hR_det_pos, hR_det]
      have hQ_det_pos : 0 < Q.det := Matrix.PosDef.det_pos hQ_pos
      nlinarith [hQ_det_pos, hB_det_gt_one]
    exact (not_lt_of_ge hdet_le) hdet_gt
  subst hc_eq
  -- Once the centers agree, equality of the shape matrices gives equality of ellipsoid sets.
  ext x
  simp [ellipsoid, hA_eq]

/- [BLOCK Exercise 8.12 | 17 | thm]
Let S be a subset of ℝ^n. Prove that whenever the Loewner-John ellipsoid of S exists, it is unique.
-/
theorem loewnerJohnEllipsoid_unique_of_exists
    (n : ℕ) (S : Set (Fin n → ℝ))
    (c₁ c₂ : Fin n → ℝ)
    (A₁ A₂ : SPDMatrix n)
    (hS_convex : Convex ℝ S)
    (h₁ : isLoewnerJohnEllipsoid n S c₁ A₁)
    (h₂ : isLoewnerJohnEllipsoid n S c₂ A₂) :
    ellipsoid n c₁ A₁ = ellipsoid n c₂ A₂ := by
  -- The first ellipsoid supplies the existence witness needed by the general uniqueness theorem.
  refine loewnerJohnEllipsoid_unique n S hS_convex ?_ c₁ c₂ A₁ A₂ h₁ h₂
  exact ⟨c₁, A₁, h₁⟩

end «problem-125»
