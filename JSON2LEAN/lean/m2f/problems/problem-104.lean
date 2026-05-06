import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-104»

/- [BLOCK Exercise 8.7 | 6 | thm]
Let n ∈ ℕ, let x₁,x₂ ∈ ℝ^n, and let P₁,P₂ ∈ S_{++}^n, where S_{++}^n is the set of real symmetric
positive definite n × n matrices. For i=1,2, let Pᵢ^{1/2} denote the unique symmetric positive
definite square root of Pᵢ, and define
E₁={x∈ ℝ^n | (x-x₁)ᵀ P₁^{-1}(x-x₁)≤ 1},
E₂={x∈ ℝ^n | (x-x₂)ᵀ P₂^{-1}(x-x₂)≤ 1}.
Let ‖·‖_2 be the Euclidean norm on ℝ^n. Show that E_1cap E₂=emptyset if and only if there exists a∈
ℝ^n such that ‖P₂^{1/2}a‖_2+‖P₁^{1/2}a‖_2< aᵀ(x₁-x₂).
-/
open scoped Matrix

/-- Any linear functional on `Fin n → ℝ` is determined by its values on the standard basis, hence
it can be written as a dot product with its coordinate vector. -/
lemma linearMap_eq_dotProduct_stdBasis (n : ℕ) (l : (Fin n → ℝ) →ₗ[ℝ] ℝ) (x : Fin n → ℝ) :
    l x = dotProduct (fun i => l (Pi.single i 1)) x := by
  -- Expand `x` in the standard basis and use linearity term-by-term.
  have hx : x = ∑ i : Fin n, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hij
      simp [hij]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  conv_lhs => rw [hx]
  simp [dotProduct, mul_comm]

/-- For a symmetric matrix, moving the matrix from the right vector to the left vector inside a
dot product produces the same value. -/
lemma dotProduct_mulVec_eq_dotProduct_mulVec_of_isSymm
    {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.IsSymm) (a v : Fin n → ℝ) :
    dotProduct a (Q.mulVec v) = dotProduct (Q.mulVec a) v := by
  -- Route correction: instead of forcing an inner-product instance on `Fin n → ℝ`,
  -- rewrite with `Matrix.dotProduct_mulVec` and `Matrix.vecMul_transpose`.
  rw [Matrix.dotProduct_mulVec]
  have hvec : a ᵥ* Q = Qᵀ.mulVec a := by
    simpa using (Matrix.vecMul_transpose Qᵀ a)
  rw [hvec, hQ.eq]

/-- A symmetric matrix with strictly positive quadratic form on nonzero vectors is invertible. -/
lemma isUnit_of_symmetric_positive
    {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ_symm : Q.IsSymm)
    (hQ_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (Q.mulVec v)) :
    IsUnit Q := by
  -- Promote the hypotheses to `PosDef`, then use the standard invertibility theorem.
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
  -- Show that `Q⁻¹ * Q⁻¹` is a left inverse of `P`, then invoke uniqueness of the nonsingular
  -- inverse.
  apply Matrix.inv_eq_left_inv
  calc
    (Q⁻¹ * Q⁻¹) * P = (Q⁻¹ * Q⁻¹) * (Q * Q) := by rw [hQsq]
    _ = Q⁻¹ * (Q⁻¹ * (Q * Q)) := by rw [Matrix.mul_assoc]
    _ = Q⁻¹ * ((Q⁻¹ * Q) * Q) := by rw [Matrix.mul_assoc]
    _ = Q⁻¹ * (1 * Q) := by rw [Matrix.inv_mul_of_invertible]
    _ = Q⁻¹ * Q := by simp
    _ = 1 := by rw [Matrix.inv_mul_of_invertible]

/-- The Euclidean `L²` norm on `Fin n → ℝ`, expressed through `WithLp`, is the square root of the
dot product with itself. -/
lemma norm_toLp_eq_sqrt_dotProduct (n : ℕ) (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 v‖ = Real.sqrt (dotProduct v v) := by
  -- Interpret the vector in `EuclideanSpace` and use the usual norm/inner-product identity there.
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
lemma dotProduct_ofLp_self {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    dotProduct u.ofLp u.ofLp = ‖u‖ ^ 2 := by
  -- Rewrite the Euclidean inner product in coordinates.
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
  -- The positivity hypothesis gives the invertibility needed to rewrite `P⁻¹`.
  let hQunit : IsUnit Q := isUnit_of_symmetric_positive hQsymm hQpos
  let _ : Invertible Q := hQunit.invertible
  have hQinv_symm : Q⁻¹.IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_nonsing_inv, hQsymm.eq]
  -- Move one inverse factor across the dot product after expressing `P⁻¹` as `Q⁻¹ * Q⁻¹`.
  calc
    dotProduct y (P⁻¹.mulVec y)
      = dotProduct y ((Q⁻¹ * Q⁻¹).mulVec y) := by
          rw [inv_eq_mul_inv_of_square hQsq hQunit]
    _ = dotProduct y (Q⁻¹.mulVec (Q⁻¹.mulVec y)) := by
          rw [Matrix.mulVec_mulVec]
    _ = dotProduct (Q⁻¹.mulVec y) (Q⁻¹.mulVec y) := by
          simpa using
            dotProduct_mulVec_eq_dotProduct_mulVec_of_isSymm hQinv_symm y (Q⁻¹.mulVec y)

/-- Membership in the inverse-quadratic ellipsoid is equivalent to having unit-ball coordinates in
the symmetric square-root parametrization. -/
lemma mem_ellipsoid_iff_exists_norm_le
    {n : ℕ} {c x : Fin n → ℝ} {P Q : Matrix (Fin n) (Fin n) ℝ}
    (hQsq : Q * Q = P) (hQsymm : Q.IsSymm)
    (hQpos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (Q.mulVec v)) :
    dotProduct (x - c) (P⁻¹.mulVec (x - c)) ≤ 1 ↔
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ 1 ∧ x = c + Q.mulVec u.ofLp := by
  let hQunit : IsUnit Q := isUnit_of_symmetric_positive hQsymm hQpos
  let _ : Invertible Q := hQunit.invertible
  constructor
  · intro hx
    let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Q⁻¹.mulVec (x - c))
    refine ⟨u, ?_, ?_⟩
    · -- The inverse-square-root coordinates satisfy the unit-ball bound by the quadratic identity.
      have hu_sq :
          ‖u‖ ^ 2 ≤ 1 := by
        calc
          ‖u‖ ^ 2 = dotProduct (Q⁻¹.mulVec (x - c)) (Q⁻¹.mulVec (x - c)) := by
            simpa [u] using (dotProduct_ofLp_self u).symm
          _ = dotProduct (x - c) (P⁻¹.mulVec (x - c)) := by
            rw [quadratic_form_eq_dotProduct_inv_sqrt hQsq hQsymm hQpos (x - c)]
          _ ≤ 1 := hx
      nlinarith [norm_nonneg u, hu_sq]
    · -- Multiplying the inverse coordinates back by `Q` recovers `x`.
      calc
        x = c + (x - c) := by abel
        _ = c + Q.mulVec (Q⁻¹.mulVec (x - c)) := by
              rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
        _ = c + Q.mulVec u.ofLp := by
              simp [u]
  · rintro ⟨u, hu, hxu⟩
    -- Substitute the square-root parametrization and reduce the quadratic form to `‖u‖²`.
    calc
      dotProduct (x - c) (P⁻¹.mulVec (x - c))
        = dotProduct (Q⁻¹.mulVec (x - c)) (Q⁻¹.mulVec (x - c)) := by
            rw [quadratic_form_eq_dotProduct_inv_sqrt hQsq hQsymm hQpos (x - c)]
      _ = dotProduct u.ofLp u.ofLp := by
            rw [hxu]
            simp [Matrix.mulVec_mulVec]
      _ = ‖u‖ ^ 2 := dotProduct_ofLp_self u
      _ ≤ 1 := by
            nlinarith [hu, norm_nonneg u]

/-- On the Euclidean unit ball, the support function of a symmetric linear image is bounded by the
Euclidean norm of `Q.mulVec a`. -/
lemma dotProduct_mulVec_le_sqrt_of_norm_le_one
    {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQsymm : Q.IsSymm)
    (a : Fin n → ℝ) {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ ≤ 1) :
    dotProduct a (Q.mulVec u.ofLp) ≤
      Real.sqrt (dotProduct (Q.mulVec a) (Q.mulVec a)) := by
  -- Move `Q` to the left slot of the dot product and reinterpret the result as a Euclidean inner
  -- product.
  have htransport :
      dotProduct a (Q.mulVec u.ofLp) = dotProduct (Q.mulVec a) u.ofLp := by
    simpa using dotProduct_mulVec_eq_dotProduct_mulVec_of_isSymm hQsymm a u.ofLp
  have hinner :
      dotProduct (Q.mulVec a) u.ofLp = inner ℝ u (WithLp.toLp 2 (Q.mulVec a)) := by
    exact (by
      simpa [EuclideanSpace.inner_toLp_toLp] using
        (EuclideanSpace.inner_toLp_toLp u.ofLp (Q.mulVec a)).symm)
  -- Apply Cauchy-Schwarz and convert the Euclidean norm back to the square-root dot-product form.
  calc
    dotProduct a (Q.mulVec u.ofLp) = inner ℝ u (WithLp.toLp 2 (Q.mulVec a)) := by
      rw [htransport, hinner]
    _ ≤ ‖u‖ * ‖WithLp.toLp 2 (Q.mulVec a)‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖WithLp.toLp 2 (Q.mulVec a)‖ := by gcongr
    _ = Real.sqrt (dotProduct (Q.mulVec a) (Q.mulVec a)) := by
      simp [norm_toLp_eq_sqrt_dotProduct]

/-- The support bound on the Euclidean unit ball is attained in the direction of `Q.mulVec a`. -/
lemma exists_norm_le_eq_sqrt_dotProduct
    {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQsymm : Q.IsSymm)
    (a : Fin n → ℝ) :
    ∃ u : EuclideanSpace ℝ (Fin n),
      ‖u‖ ≤ 1 ∧
        dotProduct a (Q.mulVec u.ofLp) =
          Real.sqrt (dotProduct (Q.mulVec a) (Q.mulVec a)) := by
  by_cases hQa : Q.mulVec a = 0
  · refine ⟨0, ?_, ?_⟩
    · simp
    -- If the support direction vanishes, the zero vector already attains the value `0`.
    · simp [hQa]
  · let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Q.mulVec a)
    refine ⟨(‖w‖⁻¹ : ℝ) • w, ?_, ?_⟩
    · -- The normalized support direction lies on the unit sphere.
      have hw : w ≠ 0 := by
        intro hw
        apply hQa
        simpa [w] using congrArg WithLp.ofLp hw
      simpa [w] using (norm_smul_inv_norm hw).le
    · -- Evaluating in the normalized direction gives exactly the Euclidean norm.
      have hw : w ≠ 0 := by
        intro hw
        apply hQa
        simpa [w] using congrArg WithLp.ofLp hw
      have htransport :
          dotProduct a (Q.mulVec (((‖w‖⁻¹ : ℝ) • w).ofLp)) =
            inner ℝ w ((‖w‖⁻¹ : ℝ) • w) := by
        have hstep :
            dotProduct a (Q.mulVec (((‖w‖⁻¹ : ℝ) • w).ofLp)) =
              dotProduct (Q.mulVec a) (((‖w‖⁻¹ : ℝ) • w).ofLp) := by
          simpa using
            dotProduct_mulVec_eq_dotProduct_mulVec_of_isSymm hQsymm a (((‖w‖⁻¹ : ℝ) • w).ofLp)
        calc
          dotProduct a (Q.mulVec (((‖w‖⁻¹ : ℝ) • w).ofLp))
            = inner ℝ ((‖w‖⁻¹ : ℝ) • w) w := by
                rw [hstep]
                simpa [w, EuclideanSpace.inner_toLp_toLp] using
                  (EuclideanSpace.inner_toLp_toLp (((‖w‖⁻¹ : ℝ) • w).ofLp) (Q.mulVec a)).symm
          _ = inner ℝ w ((‖w‖⁻¹ : ℝ) • w) := by
                rw [real_inner_comm]
      have hw_inner : inner ℝ w ((‖w‖⁻¹ : ℝ) • w) = ‖w‖ := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp [norm_ne_zero_iff.mpr hw]
      calc
        dotProduct a (Q.mulVec (((‖w‖⁻¹ : ℝ) • w).ofLp)) = ‖w‖ := by
          rw [htransport, hw_inner]
        _ = Real.sqrt (dotProduct (Q.mulVec a) (Q.mulVec a)) := by
          simp [w, norm_toLp_eq_sqrt_dotProduct]

theorem ellipsoids_disjoint_iff_exists_separating_vector
    (n : ℕ) (x₁ x₂ : Fin n → ℝ) (P₁ P₂ : Matrix (Fin n) (Fin n) ℝ)
    (hP₁_symm : P₁.IsSymm) (hP₂_symm : P₂.IsSymm)
    (hP₁_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₁.mulVec v))
    (hP₂_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₂.mulVec v))
    (hP₁_inv : Nonempty (Invertible P₁)) (hP₂_inv : Nonempty (Invertible P₂))
    (P₁sqrt P₂sqrt : Matrix (Fin n) (Fin n) ℝ)
    (hP₁sqrt_sq : P₁sqrt * P₁sqrt = P₁) (hP₂sqrt_sq : P₂sqrt * P₂sqrt = P₂)
    (hP₁sqrt_symm : P₁sqrt.IsSymm) (hP₂sqrt_symm : P₂sqrt.IsSymm)
    (hP₁sqrt_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₁sqrt.mulVec v))
    (hP₂sqrt_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₂sqrt.mulVec v)) :
    ({x : Fin n → ℝ |
        dotProduct (x - x₁) (P₁⁻¹.mulVec (x - x₁)) ≤ 1} ∩
      {x : Fin n → ℝ |
        dotProduct (x - x₂) (P₂⁻¹.mulVec (x - x₂)) ≤ 1} = (∅ : Set (Fin n → ℝ))) ↔
      ∃ a : Fin n → ℝ,
        Real.sqrt (dotProduct (P₂sqrt.mulVec a) (P₂sqrt.mulVec a)) +
            Real.sqrt (dotProduct (P₁sqrt.mulVec a) (P₁sqrt.mulVec a)) <
          dotProduct a (x₁ - x₂) := by
  let _ := hP₁_symm
  let _ := hP₂_symm
  let _ := hP₁_pos
  let _ := hP₂_pos
  let _ := hP₁_inv
  let _ := hP₂_inv
  let E₁ : Set (Fin n → ℝ) :=
    {x : Fin n → ℝ | dotProduct (x - x₁) (P₁⁻¹.mulVec (x - x₁)) ≤ 1}
  let E₂ : Set (Fin n → ℝ) :=
    {x : Fin n → ℝ | dotProduct (x - x₂) (P₂⁻¹.mulVec (x - x₂)) ≤ 1}
  let B : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1
  let L :
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun p => P₂sqrt.mulVec p.1.ofLp - P₁sqrt.mulVec p.2.ofLp
      map_add' := by
        intro p q
        ext i
        simp [Matrix.mulVec_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      map_smul' := by
        intro r p
        ext i
        simp [Matrix.mulVec_smul]
        ring }
  let K : Set (Fin n → ℝ) := L '' (B ×ˢ B)
  have hmem₁ :
      ∀ {x : Fin n → ℝ},
        x ∈ E₁ ↔
          ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ 1 ∧ x = x₁ + P₁sqrt.mulVec u.ofLp := by
    intro x
    -- Express the first ellipsoid using the square-root coordinates.
    simpa [E₁] using
      (mem_ellipsoid_iff_exists_norm_le
        (c := x₁) (x := x) (P := P₁) (Q := P₁sqrt)
        hP₁sqrt_sq hP₁sqrt_symm hP₁sqrt_pos)
  have hmem₂ :
      ∀ {x : Fin n → ℝ},
        x ∈ E₂ ↔
          ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ 1 ∧ x = x₂ + P₂sqrt.mulVec u.ofLp := by
    intro x
    -- Express the second ellipsoid using the square-root coordinates.
    simpa [E₂] using
      (mem_ellipsoid_iff_exists_norm_le
        (c := x₂) (x := x) (P := P₂) (Q := P₂sqrt)
        hP₂sqrt_sq hP₂sqrt_symm hP₂sqrt_pos)
  constructor
  · intro hdisj
    have hK_convex : Convex ℝ K := by
      -- `K` is the linear image of the product of the two Euclidean unit balls.
      simpa [K, B] using ((convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).prod
        (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).linear_image L
    have hK_compact : IsCompact K := by
      -- Compactness comes from the compact product ball and continuity of the linear map `L`.
      simpa [K, B] using
        ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).prod
          (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).image
          L.continuous_of_finiteDimensional
    have hd_not_mem : x₁ - x₂ ∉ K := by
      intro hd
      rcases hd with ⟨p, hp, hpd⟩
      have hp₁ : ‖p.1‖ ≤ 1 := by
        simpa [B, Metric.mem_closedBall] using hp.1
      have hp₂ : ‖p.2‖ ≤ 1 := by
        simpa [B, Metric.mem_closedBall] using hp.2
      let x : Fin n → ℝ := x₁ + P₁sqrt.mulVec p.2.ofLp
      have hx₁ : x ∈ E₁ := by
        exact (hmem₁.2 ⟨p.2, hp₂, rfl⟩)
      have hx₂_eq : x = x₂ + P₂sqrt.mulVec p.1.ofLp := by
        -- Route correction: instead of separating the two ellipsoids directly, rewrite a point of
        -- the Minkowski-difference body `K` as the displacement between the two square-root
        -- parametrizations.
        have hpd' : P₂sqrt.mulVec p.1.ofLp - P₁sqrt.mulVec p.2.ofLp = x₁ - x₂ := by
          simpa [L] using hpd
        calc
          x = x₁ + P₁sqrt.mulVec p.2.ofLp := rfl
          _ = x₂ + (x₁ - x₂) + P₁sqrt.mulVec p.2.ofLp := by abel
          _ = x₂ + (P₂sqrt.mulVec p.1.ofLp - P₁sqrt.mulVec p.2.ofLp) + P₁sqrt.mulVec p.2.ofLp := by
                rw [← hpd']
          _ = x₂ + P₂sqrt.mulVec p.1.ofLp := by abel
      have hx₂ : x ∈ E₂ := by
        exact (hmem₂.2 ⟨p.1, hp₁, hx₂_eq⟩)
      have hx : x ∈ E₁ ∩ E₂ := ⟨hx₁, hx₂⟩
      have hx' :
          x ∈ ({x : Fin n → ℝ |
            dotProduct (x - x₁) (P₁⁻¹.mulVec (x - x₁)) ≤ 1} ∩
            {x : Fin n → ℝ |
              dotProduct (x - x₂) (P₂⁻¹.mulVec (x - x₂)) ≤ 1}) := by
        simpa [E₁, E₂] using hx
      have : x ∈ (∅ : Set (Fin n → ℝ)) := by
        rw [← hdisj]
        exact hx'
      simp at this
    obtain ⟨f, u, hsepK, hsepd⟩ :=
      geometric_hahn_banach_closed_point hK_convex hK_compact.isClosed hd_not_mem
    let a : Fin n → ℝ := fun i => f.toLinearMap (Pi.single i 1)
    have hf_eq : ∀ x : Fin n → ℝ, f x = dotProduct a x := by
      intro x
      simpa [a] using linearMap_eq_dotProduct_stdBasis n f.toLinearMap x
    obtain ⟨u₂, hu₂, hu₂eq⟩ :=
      exists_norm_le_eq_sqrt_dotProduct (Q := P₂sqrt) hP₂sqrt_symm a
    obtain ⟨u₁, hu₁, hu₁eq⟩ :=
      exists_norm_le_eq_sqrt_dotProduct (Q := P₁sqrt) hP₁sqrt_symm (-a)
    let b : Fin n → ℝ := P₂sqrt.mulVec u₂.ofLp - P₁sqrt.mulVec u₁.ofLp
    have hbK : b ∈ K := by
      refine ⟨(u₂, u₁), ?_, rfl⟩
      constructor
      · simpa [B, Metric.mem_closedBall] using hu₂
      · simpa [B, Metric.mem_closedBall] using hu₁
    have hb_sep : f b < u := hsepK b hbK
    have hb_support :
        f b =
          Real.sqrt (dotProduct (P₂sqrt.mulVec a) (P₂sqrt.mulVec a)) +
            Real.sqrt (dotProduct (P₁sqrt.mulVec a) (P₁sqrt.mulVec a)) := by
      -- Evaluate the separator on the extremal point assembled from the two one-ball maximizers.
      calc
        f b = dotProduct a b := hf_eq b
        _ = dotProduct a (P₂sqrt.mulVec u₂.ofLp) - dotProduct a (P₁sqrt.mulVec u₁.ofLp) := by
              simp [b, dotProduct_sub]
        _ = dotProduct a (P₂sqrt.mulVec u₂.ofLp) + (-dotProduct a (P₁sqrt.mulVec u₁.ofLp)) := by
              ring
        _ = dotProduct a (P₂sqrt.mulVec u₂.ofLp) + dotProduct (-a) (P₁sqrt.mulVec u₁.ofLp) := by
              simp
        _ = Real.sqrt (dotProduct (P₂sqrt.mulVec a) (P₂sqrt.mulVec a)) +
              Real.sqrt (dotProduct (P₁sqrt.mulVec (-a)) (P₁sqrt.mulVec (-a))) := by
              rw [hu₂eq, hu₁eq]
        _ = Real.sqrt (dotProduct (P₂sqrt.mulVec a) (P₂sqrt.mulVec a)) +
              Real.sqrt (dotProduct (P₁sqrt.mulVec a) (P₁sqrt.mulVec a)) := by
              simp [Matrix.mulVec_neg]
    have hd_sep : u < dotProduct a (x₁ - x₂) := by
      simpa [hf_eq (x₁ - x₂)] using hsepd
    refine ⟨a, ?_⟩
    linarith [hb_sep, hd_sep, hb_support]
  · rintro ⟨a, ha⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rcases hx with ⟨hx₁, hx₂⟩
    rcases (hmem₁.mp hx₁) with ⟨u₁, hu₁, hx₁eq⟩
    rcases (hmem₂.mp hx₂) with ⟨u₂, hu₂, hx₂eq⟩
    have hdiff :
        x₁ - x₂ = P₂sqrt.mulVec u₂.ofLp - P₁sqrt.mulVec u₁.ofLp := by
      -- Subtract the two square-root parametrizations of the same common point.
      calc
        x₁ - x₂ = (x - P₁sqrt.mulVec u₁.ofLp) - x₂ := by rw [hx₁eq]; abel
        _ = (x₂ + P₂sqrt.mulVec u₂.ofLp - P₁sqrt.mulVec u₁.ofLp) - x₂ := by rw [hx₂eq]
        _ = P₂sqrt.mulVec u₂.ofLp - P₁sqrt.mulVec u₁.ofLp := by abel
    have hupper₂ :
        dotProduct a (P₂sqrt.mulVec u₂.ofLp) ≤
          Real.sqrt (dotProduct (P₂sqrt.mulVec a) (P₂sqrt.mulVec a)) :=
      dotProduct_mulVec_le_sqrt_of_norm_le_one hP₂sqrt_symm a hu₂
    have hupper₁ :
        -dotProduct a (P₁sqrt.mulVec u₁.ofLp) ≤
          Real.sqrt (dotProduct (P₁sqrt.mulVec a) (P₁sqrt.mulVec a)) := by
      -- Apply the support bound to `-a` to control the negative contribution.
      simpa [Matrix.mulVec_neg] using
        (dotProduct_mulVec_le_sqrt_of_norm_le_one hP₁sqrt_symm (-a) hu₁)
    have hbound :
        dotProduct a (x₁ - x₂) ≤
          Real.sqrt (dotProduct (P₂sqrt.mulVec a) (P₂sqrt.mulVec a)) +
            Real.sqrt (dotProduct (P₁sqrt.mulVec a) (P₁sqrt.mulVec a)) := by
      rw [hdiff, dotProduct_sub]
      linarith
    linarith

end «problem-104»
