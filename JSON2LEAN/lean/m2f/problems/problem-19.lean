import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-19»
/-
Given a proper cone K ⊆ ℝ^n, the generalized inequality ⪯_K is the relation on ℝ^n defined by x ⪯_K
y if and only if y - x ∈ K.
-/
def generalizedInequality {n : ℕ} (K : Set (Fin n → ℝ)) (x y : Fin n → ℝ) : Prop :=
  y - x ∈ K

/-- The unit boundary ray determined by the angle `θ`. -/
def boundaryVec (θ : ℝ) : Fin 2 → ℝ :=
  ![Real.cos θ, Real.sin θ]

/-- The determinant coordinate against the right boundary ray. -/
def leftBoundaryCoeff (α β : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  (x 0 * Real.sin β - x 1 * Real.cos β) / Real.sin (β - α)

/-- The determinant coordinate against the left boundary ray. -/
def rightBoundaryCoeff (α β : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  (-x 0 * Real.sin α + x 1 * Real.cos α) / Real.sin (β - α)

/-- The left determinant coordinate reads off the left boundary coefficient. -/
lemma leftBoundaryCoeff_of_boundaryCombination (α β a b : ℝ)
    (hsin : Real.sin (β - α) ≠ 0) :
    leftBoundaryCoeff α β (a • boundaryVec α + b • boundaryVec β) = a := by
  -- The right boundary contribution cancels, leaving only the left determinant.
  simp [leftBoundaryCoeff, boundaryVec]
  field_simp [hsin]
  rw [Real.sin_sub]
  ring_nf

/-- The right determinant coordinate reads off the right boundary coefficient. -/
lemma rightBoundaryCoeff_of_boundaryCombination (α β a b : ℝ)
    (hsin : Real.sin (β - α) ≠ 0) :
    rightBoundaryCoeff α β (a • boundaryVec α + b • boundaryVec β) = b := by
  -- The left boundary contribution cancels, leaving only the right determinant.
  simp [rightBoundaryCoeff, boundaryVec]
  field_simp [hsin]
  rw [Real.sin_sub]
  ring_nf

/-- Solving the two-by-two system recovers a vector from its determinant coordinates. -/
lemma boundaryCombination_eq_self (α β : ℝ) (x : Fin 2 → ℝ)
    (hsin : Real.sin (β - α) ≠ 0) :
    leftBoundaryCoeff α β x • boundaryVec α + rightBoundaryCoeff α β x • boundaryVec β = x := by
  -- The determinant coordinates are the inverse matrix coefficients for the two boundary rays.
  ext i <;> fin_cases i
  · simp [leftBoundaryCoeff, rightBoundaryCoeff, boundaryVec]
    field_simp [hsin]
    rw [Real.sin_sub]
    ring_nf
  · simp [leftBoundaryCoeff, rightBoundaryCoeff, boundaryVec]
    field_simp [hsin]
    rw [Real.sin_sub]
    ring_nf

/-- On a polar point `r (cos φ, sin φ)`, the left determinant coordinate is the expected sine ratio. -/
lemma leftBoundaryCoeff_of_sectorPoint (α β r : ℝ) (φ : Set.Icc α β)
    (hsin : Real.sin (β - α) ≠ 0)
    {x : Fin 2 → ℝ}
    (hx0 : x 0 = r * Real.cos φ) (hx1 : x 1 = r * Real.sin φ) :
    leftBoundaryCoeff α β x = r * Real.sin (β - φ) / Real.sin (β - α) := by
  -- This is Cramer's rule plus the sine subtraction identity.
  unfold leftBoundaryCoeff
  rw [hx0, hx1]
  field_simp [hsin]
  rw [Real.sin_sub]
  ring

/-- On a polar point `r (cos φ, sin φ)`, the right determinant coordinate is the expected sine ratio. -/
lemma rightBoundaryCoeff_of_sectorPoint (α β r : ℝ) (φ : Set.Icc α β)
    (hsin : Real.sin (β - α) ≠ 0)
    {x : Fin 2 → ℝ}
    (hx0 : x 0 = r * Real.cos φ) (hx1 : x 1 = r * Real.sin φ) :
    rightBoundaryCoeff α β x = r * Real.sin (φ - α) / Real.sin (β - α) := by
  -- This is the companion Cramer formula for the right boundary coefficient.
  unfold rightBoundaryCoeff
  rw [hx0, hx1]
  field_simp [hsin]
  rw [Real.sin_sub]
  ring

/-- A cone with nonempty interior contains a nonzero point. -/
lemma exists_nonzero_of_nonempty_interior
    {K : Set (Fin 2 → ℝ)} (hK : Set.Nonempty (interior K)) :
    ∃ x : Fin 2 → ℝ, x ∈ K ∧ x ≠ 0 := by
  rcases hK with ⟨x, hxint⟩
  by_cases hx0 : x = 0
  · -- If the interior point is the origin, a small sphere inside the neighborhood gives a
    -- nonzero point of `K`.
    subst hx0
    rw [mem_interior_iff_mem_nhds] at hxint
    rw [Metric.mem_nhds_iff] at hxint
    rcases hxint with ⟨ε, hεpos, hεsub⟩
    have hsphere_nonempty : (Metric.sphere (0 : Fin 2 → ℝ) (ε / 2)).Nonempty := by
      exact NormedSpace.sphere_nonempty.mpr (by linarith)
    rcases hsphere_nonempty with ⟨y, hySphere⟩
    refine ⟨y, hεsub ?_, ?_⟩
    · -- Any point on the smaller sphere lies in the ambient open ball.
      have hydist : dist y (0 : Fin 2 → ℝ) = ε / 2 := by
        simpa [Metric.sphere, dist_comm] using hySphere
      rw [Metric.mem_ball, hydist]
      linarith
    · -- A point on a positive-radius sphere cannot be the origin.
      intro hy0
      rw [Metric.mem_sphere, hy0, dist_self] at hySphere
      linarith
  · -- Otherwise the interior point itself is already the required nonzero cone point.
    exact ⟨x, interior_subset hxint, hx0⟩

/-- In a pointed cone, the negative of a nonzero cone point is not in the cone. -/
lemma neg_not_mem_of_pointed
    {K : Set (Fin 2 → ℝ)}
    (hpointed : K ∩ (-K) = ({0} : Set (Fin 2 → ℝ)))
    {x : Fin 2 → ℝ} (hx : x ∈ K) (hx0 : x ≠ 0) :
    -x ∉ K := by
  intro hxneg
  -- Putting `x` and `-x` in the pointed intersection forces `x = 0`.
  have hxboth : x ∈ K ∩ (-K) := by
    refine ⟨hx, ?_⟩
    simpa using hxneg
  have hxeq : x = 0 := by
    simpa [hpointed] using hxboth
  exact hx0 hxeq

/-- Separating a closed convex cone from the negative of one of its points produces a functional
that is nonnegative on the cone and strictly positive on that chosen point. -/
lemma exists_nonneg_separating_functional
    (K : Set (Fin 2 → ℝ))
    (h_closed : IsClosed K)
    (h_convex : Convex ℝ K)
    (h_cone : ∀ ⦃x : Fin 2 → ℝ⦄ ⦃a : ℝ⦄, x ∈ K → 0 ≤ a → a • x ∈ K)
    {z : Fin 2 → ℝ} (hz : z ∈ K) (hneg : -z ∉ K) :
    ∃ f : StrongDual ℝ (Fin 2 → ℝ),
      (∀ x : Fin 2 → ℝ, x ∈ K → 0 ≤ f x) ∧ 0 < f z := by
  obtain ⟨f, u, hltK, hltNeg⟩ := geometric_hahn_banach_closed_point h_convex h_closed hneg
  have hzero : (0 : Fin 2 → ℝ) ∈ K := by
    -- Every nonempty cone contains the origin by scaling a point by `0`.
    simpa using h_cone hz (show 0 ≤ (0 : ℝ) by norm_num)
  have hu_pos : 0 < u := by
    -- The separating threshold must be positive because `0 ∈ K`.
    have h0lt : f (0 : Fin 2 → ℝ) < u := hltK 0 hzero
    simpa using h0lt
  have hnonpos : ∀ x : Fin 2 → ℝ, x ∈ K → f x ≤ 0 := by
    intro x hx
    by_contra hpos
    -- If `f x` were positive on some cone point, scaling that ray would violate the separator.
    have hfx_pos : 0 < f x := lt_of_not_ge hpos
    obtain ⟨n, hn⟩ := exists_nat_gt (u / f x)
    have hnx : ((n : ℝ) • x) ∈ K := h_cone hx (show 0 ≤ (n : ℝ) by exact Nat.cast_nonneg n)
    have hlt_scaled : f ((n : ℝ) • x) < u := hltK _ hnx
    have hgt_scaled : u < f ((n : ℝ) • x) := by
      rw [map_smul]
      have hmul : u < (n : ℝ) * f x := (div_lt_iff₀ hfx_pos).1 (by simpa using hn)
      simpa [smul_eq_mul] using hmul
    linarith
  refine ⟨-f, ?_, ?_⟩
  · -- Negating the separator flips the cone inequality to the nonnegative orientation we want.
    intro x hx
    simpa using neg_nonneg.mpr (hnonpos x hx)
  · -- The chosen point stays strictly positive after the same sign change.
    have hzneg : u < -f z := by
      simpa using hltNeg
    have hpos' : 0 < -f z := lt_trans hu_pos hzneg
    simpa using hpos'

/-- A proper closed convex cone admits a single functional that is nonnegative on the cone and
strictly positive on every nonzero cone point. -/
lemma exists_strictly_positive_functional_on_nonzero_cone_points
    (K : Set (Fin 2 → ℝ))
    (h_closed : IsClosed K)
    (h_convex : Convex ℝ K)
    (h_cone : ∀ ⦃x : Fin 2 → ℝ⦄ ⦃a : ℝ⦄, x ∈ K → 0 ≤ a → a • x ∈ K)
    (hpointed : K ∩ (-K) = ({0} : Set (Fin 2 → ℝ)))
    (hint : Set.Nonempty (interior K)) :
    ∃ f : StrongDual ℝ (Fin 2 → ℝ),
      (∀ x : Fin 2 → ℝ, x ∈ K → 0 ≤ f x) ∧
      (∀ x : Fin 2 → ℝ, x ∈ K → x ≠ 0 → 0 < f x) := by
  let S : Set (Fin 2 → ℝ) := K ∩ Metric.sphere (0 : Fin 2 → ℝ) 1
  have hS_compact : IsCompact S := by
    -- The unit slice is the intersection of the closed cone with the compact unit sphere.
    simpa [S, Set.inter_comm] using (isCompact_sphere (0 : Fin 2 → ℝ) 1).inter_right h_closed
  have hS_nonempty : S.Nonempty := by
    -- Normalize a nonzero interior cone point onto the unit sphere.
    obtain ⟨z, hzK, hz0⟩ := exists_nonzero_of_nonempty_interior hint
    refine ⟨‖z‖⁻¹ • z, ?_⟩
    constructor
    · exact h_cone hzK (inv_nonneg.mpr (norm_nonneg _))
    · simpa [Metric.mem_sphere, dist_eq_norm, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)
  have hsep :
      ∀ y : Fin 2 → ℝ, y ∈ S →
        ∃ fy : StrongDual ℝ (Fin 2 → ℝ),
          (∀ x : Fin 2 → ℝ, x ∈ K → 0 ≤ fy x) ∧ 0 < fy y := by
    intro y hyS
    have hyK : y ∈ K := hyS.1
    have hy0 : y ≠ 0 := by
      intro hy0
      have hySphere : y ∈ Metric.sphere (0 : Fin 2 → ℝ) 1 := hyS.2
      rw [Metric.mem_sphere, hy0, dist_self] at hySphere
      norm_num at hySphere
    -- Pointwise separation on the compact unit slice gives local positivity neighborhoods.
    have hneg : -y ∉ K := neg_not_mem_of_pointed hpointed hyK hy0
    exact exists_nonneg_separating_functional K h_closed h_convex h_cone hyK hneg
  choose sep hsep_nonneg hsep_pos using hsep
  have hcover :
      S ⊆ ⋃ y ∈ (Set.univ : Set S), {x : Fin 2 → ℝ | 0 < sep y.1 y.2 x} := by
    intro x hxS
    -- Each unit cone point lies in the positivity set of its own separator.
    rw [Set.mem_iUnion]
    refine ⟨⟨x, hxS⟩, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨by simp, ?_⟩
    simpa using hsep_pos x hxS
  obtain ⟨q, -, hqfin, hqcover⟩ :
      ∃ q : Set S, q ⊆ (Set.univ : Set S) ∧ q.Finite ∧
        S ⊆ ⋃ y ∈ q, {x : Fin 2 → ℝ | 0 < sep y.1 y.2 x} := by
    exact hS_compact.elim_finite_subcover_image (b := (Set.univ : Set S))
      (fun y _ => isOpen_lt continuous_const (sep y.1 y.2).continuous) hcover
  let qf : Finset S := hqfin.toFinset
  let f : StrongDual ℝ (Fin 2 → ℝ) :=
    Finset.sum qf fun y => (sep y.1 y.2 : StrongDual ℝ (Fin 2 → ℝ))
  have hf_nonneg : ∀ x : Fin 2 → ℝ, x ∈ K → 0 ≤ f x := by
    intro x hxK
    -- Finite sums preserve nonnegativity on the cone.
    have :
        0 ≤ Finset.sum qf (fun y : S => (sep y.1 y.2 : StrongDual ℝ (Fin 2 → ℝ)) x) := by
      exact Finset.sum_nonneg fun y _ => hsep_nonneg y.1 y.2 x hxK
    simpa [f] using this
  have hf_pos_on_S : ∀ x : Fin 2 → ℝ, x ∈ S → 0 < f x := by
    intro x hxS
    -- A finite subcover witness contributes a strictly positive summand.
    have hxcover : x ∈ ⋃ y ∈ q, {x : Fin 2 → ℝ | 0 < sep y.1 y.2 x} := hqcover hxS
    simp only [Set.mem_iUnion] at hxcover
    rcases hxcover with ⟨y, hyq, hypos⟩
    have hyqf : y ∈ qf := by
      simpa [qf] using hqfin.mem_toFinset.mpr hyq
    have htail_nonneg :
        0 ≤ Finset.sum (qf.erase y) fun z => (sep z.1 z.2 : StrongDual ℝ (Fin 2 → ℝ)) x := by
      exact Finset.sum_nonneg fun z _ => hsep_nonneg z.1 z.2 x hxS.1
    have hle : sep y.1 y.2 x ≤ f x := by
      have hsum :
          f x =
            sep y.1 y.2 x +
              Finset.sum (qf.erase y) fun z => (sep z.1 z.2 : StrongDual ℝ (Fin 2 → ℝ)) x := by
        dsimp [f]
        rw [← Finset.sum_erase_add _ _ hyqf]
        simp [add_comm, add_left_comm, add_assoc]
      rw [hsum]
      linarith
    exact lt_of_lt_of_le hypos hle
  refine ⟨f, hf_nonneg, ?_⟩
  intro x hxK hx0
  let y : Fin 2 → ℝ := ‖x‖⁻¹ • x
  have hyS : y ∈ S := by
    -- Normalizing a nonzero cone point moves it onto the compact unit slice.
    constructor
    · exact h_cone hxK (inv_nonneg.mpr (norm_nonneg _))
    · unfold y
      simpa [Metric.mem_sphere, dist_eq_norm, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)
  have hypos : 0 < f y := hf_pos_on_S y hyS
  have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  -- Positivity on the normalized ray rescales back to positivity on the original cone point.
  have hscaled : 0 < ‖x‖⁻¹ * f x := by
    simpa [y, map_smul, smul_eq_mul] using hypos
  have hinv_nonneg : 0 ≤ ‖x‖⁻¹ := (inv_pos.mpr hnormpos).le
  nlinarith

/-- A functional that is strictly positive on every nonzero cone point cuts out a compact affine
slice of the cone. -/
lemma isCompact_normalized_slice_of_strictly_positive_functional
    (K : Set (Fin 2 → ℝ))
    (h_closed : IsClosed K)
    (h_cone : ∀ ⦃x : Fin 2 → ℝ⦄ ⦃a : ℝ⦄, x ∈ K → 0 ≤ a → a • x ∈ K)
    (hKnonzero : ∃ y : Fin 2 → ℝ, y ∈ K ∧ y ≠ 0)
    {f : StrongDual ℝ (Fin 2 → ℝ)}
    (hf_nonneg : ∀ x : Fin 2 → ℝ, x ∈ K → 0 ≤ f x)
    (hf_pos : ∀ x : Fin 2 → ℝ, x ∈ K → x ≠ 0 → 0 < f x) :
    IsCompact {x : Fin 2 → ℝ | x ∈ K ∧ f x = 1} := by
  let S : Set (Fin 2 → ℝ) := K ∩ Metric.sphere (0 : Fin 2 → ℝ) 1
  have hS_compact : IsCompact S := by
    -- The unit slice stays compact because the cone is closed.
    simpa [S, Set.inter_comm] using (isCompact_sphere (0 : Fin 2 → ℝ) 1).inter_right h_closed
  have hS_nonempty : S.Nonempty := by
    -- Normalize any nonzero cone point onto the unit sphere.
    rcases hKnonzero with ⟨z, hzK, hz0⟩
    refine ⟨‖z‖⁻¹ • z, ?_⟩
    constructor
    · exact h_cone hzK (inv_nonneg.mpr (norm_nonneg _))
    · simpa [Metric.mem_sphere, dist_eq_norm, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)
  obtain ⟨u, huS, huMin⟩ := hS_compact.exists_isMinOn hS_nonempty f.continuous.continuousOn
  have hu0 : u ≠ 0 := by
    intro hu0
    have huSphere : u ∈ Metric.sphere (0 : Fin 2 → ℝ) 1 := huS.2
    rw [Metric.mem_sphere, hu0, dist_self] at huSphere
    norm_num at huSphere
  have hu_pos : 0 < f u := hf_pos u huS.1 hu0
  have hslice_closed : IsClosed {x : Fin 2 → ℝ | x ∈ K ∧ f x = 1} := by
    -- The normalized slice is the intersection of the closed cone with a closed affine hyperplane.
    exact h_closed.inter (isClosed_eq f.continuous continuous_const)
  have hslice_subset :
      {x : Fin 2 → ℝ | x ∈ K ∧ f x = 1} ⊆ Metric.closedBall (0 : Fin 2 → ℝ) (f u)⁻¹ := by
    intro x hxSlice
    have hx0 : x ≠ 0 := by
      intro hx0
      have hfx : f x = 1 := hxSlice.2
      rw [hx0, map_zero] at hfx
      norm_num at hfx
    let y : Fin 2 → ℝ := ‖x‖⁻¹ • x
    have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hyS : y ∈ S := by
      -- Every slice point normalizes to the compact unit slice.
      constructor
      · exact h_cone hxSlice.1 (inv_nonneg.mpr (norm_nonneg _))
      · unfold y
        simpa [Metric.mem_sphere, dist_eq_norm, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)
    have huMin' : ∀ v ∈ S, f u ≤ f v := isMinOn_iff.mp huMin
    have hbound_inv : f u ≤ ‖x‖⁻¹ := by
      -- The minimal value on the unit slice bounds the reciprocal radius from below.
      calc
        f u ≤ f y := huMin' y hyS
        _ = ‖x‖⁻¹ := by
          unfold y
          rw [map_smul, hxSlice.2]
          simp [smul_eq_mul]
    have hmul_bound : ‖x‖ * f u ≤ 1 := by
      have :=
        mul_le_mul_of_nonneg_left hbound_inv (norm_nonneg x)
      simpa [mul_comm, mul_left_comm, mul_assoc,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0)] using this
    have hnorm_bound : ‖x‖ ≤ (f u)⁻¹ := by
      have : ‖x‖ ≤ 1 / f u := (le_div_iff₀ hu_pos).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_bound)
      simpa [one_div] using this
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_bound
  exact (isCompact_closedBall (0 : Fin 2 → ℝ) (f u)⁻¹).of_isClosed_subset hslice_closed hslice_subset

/-- In a convex cone, every nonnegative linear combination of two cone points stays in the cone. -/
lemma nonnegative_combo_mem_of_convex_cone
    {K : Set (Fin 2 → ℝ)}
    (h_convex : Convex ℝ K)
    (h_cone : ∀ ⦃x : Fin 2 → ℝ⦄ ⦃a : ℝ⦄, x ∈ K → 0 ≤ a → a • x ∈ K)
    {x y : Fin 2 → ℝ} (hx : x ∈ K) (hy : y ∈ K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • x + b • y ∈ K := by
  by_cases hsum : a + b = 0
  · -- If the coefficients sum to zero, nonnegativity forces both scaled points to vanish.
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simpa [ha0, hb0] using h_cone hx (show 0 ≤ (0 : ℝ) by norm_num)
  · -- Otherwise normalize to a convex combination and rescale back by the cone property.
    have hsum_nonneg : 0 ≤ a + b := add_nonneg ha hb
    have hsum_pos : 0 < a + b := lt_of_le_of_ne hsum_nonneg (Ne.symm hsum)
    have hline : AffineMap.lineMap x y (b / (a + b)) ∈ K := by
      apply h_convex.lineMap_mem hx hy
      refine ⟨div_nonneg hb hsum_pos.le, ?_⟩
      have hb_le : b ≤ a + b := by linarith
      have hq : b / (a + b) ≤ (a + b) / (a + b) :=
        div_le_div_of_nonneg_right hb_le hsum_nonneg
      simpa [hsum_pos.ne'] using hq
    have hscaled : (a + b) • AffineMap.lineMap x y (b / (a + b)) ∈ K := h_cone hline hsum_pos.le
    have hrewrite :
        a • x + b • y = (a + b) • AffineMap.lineMap x y (b / (a + b)) := by
      ext i <;> fin_cases i <;>
        simp [AffineMap.lineMap_apply, hsum_pos.ne'] <;>
        field_simp [hsum_pos.ne'] <;>
        ring
    exact hrewrite ▸ hscaled

/-- A vector in `ℝ²` decomposes against the two standard basis vectors. -/
lemma strongDual_apply_eq_stdBasis
    (f : StrongDual ℝ (Fin 2 → ℝ)) (x : Fin 2 → ℝ) :
    f x = x 0 * f ![1, 0] + x 1 * f ![0, 1] := by
  -- Expanding in the standard basis reduces every functional evaluation to two coordinates.
  have hx :
      x = x 0 • (![1, 0] : Fin 2 → ℝ) + x 1 • (![0, 1] : Fin 2 → ℝ) := by
    ext i <;> fin_cases i <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_smul, map_smul]
  simp [smul_eq_mul]

/-- The explicit nonzero direction orthogonal to a functional on `ℝ²`. -/
def kernelDirectionOfFunctional (f : StrongDual ℝ (Fin 2 → ℝ)) : Fin 2 → ℝ :=
  ![-f ![0, 1], f ![1, 0]]

/-- The explicit kernel direction is annihilated by the functional. -/
lemma apply_kernelDirectionOfFunctional
    (f : StrongDual ℝ (Fin 2 → ℝ)) :
    f (kernelDirectionOfFunctional f) = 0 := by
  -- The determinant-style construction cancels the two basis coefficients.
  rw [strongDual_apply_eq_stdBasis]
  simp [kernelDirectionOfFunctional]
  ring

/-- If a functional is nonzero somewhere, its explicit kernel direction is nonzero. -/
lemma kernelDirectionOfFunctional_ne_zero
    (f : StrongDual ℝ (Fin 2 → ℝ))
    {x : Fin 2 → ℝ} (hx : f x ≠ 0) :
    kernelDirectionOfFunctional f ≠ 0 := by
  intro hv
  have h01 : f ![0, 1] = 0 := by
    have := congrArg (fun v : Fin 2 → ℝ => v 0) hv
    simpa [kernelDirectionOfFunctional] using this
  have h10 : f ![1, 0] = 0 := by
    have := congrArg (fun v : Fin 2 → ℝ => v 1) hv
    simpa [kernelDirectionOfFunctional] using this
  apply hx
  rw [strongDual_apply_eq_stdBasis, h10, h01]
  ring

/-- Every vector annihilated by a nonzero functional on `ℝ²` lies on the explicit kernel ray. -/
lemma mem_span_kernelDirectionOfFunctional
    (f : StrongDual ℝ (Fin 2 → ℝ))
    {x witness : Fin 2 → ℝ}
    (hx : f x = 0) (hwitness : f witness ≠ 0) :
    x ∈ ℝ ∙ kernelDirectionOfFunctional f := by
  -- Route correction: instead of abstract finrank bookkeeping, solve the one-dimensional kernel
  -- directly in coordinates against the standard basis of `Fin 2 → ℝ`.
  have hcoord : x 0 * f ![1, 0] + x 1 * f ![0, 1] = 0 := by
    rw [← strongDual_apply_eq_stdBasis, hx]
  have hnotBoth : ¬ (f ![1, 0] = 0 ∧ f ![0, 1] = 0) := by
    intro hzero
    apply hwitness
    rw [strongDual_apply_eq_stdBasis, hzero.1, hzero.2]
    ring
  by_cases h10 : f ![1, 0] = 0
  · have h01 : f ![0, 1] ≠ 0 := by
      intro h01
      exact hnotBoth ⟨h10, h01⟩
    have hx1 : x 1 = 0 := by
      have hmul : x 1 * f ![0, 1] = 0 := by simpa [h10] using hcoord
      exact (mul_eq_zero.mp hmul).resolve_right h01
    refine Submodule.mem_span_singleton.2 ⟨-(x 0 / f ![0, 1]), ?_⟩
    ext i <;> fin_cases i
    · -- With the first basis coefficient vanishing, the kernel direction is horizontal.
      have hx0' : (-(x 0 / f ![0, 1]) • kernelDirectionOfFunctional f) 0 = x 0 := by
        simp [kernelDirectionOfFunctional, h10]
        field_simp [h01]
      simpa using hx0'
    · simp [kernelDirectionOfFunctional, h10, hx1]
  · refine Submodule.mem_span_singleton.2 ⟨x 1 / f ![1, 0], ?_⟩
    ext i <;> fin_cases i
    · have hx0mul : x 0 * f ![1, 0] = -(x 1 * f ![0, 1]) := by
        nlinarith
      have hx0div : x 0 = -(x 1 * f ![0, 1]) / f ![1, 0] := by
        exact (eq_div_iff h10).2 (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hx0mul)
      have hx0 : x 0 = -(x 1 / f ![1, 0]) * f ![0, 1] := by
        calc
          x 0 = -(x 1 * f ![0, 1]) / f ![1, 0] := hx0div
          _ = -(x 1 / f ![1, 0]) * f ![0, 1] := by
            field_simp [h10]
      simpa [kernelDirectionOfFunctional] using hx0.symm
    · have hx1' : x 1 = (x 1 / f ![1, 0]) * f ![1, 0] := by
        field_simp [h10]
      simpa [kernelDirectionOfFunctional, mul_comm] using hx1'.symm

/-- The complex number with real and imaginary parts given by the two coordinates of a vector in
`ℝ²`. -/
def complexOfVec (x : Fin 2 → ℝ) : ℂ :=
  x 0 + x 1 * Complex.I

/-- A nonzero vector in `ℝ²` gives a nonzero complex number under `complexOfVec`. -/
lemma complexOfVec_ne_zero
    {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    complexOfVec x ≠ 0 := by
  -- A vanishing complex representative would force both coordinates of the vector to vanish.
  intro hz
  apply hx
  ext i <;> fin_cases i
  · have hre : (complexOfVec x).re = 0 := by simpa [hz]
    simpa [complexOfVec] using hre
  · have him : (complexOfVec x).im = 0 := by simpa [hz]
    simpa [complexOfVec] using him

/-- Every nonzero vector is a positive scalar multiple of the unit boundary vector at its complex
argument. -/
lemma eq_norm_complexOfVec_smul_boundaryVec_arg
    {x : Fin 2 → ℝ} (hx : x ≠ 0) :
    x = ‖complexOfVec x‖ • boundaryVec (Complex.arg (complexOfVec x)) := by
  -- The complex argument recovers the direction, and the complex norm recovers the radius.
  ext i <;> fin_cases i
  · simp [complexOfVec, boundaryVec, Complex.norm_mul_cos_arg]
  · simp [complexOfVec, boundaryVec, Complex.norm_mul_sin_arg]

/-- The left determinant coordinate formula only needs a trigonometric coordinate representation. -/
lemma leftBoundaryCoeff_of_angle_rep (α β r φ : ℝ)
    (hsin : Real.sin (β - α) ≠ 0)
    {x : Fin 2 → ℝ}
    (hx0 : x 0 = r * Real.cos φ) (hx1 : x 1 = r * Real.sin φ) :
    leftBoundaryCoeff α β x = r * Real.sin (β - φ) / Real.sin (β - α) := by
  -- This is the same Cramer-rule computation as the sector-point version, without interval data.
  unfold leftBoundaryCoeff
  rw [hx0, hx1]
  field_simp [hsin]
  rw [Real.sin_sub]
  ring

/-- The right determinant coordinate formula only needs a trigonometric coordinate representation. -/
lemma rightBoundaryCoeff_of_angle_rep (α β r φ : ℝ)
    (hsin : Real.sin (β - α) ≠ 0)
    {x : Fin 2 → ℝ}
    (hx0 : x 0 = r * Real.cos φ) (hx1 : x 1 = r * Real.sin φ) :
    rightBoundaryCoeff α β x = r * Real.sin (φ - α) / Real.sin (β - α) := by
  -- This is the companion Cramer-rule computation for the right boundary coefficient.
  unfold rightBoundaryCoeff
  rw [hx0, hx1]
  field_simp [hsin]
  rw [Real.sin_sub]
  ring

/-- The determinant of the two unit boundary rays is `sin (β - α)`. -/
lemma boundaryVec_det (α β : ℝ) :
    boundaryVec α 0 * boundaryVec β 1 - boundaryVec α 1 * boundaryVec β 0 =
      Real.sin (β - α) := by
  -- Expanding both coordinates reduces the determinant to the sine subtraction formula.
  simp [boundaryVec, Real.sin_sub]
  ring

/-- A nonempty interior contains a nonzero interior point. -/
lemma exists_nonzero_mem_interior_of_nonempty_interior
    {K : Set (Fin 2 → ℝ)} (hK : Set.Nonempty (interior K)) :
    ∃ x : Fin 2 → ℝ, x ∈ interior K ∧ x ≠ 0 := by
  rcases hK with ⟨x, hxint⟩
  by_cases hx0 : x = 0
  · -- If the chosen interior point is the origin, move to a nearby nonzero point inside the same
    -- open neighborhood.
    subst hx0
    have hxnhds : interior K ∈ 𝓝 (0 : Fin 2 → ℝ) := isOpen_interior.mem_nhds hxint
    rw [Metric.mem_nhds_iff] at hxnhds
    rcases hxnhds with ⟨ε, hεpos, hεsub⟩
    have hsphere_nonempty : (Metric.sphere (0 : Fin 2 → ℝ) (ε / 2)).Nonempty := by
      exact NormedSpace.sphere_nonempty.mpr (by linarith)
    rcases hsphere_nonempty with ⟨y, hySphere⟩
    have hyBall : y ∈ Metric.ball (0 : Fin 2 → ℝ) ε := by
      -- Any point on the smaller sphere lies in the ambient open ball.
      have hydist : dist y (0 : Fin 2 → ℝ) = ε / 2 := by
        simpa [Metric.sphere, dist_comm] using hySphere
      rw [Metric.mem_ball, hydist]
      linarith
    refine ⟨y, hεsub hyBall, ?_⟩
    -- A point on a positive-radius sphere cannot be the origin.
    intro hy0
    rw [Metric.mem_sphere, hy0, dist_self] at hySphere
    linarith
  · -- Otherwise the original interior point is already nonzero.
    exact ⟨x, hxint, hx0⟩

/-- In `ℝ²`, vanishing determinant makes one vector a scalar multiple of the other. -/
lemma eq_smul_of_det_eq_zero
    {p q : Fin 2 → ℝ}
    (hp : p ≠ 0)
    (hdet : p 0 * q 1 - p 1 * q 0 = 0) :
    ∃ c : ℝ, q = c • p := by
  have hp0_or_hp1 : p 0 ≠ 0 ∨ p 1 ≠ 0 := by
    by_cases hp0 : p 0 = 0
    · right
      intro hp1
      apply hp
      ext i
      fin_cases i
      · exact hp0
      · exact hp1
    · exact Or.inl hp0
  rcases hp0_or_hp1 with hp0 | hp1
  · -- When the first coordinate is nonzero, solve for the scalar from that coordinate.
    refine ⟨q 0 / p 0, ?_⟩
    ext i
    fin_cases i
    · have h0 : (q 0 / p 0) * p 0 = q 0 := by
        field_simp [hp0]
      simpa [smul_eq_mul] using h0.symm
    · have h1 : q 1 = (q 0 / p 0) * p 1 := by
        have hmul : q 1 * p 0 = q 0 * p 1 := by
          linarith
        calc
          q 1 = (q 0 * p 1) / p 0 := (eq_div_iff hp0).2 hmul
          _ = (q 0 / p 0) * p 1 := by field_simp [hp0]
      simpa [smul_eq_mul, mul_comm] using h1
  · -- Otherwise the second coordinate is nonzero, so solve from that coordinate instead.
    refine ⟨q 1 / p 1, ?_⟩
    ext i
    fin_cases i
    · have h0 : q 0 = (q 1 / p 1) * p 0 := by
        have hmul : q 0 * p 1 = q 1 * p 0 := by
          linarith
        calc
          q 0 = (q 1 * p 0) / p 1 := (eq_div_iff hp1).2 hmul
          _ = (q 1 / p 1) * p 0 := by field_simp [hp1]
      simpa [smul_eq_mul, mul_comm] using h0
    · have h1 : (q 1 / p 1) * p 1 = q 1 := by
        field_simp [hp1]
      simpa [smul_eq_mul] using h1.symm

/-- A positively oriented pair of nonzero rays can be written as ordered boundary rays with angular
gap strictly between `0` and `π`. -/
lemma exists_angles_of_oriented_endpoint_rays
    {p q : Fin 2 → ℝ}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hdet : 0 < p 0 * q 1 - p 1 * q 0) :
    ∃ α β rp rq : ℝ,
      -Real.pi < α ∧
      α ≤ Real.pi ∧
      0 < rp ∧
      0 < rq ∧
      0 < β - α ∧
      β - α < Real.pi ∧
      p = rp • boundaryVec α ∧
      q = rq • boundaryVec β := by
  let α : ℝ := Complex.arg (complexOfVec p)
  let β₀ : ℝ := Complex.arg (complexOfVec q)
  let β : ℝ := if β₀ < α then β₀ + 2 * Real.pi else β₀
  let rp : ℝ := ‖complexOfVec p‖
  let rq : ℝ := ‖complexOfVec q‖
  have hrp : 0 < rp := by
    -- The radius of a nonzero complex representative is positive.
    exact norm_pos_iff.mpr (complexOfVec_ne_zero hp0)
  have hrq : 0 < rq := by
    -- The same positivity holds for the second endpoint.
    exact norm_pos_iff.mpr (complexOfVec_ne_zero hq0)
  have hp_repr : p = rp • boundaryVec α := by
    -- The complex argument and norm recover the first endpoint ray.
    simpa [rp, α] using eq_norm_complexOfVec_smul_boundaryVec_arg hp0
  have hq_repr₀ : q = rq • boundaryVec β₀ := by
    -- The same polar decomposition works for the second endpoint.
    simpa [rq, β₀] using eq_norm_complexOfVec_smul_boundaryVec_arg hq0
  have hβ_periodic : boundaryVec β = boundaryVec β₀ := by
    -- Adding `2π` does not change the unit boundary ray.
    by_cases hlt : β₀ < α
    · simp [β, hlt, β₀, boundaryVec]
    · simp [β, hlt]
  have hq_repr : q = rq • boundaryVec β := by
    -- Replace the principal-branch angle by the ordered representative when necessary.
    rw [hq_repr₀, hβ_periodic]
  have hβ_gt_α : α < β := by
    -- The adjusted second angle is chosen strictly to the right of the first.
    have hβ₀_ne_α : β₀ ≠ α := by
      intro hEq
      have hdet_zero :
          p 0 * q 1 - p 1 * q 0 = 0 := by
        rw [hp_repr, hq_repr₀, hEq]
        simp [boundaryVec]
        ring
      linarith
    by_cases hlt : β₀ < α
    · simp [β, hlt]
      have hgap : α - β₀ < 2 * Real.pi := by
        linarith [Complex.neg_pi_lt_arg (complexOfVec q), Complex.arg_le_pi (complexOfVec p),
          Real.pi_pos]
      linarith
    · simp [β, hlt]
      exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hβ₀_ne_α)
  have hβ_sub_α_lt_two_pi : β - α < 2 * Real.pi := by
    -- The ordered representative stays within one full turn of `α`.
    by_cases hlt : β₀ < α
    · have : 0 < α - β₀ := sub_pos.mpr hlt
      simp [β, hlt]
      linarith
    · simp [β, hlt]
      linarith [Complex.arg_le_pi (complexOfVec q), Complex.neg_pi_lt_arg (complexOfVec p),
        Real.pi_pos]
  have hdet_eq :
      p 0 * q 1 - p 1 * q 0 = rp * rq * Real.sin (β - α) := by
    -- Expanding both endpoints along their boundary rays identifies the determinant with the sine
    -- of the angular gap.
    calc
      p 0 * q 1 - p 1 * q 0 =
          rp * rq * (boundaryVec α 0 * boundaryVec β 1 - boundaryVec α 1 * boundaryVec β 0) := by
            rw [hp_repr, hq_repr]
            simp [smul_eq_mul]
            ring
      _ = rp * rq * Real.sin (β - α) := by rw [boundaryVec_det]
  have hsin_pos : 0 < Real.sin (β - α) := by
    have hprod_pos : 0 < rp * rq * Real.sin (β - α) := by
      simpa [hdet_eq] using hdet
    exact (mul_pos_iff_of_pos_left (mul_pos hrp hrq)).mp hprod_pos
  have hβ_sub_α_lt_pi : β - α < Real.pi := by
    -- Positive sine on the interval `(0, 2π)` forces the angle gap to be `< π`.
    by_contra hnot
    have hpi_le : Real.pi ≤ β - α := not_lt.mp hnot
    have htwo_pi_sub_nonneg : 0 ≤ 2 * Real.pi - (β - α) := by linarith
    have htwo_pi_sub_le_pi : 2 * Real.pi - (β - α) ≤ Real.pi := by linarith
    have hsin_nonneg : 0 ≤ Real.sin (2 * Real.pi - (β - α)) := by
      exact Real.sin_nonneg_of_mem_Icc ⟨htwo_pi_sub_nonneg, htwo_pi_sub_le_pi⟩
    have hsin_nonpos : Real.sin (β - α) ≤ 0 := by
      have hs : Real.sin (2 * Real.pi - (β - α)) = -Real.sin (β - α) := by
        simpa using Real.sin_two_pi_sub (β - α)
      linarith
    linarith
  refine ⟨α, β, rp, rq, Complex.neg_pi_lt_arg (complexOfVec p), Complex.arg_le_pi (complexOfVec p),
    hrp, hrq, sub_pos.mpr hβ_gt_α, hβ_sub_α_lt_pi, hp_repr, hq_repr⟩

/-- For an angular gap strictly between `0` and `π`, the nonnegative span of the two boundary rays
is exactly the corresponding polar sector. -/
lemma nonnegative_span_boundaryVec_eq_sector
    (α β : ℝ)
    (hα_left : -Real.pi < α)
    (hα_right : α ≤ Real.pi)
    (hdiff_pos : 0 < β - α)
    (hdiff_lt_pi : β - α < Real.pi) :
    {x : Fin 2 → ℝ |
      ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • boundaryVec α + b • boundaryVec β} =
      {x : Fin 2 → ℝ |
        ∃ r : ℝ, ∃ φ : Set.Icc α β,
          x 0 = r * Real.cos φ ∧
          x 1 = r * Real.sin φ ∧
          0 ≤ r} := by
  have hα_le_β : α ≤ β := by linarith
  have hsin_pos : 0 < Real.sin (β - α) := Real.sin_pos_of_pos_of_lt_pi hdiff_pos hdiff_lt_pi
  have hsin : Real.sin (β - α) ≠ 0 := hsin_pos.ne'
  ext x
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    by_cases hzero : a = 0 ∧ b = 0
    · -- The zero combination corresponds to radius `0`.
      refine ⟨0, ⟨⟨α, ⟨le_rfl, hα_le_β⟩⟩, ?_⟩⟩
      rcases hzero with ⟨ha0, hb0⟩
      simp [ha0, hb0, boundaryVec]
    · -- Otherwise use the complex argument of the nonzero combination to recover its angle.
      let y : Fin 2 → ℝ := a • boundaryVec α + b • boundaryVec β
      have hy0 : y ≠ 0 := by
        intro hy
        apply hzero
        have hleft :
            leftBoundaryCoeff α β y = 0 := by
          simpa [hy, leftBoundaryCoeff]
        have hright :
            rightBoundaryCoeff α β y = 0 := by
          simpa [hy, rightBoundaryCoeff]
        rw [leftBoundaryCoeff_of_boundaryCombination α β a b hsin] at hleft
        rw [rightBoundaryCoeff_of_boundaryCombination α β a b hsin] at hright
        exact ⟨hleft, hright⟩
      let r : ℝ := ‖complexOfVec y‖
      let φ₀ : ℝ := Complex.arg (complexOfVec y)
      let φ : ℝ := if φ₀ < α then φ₀ + 2 * Real.pi else φ₀
      have hr_pos : 0 < r := by
        -- The radius is positive because the boundary combination is nonzero.
        exact norm_pos_iff.mpr (complexOfVec_ne_zero hy0)
      have hy_repr : y = r • boundaryVec φ := by
        -- Adjust the principal-branch angle by `2π` only if it lies to the left of `α`.
        have hy_repr₀ : y = r • boundaryVec φ₀ := by
          simpa [y, r, φ₀] using eq_norm_complexOfVec_smul_boundaryVec_arg hy0
        have hperiodic : boundaryVec φ = boundaryVec φ₀ := by
          by_cases hlt : φ₀ < α
          · simp [φ, hlt, boundaryVec]
          · simp [φ, hlt]
        rw [hy_repr₀, hperiodic]
      have hright_formula :
          rightBoundaryCoeff α β y = r * Real.sin (φ - α) / Real.sin (β - α) := by
        -- Rewrite the determinant coordinate using the trigonometric representation of `y`.
        have hy0' : y 0 = r * Real.cos φ := by
          have := congrArg (fun z : Fin 2 → ℝ => z 0) hy_repr
          simpa [boundaryVec] using this
        have hy1' : y 1 = r * Real.sin φ := by
          have := congrArg (fun z : Fin 2 → ℝ => z 1) hy_repr
          simpa [boundaryVec] using this
        exact rightBoundaryCoeff_of_angle_rep α β r φ hsin hy0' hy1'
      have hleft_formula :
          leftBoundaryCoeff α β y = r * Real.sin (β - φ) / Real.sin (β - α) := by
        -- The left determinant coordinate has the companion sine-ratio formula.
        have hy0' : y 0 = r * Real.cos φ := by
          have := congrArg (fun z : Fin 2 → ℝ => z 0) hy_repr
          simpa [boundaryVec] using this
        have hy1' : y 1 = r * Real.sin φ := by
          have := congrArg (fun z : Fin 2 → ℝ => z 1) hy_repr
          simpa [boundaryVec] using this
        exact leftBoundaryCoeff_of_angle_rep α β r φ hsin hy0' hy1'
      have hsin_phi_nonneg : 0 ≤ Real.sin (φ - α) := by
        -- Nonnegative right coefficient means the adjusted angle is not below `α`.
        have hright_nonneg :
            0 ≤ rightBoundaryCoeff α β y := by
          rw [rightBoundaryCoeff_of_boundaryCombination α β a b hsin]
          exact hb
        rw [hright_formula] at hright_nonneg
        have hmul_nonneg : 0 ≤ r * Real.sin (φ - α) := by
          have hm :
              0 ≤ (r * Real.sin (φ - α) / Real.sin (β - α)) * Real.sin (β - α) :=
            mul_nonneg hright_nonneg hsin_pos.le
          simpa [div_eq_mul_inv, hsin_pos.ne', mul_assoc] using hm
        nlinarith [hmul_nonneg, hr_pos]
      have hφ_ge_α : α ≤ φ := by
        -- The angle was explicitly shifted by `2π` whenever it fell below `α`.
        by_cases hlt : φ₀ < α
        · simp [φ, hlt]
          linarith [hα_right, Complex.neg_pi_lt_arg (complexOfVec y), Real.pi_pos]
        · simp [φ, hlt]
          exact le_of_not_gt hlt
      have hφ_sub_lt_two_pi : φ - α < 2 * Real.pi := by
        -- The adjusted angle stays within one turn of `α`.
        by_cases hlt : φ₀ < α
        · simp [φ, hlt]
          have : 0 < α - φ₀ := sub_pos.mpr hlt
          linarith
        · simp [φ, hlt]
          linarith [Complex.arg_le_pi (complexOfVec y), hα_left, Real.pi_pos]
      have hφ_sub_le_pi : φ - α ≤ Real.pi := by
        -- Nonnegative sine on `[0, 2π)` rules out landing past `π`.
        by_contra hnot
        have hpi_lt : Real.pi < φ - α := not_le.mp hnot
        have htwo_pi_sub_pos : 0 < 2 * Real.pi - (φ - α) := by linarith
        have htwo_pi_sub_lt_pi : 2 * Real.pi - (φ - α) < Real.pi := by linarith
        have hsin_neg : Real.sin (φ - α) < 0 := by
          have hspos :
              0 < Real.sin (2 * Real.pi - (φ - α)) := by
            exact Real.sin_pos_of_pos_of_lt_pi htwo_pi_sub_pos htwo_pi_sub_lt_pi
          have hs : Real.sin (2 * Real.pi - (φ - α)) = -Real.sin (φ - α) := by
            simpa using Real.sin_two_pi_sub (φ - α)
          linarith
        exact not_le_of_gt hsin_neg hsin_phi_nonneg
      have hleft_nonneg :
          0 ≤ Real.sin (β - φ) := by
        -- The same sign argument for the left coefficient bounds the angle from above by `β`.
        have hleft_nonneg :
            0 ≤ leftBoundaryCoeff α β y := by
          rw [leftBoundaryCoeff_of_boundaryCombination α β a b hsin]
          exact ha
        rw [hleft_formula] at hleft_nonneg
        have hmul_nonneg : 0 ≤ r * Real.sin (β - φ) := by
          have hm :
              0 ≤ (r * Real.sin (β - φ) / Real.sin (β - α)) * Real.sin (β - α) :=
            mul_nonneg hleft_nonneg hsin_pos.le
          simpa [div_eq_mul_inv, hsin_pos.ne', mul_assoc] using hm
        nlinarith [hmul_nonneg, hr_pos]
      have hβ_ge_φ : φ ≤ β := by
        -- If `φ` were to the right of `β`, the left sine would be negative on `(-π, 0)`.
        by_contra hnot
        have hβ_sub_φ_neg : β - φ < 0 := sub_neg.mpr (lt_of_not_ge hnot)
        have hneg_pi_lt : -Real.pi < β - φ := by
          linarith [hdiff_lt_pi, hφ_sub_le_pi]
        have hsin_neg : Real.sin (β - φ) < 0 := by
          exact Real.sin_neg_of_neg_of_neg_pi_lt hβ_sub_φ_neg hneg_pi_lt
        exact not_le_of_gt hsin_neg hleft_nonneg
      refine ⟨r, ⟨⟨φ, ⟨hφ_ge_α, hβ_ge_φ⟩⟩, ?_⟩⟩
      have hy0' : y 0 = r * Real.cos φ := by
        have := congrArg (fun z : Fin 2 → ℝ => z 0) hy_repr
        simpa [boundaryVec] using this
      have hy1' : y 1 = r * Real.sin φ := by
        have := congrArg (fun z : Fin 2 → ℝ => z 1) hy_repr
        simpa [boundaryVec] using this
      simpa [y, r] using And.intro hy0' (And.intro hy1' hr_pos.le)
  · rintro ⟨r, φ, hx0, hx1, hr⟩
    -- Sector coordinates convert directly into nonnegative determinant coordinates.
    let a : ℝ := r * Real.sin (β - φ) / Real.sin (β - α)
    let b : ℝ := r * Real.sin (φ - α) / Real.sin (β - α)
    have ha_nonneg : 0 ≤ a := by
      have hsin_nonneg : 0 ≤ Real.sin (β - φ) := by
        apply Real.sin_nonneg_of_mem_Icc
        constructor
        · exact sub_nonneg.mpr φ.2.2
        · have : β - (φ : ℝ) ≤ β - α := by linarith [φ.2.1]
          linarith
      exact div_nonneg (mul_nonneg hr hsin_nonneg) hsin_pos.le
    have hb_nonneg : 0 ≤ b := by
      have hsin_nonneg : 0 ≤ Real.sin (φ - α) := by
        apply Real.sin_nonneg_of_mem_Icc
        constructor
        · exact sub_nonneg.mpr φ.2.1
        · have : (φ : ℝ) - α ≤ β - α := by linarith [φ.2.2]
          linarith
      exact div_nonneg (mul_nonneg hr hsin_nonneg) hsin_pos.le
    refine ⟨a, b, ha_nonneg, hb_nonneg, ?_⟩
    -- Cramer's formulas reconstruct the boundary coordinates from the polar point.
    have hreconstruct := boundaryCombination_eq_self α β x hsin
    rw [leftBoundaryCoeff_of_sectorPoint α β r φ hsin hx0 hx1,
      rightBoundaryCoeff_of_sectorPoint α β r φ hsin hx0 hx1] at hreconstruct
    simpa [a, b] using hreconstruct.symm

/-
Let K ⊆ ℝ² be a closed convex cone. A cone is proper if it is pointed and has nonempty interior. For
a proper cone K, define the generalized inequality ⪯_K by x ⪯_K y if and only if y - x ∈ K. Prove
that K is proper if and only if K is a sector {(r cos φ, r sin φ) | r ≥ 0 and α ≤ φ ≤ β} for some α,
β satisfying 0 < β - α < π.
-/
theorem proper_cone_iff_eq_sector
    (K : Set (Fin 2 → ℝ))
    (h_closed : IsClosed K)
    (h_convex : Convex ℝ K)
    (h_cone : ∀ ⦃x : Fin 2 → ℝ⦄ ⦃a : ℝ⦄, x ∈ K → 0 ≤ a → a • x ∈ K) :
    (K ∩ (-K) = ({0} : Set (Fin 2 → ℝ)) ∧ Set.Nonempty (interior K)) ↔
      ∃ α β : ℝ,
        0 < β - α ∧
        β - α < Real.pi ∧
        K =
          {x : Fin 2 → ℝ |
            ∃ r : ℝ, ∃ φ : Set.Icc α β,
              x 0 = r * Real.cos φ ∧
              x 1 = r * Real.sin φ ∧
              0 ≤ r} := by
  constructor
  · intro hproper
    rcases hproper with ⟨hpointed, hint⟩
    -- Route correction: the earlier one-point separator only controlled a single ray, so we switch
    -- to the finite-subcover construction of a functional that is positive on every nonzero ray.
    obtain ⟨z, hzK, hz0⟩ := exists_nonzero_of_nonempty_interior hint
    obtain ⟨f, hf_nonneg, hf_pos⟩ :=
      exists_strictly_positive_functional_on_nonzero_cone_points
        K h_closed h_convex h_cone hpointed hint
    let slice : Set (Fin 2 → ℝ) := {x : Fin 2 → ℝ | x ∈ K ∧ f x = 1}
    have hslice_nonempty : slice.Nonempty := by
      -- Normalizing the chosen ray gives a concrete point on the affine slice `f = 1`.
      refine ⟨(f z)⁻¹ • z, ?_⟩
      constructor
      · exact h_cone hzK (inv_nonneg.mpr (hf_pos z hzK hz0).le)
      · rw [map_smul]
        exact inv_mul_cancel₀ (hf_pos z hzK hz0).ne'
    have hslice_compact : IsCompact slice := by
      -- The strict positivity of `f` makes the normalized slice globally bounded.
      simpa [slice] using
        isCompact_normalized_slice_of_strictly_positive_functional
          K h_closed h_cone ⟨z, hzK, hz0⟩ hf_nonneg hf_pos
    have hslice_convex : Convex ℝ slice := by
      -- The normalized slice is the cone intersected with the affine hyperplane `f = 1`.
      intro x hx y hy a b ha hb hab
      constructor
      · exact h_convex hx.1 hy.1 ha hb hab
      · rw [map_add, map_smul, map_smul, hx.2, hy.2, smul_eq_mul, smul_eq_mul]
        ring_nf
        exact hab
    let v : Fin 2 → ℝ := kernelDirectionOfFunctional f
    have hvker : f v = 0 := apply_kernelDirectionOfFunctional f
    have hv0 : v ≠ 0 := kernelDirectionOfFunctional_ne_zero f (hf_pos z hzK hz0).ne'
    have hslice_diff_mem_span :
        ∀ {x y : Fin 2 → ℝ}, x ∈ slice → y ∈ slice → x - y ∈ ℝ ∙ v := by
      intro x y hx hy
      -- Equal slice values force differences into the one-dimensional kernel direction.
      apply mem_span_kernelDirectionOfFunctional f
      · rw [map_sub, hx.2, hy.2]
        ring
      · exact (hf_pos z hzK hz0).ne'
    obtain ⟨y, hyint, hy0⟩ := exists_nonzero_mem_interior_of_nonempty_interior hint
    have hyK : y ∈ K := interior_subset hyint
    have hfy : 0 < f y := hf_pos y hyK hy0
    rw [mem_interior_iff_mem_nhds] at hyint
    rw [Metric.mem_nhds_iff] at hyint
    obtain ⟨ε, hεpos, hεsub⟩ := hyint
    let t : ℝ := ε / (2 * ‖v‖)
    have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have ht_pos : 0 < t := by
      -- The perturbation size is positive because both the neighborhood radius and `‖v‖` are.
      unfold t
      positivity
    have htv_norm_lt : ‖t • v‖ < ε := by
      -- Scaling the kernel direction down by `ε / (2 ‖v‖)` stays strictly inside the interior ball.
      calc
        ‖t • v‖ = |t| * ‖v‖ := norm_smul t v
        _ = t * ‖v‖ := by rw [abs_of_nonneg ht_pos.le]
        _ = ε / 2 := by
          unfold t
          field_simp [hvnorm_pos.ne']
        _ < ε := by linarith
    have hyPlusK : y + t • v ∈ K := by
      -- The forward perturbation along the kernel direction stays in the interior neighborhood.
      apply hεsub
      rw [Metric.mem_ball, dist_eq_norm]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htv_norm_lt
    have hyMinusK : y - t • v ∈ K := by
      -- The backward perturbation stays in the same interior neighborhood by symmetry.
      apply hεsub
      rw [Metric.mem_ball, dist_eq_norm]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (show ‖-(t • v)‖ < ε by simpa using htv_norm_lt)
    have hfy_plus : f (y + t • v) = f y := by
      -- The kernel perturbation does not change the slice normalizing functional.
      rw [map_add, map_smul, hvker]
      ring
    have hfy_minus : f (y - t • v) = f y := by
      -- The same kernel computation works for the backward perturbation.
      rw [sub_eq_add_neg, map_add, map_smul, map_smul, hvker]
      ring
    let xPlus : Fin 2 → ℝ := (f y)⁻¹ • (y + t • v)
    let xMinus : Fin 2 → ℝ := (f y)⁻¹ • (y - t • v)
    have hxPlus_slice : xPlus ∈ slice := by
      -- Normalizing the forward perturbation lands back on the affine slice `f = 1`.
      constructor
      · exact h_cone hyPlusK (inv_nonneg.mpr hfy.le)
      · rw [show xPlus = (f y)⁻¹ • (y + t • v) by rfl, map_smul, hfy_plus]
        exact inv_mul_cancel₀ hfy.ne'
    have hxMinus_slice : xMinus ∈ slice := by
      -- Normalizing the backward perturbation gives a second point on the same slice.
      constructor
      · exact h_cone hyMinusK (inv_nonneg.mpr hfy.le)
      · rw [show xMinus = (f y)⁻¹ • (y - t • v) by rfl, map_smul, hfy_minus]
        exact inv_mul_cancel₀ hfy.ne'
    let i : Fin 2 := if h : v 0 = 0 then 1 else 0
    have hi : v i ≠ 0 := by
      -- One coordinate of the nonzero kernel direction must be nonzero.
      unfold i
      by_cases h : v 0 = 0
      · simp [h]
        intro hv1
        apply hv0
        ext j
        fin_cases j <;> simp [h, hv1]
      · simp [h]
    have hxCoord_ne : xPlus i ≠ xMinus i := by
      -- The two normalized perturbations stay distinct because they move in opposite directions
      -- along a coordinate where `v` is nonzero.
      intro hEq
      have hEqCoord : (f y)⁻¹ * ((y + t • v) i) = (f y)⁻¹ * ((y - t • v) i) := by
        simpa [xPlus, xMinus, smul_eq_mul] using congrArg (fun x : Fin 2 → ℝ => x i) hEq
      have hUnscaled := congrArg (fun r : ℝ => f y * r) hEqCoord
      have hsame : (y + t • v) i = (y - t • v) i := by
        simpa [mul_assoc, hfy.ne', smul_eq_mul] using hUnscaled
      have hvi_zero : v i = 0 := by
        have hplus_coord : (y + t • v) i = y i + t * v i := by
          simp [smul_eq_mul]
        have hminus_coord : (y - t • v) i = y i - t * v i := by
          simp [sub_eq_add_neg, smul_eq_mul]
        rw [hplus_coord, hminus_coord] at hsame
        nlinarith [ht_pos]
      exact hi hvi_zero
    obtain ⟨p, hp_slice, hp_min⟩ :=
      hslice_compact.exists_isMinOn hslice_nonempty (continuous_apply i).continuousOn
    obtain ⟨q, hq_slice, hq_max⟩ :=
      hslice_compact.exists_isMaxOn hslice_nonempty (continuous_apply i).continuousOn
    have hp_min' : ∀ x ∈ slice, p i ≤ x i := isMinOn_iff.mp hp_min
    have hq_max' : ∀ x ∈ slice, x i ≤ q i := isMaxOn_iff.mp hq_max
    have hp_lt_q : p i < q i := by
      -- The compact slice contains two distinct normalized perturbations, so its chosen coordinate
      -- must have distinct extrema.
      have hp_le_q : p i ≤ q i := hp_min' q hq_slice
      by_contra hnot
      have hq_le_p : q i ≤ p i := le_of_not_gt hnot
      have hp_eq_q : p i = q i := le_antisymm hp_le_q hq_le_p
      have hxPlus_eq : xPlus i = p i := by
        linarith [hp_min' xPlus hxPlus_slice, hq_max' xPlus hxPlus_slice]
      have hxMinus_eq : xMinus i = p i := by
        linarith [hp_min' xMinus hxMinus_slice, hq_max' xMinus hxMinus_slice]
      exact hxCoord_ne (by linarith)
    have hslice_segment :
        ∀ {x : Fin 2 → ℝ}, x ∈ slice →
          ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = AffineMap.lineMap p q t := by
      intro x hx
      -- Every slice point lies on the same affine line as `p` and `q`, and the extremal
      -- coordinate bounds force the line parameter into `[0, 1]`.
      have hx_span : x - p ∈ ℝ ∙ v := hslice_diff_mem_span hx hp_slice
      rcases Submodule.mem_span_singleton.mp hx_span with ⟨c, hc⟩
      have hq_span : q - p ∈ ℝ ∙ v := hslice_diff_mem_span hq_slice hp_slice
      rcases Submodule.mem_span_singleton.mp hq_span with ⟨d, hd⟩
      have hx_coord : x i - p i = c * v i := by
        have := congrArg (fun z : Fin 2 → ℝ => z i) hc
        simpa [smul_eq_mul] using this
      have hq_coord : q i - p i = d * v i := by
        have := congrArg (fun z : Fin 2 → ℝ => z i) hd
        simpa [smul_eq_mul] using this
      have hqp_ne : q i - p i ≠ 0 := sub_ne_zero.mpr (ne_of_gt hp_lt_q)
      let tx : ℝ := (x i - p i) / (q i - p i)
      have htx_mul : tx * d = c := by
        have hcoord :
            (tx * d) * v i = c * v i := by
          calc
            (tx * d) * v i = tx * (d * v i) := by ring
            _ = tx * (q i - p i) := by rw [hq_coord]
            _ = x i - p i := by
              unfold tx
              field_simp [hqp_ne]
            _ = c * v i := hx_coord
        exact (mul_right_cancel₀ hi).mp (by simpa [mul_assoc] using hcoord)
      have htx_nonneg : 0 ≤ tx := by
        -- The minimality of `p` makes the segment parameter nonnegative.
        unfold tx
        exact div_nonneg (sub_nonneg.mpr (hp_min' x hx)) (sub_nonneg.mpr (le_of_lt hp_lt_q))
      have htx_le_one : tx ≤ 1 := by
        -- The maximality of `q` bounds the same parameter above by `1`.
        have hx_le_q : x i - p i ≤ q i - p i := by
          linarith [hp_min' x hx, hq_max' x hx]
        unfold tx
        exact (div_le_iff (sub_pos.mpr hp_lt_q)).2 hx_le_q
      refine ⟨tx, ⟨htx_nonneg, htx_le_one⟩, ?_⟩
      -- Matching the line parameter on the distinguished coordinate identifies the whole point.
      rw [AffineMap.lineMap_apply_module']
      calc
        x = x - p + p := by
          symm
          exact sub_add_cancel x p
        _ = tx • (q - p) + p := by
          rw [hc, hd, smul_smul, htx_mul]
    have hcone_eq_span :
        K =
          {x : Fin 2 → ℝ |
            ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • p + b • q} := by
      ext x
      constructor
      · intro hxK
        -- Every nonzero cone point normalizes to the compact slice segment, then scales back to a
        -- nonnegative combination of the endpoint rays.
        by_cases hx0 : x = 0
        · refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
          simp [hx0]
        · have hfx : 0 < f x := hf_pos x hxK hx0
          let yx : Fin 2 → ℝ := (f x)⁻¹ • x
          have hyx_slice : yx ∈ slice := by
            constructor
            · exact h_cone hxK (inv_nonneg.mpr hfx.le)
            · rw [show yx = (f x)⁻¹ • x by rfl, map_smul]
              exact inv_mul_cancel₀ hfx.ne'
          obtain ⟨s, hs_mem, hs_line⟩ := hslice_segment hyx_slice
          refine ⟨f x * (1 - s), f x * s, ?_, ?_, ?_⟩
          · exact mul_nonneg hfx.le (sub_nonneg.mpr hs_mem.2)
          · exact mul_nonneg hfx.le hs_mem.1
          · calc
              x = f x • yx := by
                rw [show yx = (f x)⁻¹ • x by rfl, smul_smul]
                simp [hfx.ne']
              _ = f x • AffineMap.lineMap p q s := by rw [hs_line]
              _ = (f x * (1 - s)) • p + (f x * s) • q := by
                rw [AffineMap.lineMap_apply_module, smul_add, smul_smul, smul_smul]
      · rintro ⟨a, b, ha, hb, rfl⟩
        -- Nonnegative combinations of the endpoint slice points stay inside the convex cone.
        exact nonnegative_combo_mem_of_convex_cone h_convex h_cone hp_slice.1 hq_slice.1 ha hb
    have hp_nonzero : p ≠ 0 := by
      -- Slice points cannot be zero because the slice equation is `f x = 1`.
      intro hp0
      rw [hp0, map_zero] at hp_slice
      norm_num at hp_slice
    have hq_nonzero : q ≠ 0 := by
      -- The same normalization excludes zero for the other endpoint.
      intro hq0
      rw [hq0, map_zero] at hq_slice
      norm_num at hq_slice
    have hp_ne_q : p ≠ q := by
      -- Distinct extremal coordinate values force the endpoint vectors to be different.
      intro hpq
      have : p i = q i := by simpa [hpq]
      exact (ne_of_lt hp_lt_q) this
    have hdet_ne :
        p 0 * q 1 - p 1 * q 0 ≠ 0 := by
      -- If the determinant vanished, the two normalized endpoints would lie on the same ray, and
      -- the slice equation would then force them to coincide.
      intro hdet
      obtain ⟨c, hq_eq⟩ := eq_smul_of_det_eq_zero hp_nonzero hdet
      have hc : c = 1 := by
        rw [hq_eq, map_smul, hp_slice.2] at hq_slice
        linarith
      have hpq : p = q := by
        simpa [hc] using hq_eq.symm
      exact hp_ne_q hpq
    have hspan_boundary_eq :
        ∀ {u w : Fin 2 → ℝ} {ru rw α β : ℝ},
          0 < ru →
          0 < rw →
          u = ru • boundaryVec α →
          w = rw • boundaryVec β →
          {x : Fin 2 → ℝ |
            ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • u + b • w} =
            {x : Fin 2 → ℝ |
              ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • boundaryVec α + b • boundaryVec β} := by
      intro u w ru rw α β hru hrw hu hw
      -- Positive ray lengths can be absorbed into or pulled out of the nonnegative coefficients.
      ext x
      constructor
      · rintro ⟨a, b, ha, hb, rfl⟩
        refine ⟨a * ru, b * rw, mul_nonneg ha hru.le, mul_nonneg hb hrw.le, ?_⟩
        rw [hu, hw, smul_smul, smul_smul]
        simpa [mul_assoc, mul_left_comm, mul_comm]
      · rintro ⟨a, b, ha, hb, rfl⟩
        refine ⟨a * ru⁻¹, b * rw⁻¹, mul_nonneg ha (inv_nonneg.mpr hru.le),
          mul_nonneg hb (inv_nonneg.mpr hrw.le), ?_⟩
        rw [hu, hw, smul_smul, smul_smul]
        simp [mul_assoc, mul_left_comm, mul_comm, hru.ne', hrw.ne']
    have hspan_swap :
        {x : Fin 2 → ℝ |
          ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • p + b • q} =
          {x : Fin 2 → ℝ |
            ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • q + b • p} := by
      -- Swapping the endpoint rays only swaps the two nonnegative coefficients.
      ext x
      constructor
      · rintro ⟨a, b, ha, hb, rfl⟩
        exact ⟨b, a, hb, ha, by simpa [add_comm]⟩
      · rintro ⟨a, b, ha, hb, rfl⟩
        exact ⟨b, a, hb, ha, by simpa [add_comm]⟩
    by_cases hdet_pos : 0 < p 0 * q 1 - p 1 * q 0
    · obtain ⟨α, β, rp, rq, hα_left, hα_right, hrp, hrq, hdiff_pos, hdiff_lt_pi,
        hp_repr, hq_repr⟩ :=
          exists_angles_of_oriented_endpoint_rays hp_nonzero hq_nonzero hdet_pos
      refine ⟨α, β, hdiff_pos, hdiff_lt_pi, ?_⟩
      -- The ordered endpoint rays identify the cone with the corresponding polar sector.
      calc
        K =
            {x : Fin 2 → ℝ |
              ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • p + b • q} := hcone_eq_span
        _ =
            {x : Fin 2 → ℝ |
              ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • boundaryVec α + b • boundaryVec β} := by
                exact hspan_boundary_eq hrp hrq hp_repr hq_repr
        _ =
            {x : Fin 2 → ℝ |
              ∃ r : ℝ, ∃ φ : Set.Icc α β,
                x 0 = r * Real.cos φ ∧
                x 1 = r * Real.sin φ ∧
                0 ≤ r} :=
              nonnegative_span_boundaryVec_eq_sector α β hα_left hα_right hdiff_pos hdiff_lt_pi
    · have hdet_neg : p 0 * q 1 - p 1 * q 0 < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hdet_pos) hdet_ne
      have hswap_pos : 0 < q 0 * p 1 - q 1 * p 0 := by
        linarith
      obtain ⟨α, β, rq, rp, hα_left, hα_right, hrq, hrp, hdiff_pos, hdiff_lt_pi,
        hq_repr, hp_repr⟩ :=
          exists_angles_of_oriented_endpoint_rays hq_nonzero hp_nonzero hswap_pos
      refine ⟨α, β, hdiff_pos, hdiff_lt_pi, ?_⟩
      -- If the determinant is negative, swap the endpoints before applying the same sector
      -- description.
      calc
        K =
            {x : Fin 2 → ℝ |
              ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • p + b • q} := hcone_eq_span
        _ =
            {x : Fin 2 → ℝ |
              ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • q + b • p} := hspan_swap
        _ =
            {x : Fin 2 → ℝ |
              ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • boundaryVec α + b • boundaryVec β} := by
                exact hspan_boundary_eq hrq hrp hq_repr hp_repr
        _ =
            {x : Fin 2 → ℝ |
              ∃ r : ℝ, ∃ φ : Set.Icc α β,
                x 0 = r * Real.cos φ ∧
                x 1 = r * Real.sin φ ∧
                0 ≤ r} :=
              nonnegative_span_boundaryVec_eq_sector α β hα_left hα_right hdiff_pos hdiff_lt_pi
  · rintro ⟨α, β, hdiff_pos, hdiff_lt_pi, rfl⟩
    let sector : Set (Fin 2 → ℝ) :=
      {x : Fin 2 → ℝ |
        ∃ r : ℝ, ∃ φ : Set.Icc α β,
          x 0 = r * Real.cos φ ∧
          x 1 = r * Real.sin φ ∧
          0 ≤ r}
    have hα_le_β : α ≤ β := by linarith
    have hsin_pos : 0 < Real.sin (β - α) := Real.sin_pos_of_pos_of_lt_pi hdiff_pos hdiff_lt_pi
    have hsin : Real.sin (β - α) ≠ 0 := hsin_pos.ne'
    have hzero_mem : (0 : Fin 2 → ℝ) ∈ sector := by
      -- Radius zero places the origin in every sector.
      refine ⟨0, ⟨⟨α, ⟨le_rfl, hα_le_β⟩⟩, ?_⟩⟩
      simp [sector]
    have hleft_mem : boundaryVec α ∈ sector := by
      -- The left boundary ray is realized at radius `1` and angle `α`.
      refine ⟨1, ⟨⟨α, ⟨le_rfl, hα_le_β⟩⟩, ?_⟩⟩
      simp [boundaryVec, sector]
    have hright_mem : boundaryVec β ∈ sector := by
      -- The right boundary ray is realized at radius `1` and angle `β`.
      refine ⟨1, ⟨⟨β, ⟨hα_le_β, le_rfl⟩⟩, ?_⟩⟩
      simp [boundaryVec, sector]
    have hcombo_mem :
        ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b →
          a • boundaryVec α + b • boundaryVec β ∈ sector := by
      intro a b ha hb
      by_cases hsum : a + b = 0
      · -- If the coefficients sum to zero, nonnegativity forces both to vanish.
        have ha0 : a = 0 := by linarith
        have hb0 : b = 0 := by linarith
        simpa [ha0, hb0] using hzero_mem
      · -- Otherwise we normalize to a convex combination and rescale back by the cone property.
        have hsum_nonneg : 0 ≤ a + b := add_nonneg ha hb
        have hsum_pos : 0 < a + b := by
          exact lt_of_le_of_ne hsum_nonneg (Ne.symm hsum)
        have hline :
            AffineMap.lineMap (boundaryVec α) (boundaryVec β) (b / (a + b)) ∈ sector := by
          apply h_convex.lineMap_mem hleft_mem hright_mem
          refine ⟨div_nonneg hb hsum_pos.le, ?_⟩
          have hb_le : b ≤ a + b := by linarith
          have hq : b / (a + b) ≤ (a + b) / (a + b) :=
            div_le_div_of_nonneg_right hb_le hsum_nonneg
          simpa [hsum_pos.ne'] using hq
        have hscaled : (a + b) • AffineMap.lineMap (boundaryVec α) (boundaryVec β) (b / (a + b)) ∈
            sector := h_cone hline hsum_pos.le
        have hrewrite :
            a • boundaryVec α + b • boundaryVec β =
              (a + b) • AffineMap.lineMap (boundaryVec α) (boundaryVec β) (b / (a + b)) := by
          ext i <;> fin_cases i
          · simp [AffineMap.lineMap_apply, boundaryVec, hsum_pos.ne']
            field_simp [hsum_pos.ne']
            ring
          · simp [AffineMap.lineMap_apply, boundaryVec, hsum_pos.ne']
            field_simp [hsum_pos.ne']
            ring
        exact hrewrite ▸ hscaled
    have hboundary_zero :
        ∀ {a b : ℝ}, a • boundaryVec α + b • boundaryVec β = 0 → a = 0 ∧ b = 0 := by
      intro a b hab
      -- Applying the two determinant coordinates separates the two boundary coefficients.
      have hleft :
          leftBoundaryCoeff α β (a • boundaryVec α + b • boundaryVec β) = 0 := by
        exact by
          rw [hab]
          simp [leftBoundaryCoeff, hsin]
      have hright :
          rightBoundaryCoeff α β (a • boundaryVec α + b • boundaryVec β) = 0 := by
        exact by
          rw [hab]
          simp [rightBoundaryCoeff, hsin]
      rw [leftBoundaryCoeff_of_boundaryCombination α β a b hsin] at hleft
      rw [rightBoundaryCoeff_of_boundaryCombination α β a b hsin] at hright
      exact ⟨hleft, hright⟩
    have hsector_inter_neg : (sector ∩ -sector : Set (Fin 2 → ℝ)) = ({0} : Set (Fin 2 → ℝ)) := by
      ext x
      constructor
      · intro hx
        -- Writing `x` and `-x` in boundary coordinates turns the intersection condition into a
        -- nonnegative linear relation among the boundary rays.
        rcases hx.1 with ⟨r, φ, hx0, hx1, hr⟩
        have hxneg : -x ∈ sector := by simpa using hx.2
        rcases hxneg with ⟨s, ψ, hxneg0, hxneg1, hs⟩
        let a : ℝ := r * Real.sin (β - φ) / Real.sin (β - α)
        let b : ℝ := r * Real.sin (φ - α) / Real.sin (β - α)
        let a' : ℝ := s * Real.sin (β - ψ) / Real.sin (β - α)
        let b' : ℝ := s * Real.sin (ψ - α) / Real.sin (β - α)
        have ha_nonneg : 0 ≤ a := by
          have hsin_nonneg : 0 ≤ Real.sin (β - φ) := by
            apply Real.sin_nonneg_of_mem_Icc
            constructor
            · exact sub_nonneg.mpr φ.2.2
            · have : β - (φ : ℝ) ≤ β - α := by linarith [φ.2.1]
              linarith
          exact div_nonneg (mul_nonneg hr hsin_nonneg) hsin_pos.le
        have hb_nonneg : 0 ≤ b := by
          have hsin_nonneg : 0 ≤ Real.sin (φ - α) := by
            apply Real.sin_nonneg_of_mem_Icc
            constructor
            · exact sub_nonneg.mpr φ.2.1
            · have : (φ : ℝ) - α ≤ β - α := by linarith [φ.2.2]
              linarith
          exact div_nonneg (mul_nonneg hr hsin_nonneg) hsin_pos.le
        have ha'_nonneg : 0 ≤ a' := by
          have hsin_nonneg : 0 ≤ Real.sin (β - ψ) := by
            apply Real.sin_nonneg_of_mem_Icc
            constructor
            · exact sub_nonneg.mpr ψ.2.2
            · have : β - (ψ : ℝ) ≤ β - α := by linarith [ψ.2.1]
              linarith
          exact div_nonneg (mul_nonneg hs hsin_nonneg) hsin_pos.le
        have hb'_nonneg : 0 ≤ b' := by
          have hsin_nonneg : 0 ≤ Real.sin (ψ - α) := by
            apply Real.sin_nonneg_of_mem_Icc
            constructor
            · exact sub_nonneg.mpr ψ.2.1
            · have : (ψ : ℝ) - α ≤ β - α := by linarith [ψ.2.2]
              linarith
          exact div_nonneg (mul_nonneg hs hsin_nonneg) hsin_pos.le
        have hx_boundary :
            a • boundaryVec α + b • boundaryVec β = x := by
          -- Cramer's formulas convert the polar coordinates of `x` into boundary coefficients.
          have hreconstruct := boundaryCombination_eq_self α β x hsin
          rw [leftBoundaryCoeff_of_sectorPoint α β r φ hsin hx0 hx1,
            rightBoundaryCoeff_of_sectorPoint α β r φ hsin hx0 hx1] at hreconstruct
          simpa [a, b] using hreconstruct
        have hxneg_boundary :
            a' • boundaryVec α + b' • boundaryVec β = -x := by
          -- The same boundary-coordinate formula applies to the representation of `-x`.
          have hreconstruct := boundaryCombination_eq_self α β (-x) hsin
          rw [leftBoundaryCoeff_of_sectorPoint α β s ψ hsin hxneg0 hxneg1,
            rightBoundaryCoeff_of_sectorPoint α β s ψ hsin hxneg0 hxneg1] at hreconstruct
          simpa [a', b'] using hreconstruct
        have hsum_zero :
            (a + a') • boundaryVec α + (b + b') • boundaryVec β = 0 := by
          calc
            (a + a') • boundaryVec α + (b + b') • boundaryVec β =
                (a • boundaryVec α + b • boundaryVec β) +
                  (a' • boundaryVec α + b' • boundaryVec β) := by
                  simp [add_smul, smul_add, add_assoc, add_left_comm, add_comm]
            _ = x + (-x) := by rw [hx_boundary, hxneg_boundary]
            _ = 0 := by simp
        have hcoeff_zero := hboundary_zero hsum_zero
        have ha_zero : a = 0 := by linarith
        have hb_zero : b = 0 := by linarith
        have hx_zero : x = 0 := by
          rw [← hx_boundary, ha_zero, hb_zero]
          simp
        simpa [hx_zero]
      · rintro rfl
        exact ⟨hzero_mem, by simpa using hzero_mem⟩
    let wedgeInterior : Set (Fin 2 → ℝ) :=
      {x : Fin 2 → ℝ |
        0 < leftBoundaryCoeff α β x ∧ 0 < rightBoundaryCoeff α β x}
    have hwedge_open : IsOpen wedgeInterior := by
      -- The strict determinant inequalities define an open set.
      have hleft_cont : Continuous (leftBoundaryCoeff α β) := by
        have h0 : Continuous fun x : Fin 2 → ℝ => x 0 := continuous_apply 0
        have h1 : Continuous fun x : Fin 2 → ℝ => x 1 := continuous_apply 1
        have hnum : Continuous fun x : Fin 2 → ℝ => x 0 * Real.sin β - x 1 * Real.cos β :=
          (h0.mul continuous_const).sub (h1.mul continuous_const)
        simpa [leftBoundaryCoeff, div_eq_mul_inv] using hnum.mul continuous_const
      have hright_cont : Continuous (rightBoundaryCoeff α β) := by
        have h0 : Continuous fun x : Fin 2 → ℝ => x 0 := continuous_apply 0
        have h1 : Continuous fun x : Fin 2 → ℝ => x 1 := continuous_apply 1
        have hnum : Continuous fun x : Fin 2 → ℝ => -(x 0 * Real.sin α) + x 1 * Real.cos α := by
          simpa [neg_mul] using ((h0.mul continuous_const).neg.add (h1.mul continuous_const))
        unfold rightBoundaryCoeff
        simpa [div_eq_mul_inv, neg_mul] using hnum.mul continuous_const
      simpa [wedgeInterior] using
        (isOpen_lt continuous_const hleft_cont).inter (isOpen_lt continuous_const hright_cont)
    have hwedge_subset : wedgeInterior ⊆ sector := by
      intro x hx
      -- Positive determinant coordinates reconstruct `x` as a positive boundary combination.
      have hmem :
          leftBoundaryCoeff α β x • boundaryVec α +
            rightBoundaryCoeff α β x • boundaryVec β ∈ sector :=
        hcombo_mem hx.1.le hx.2.le
      simpa [boundaryCombination_eq_self α β x hsin] using hmem
    have hwedge_nonempty : Set.Nonempty wedgeInterior := by
      -- The sum of the two boundary rays has determinant coordinates `(1, 1)`.
      refine ⟨boundaryVec α + boundaryVec β, ?_⟩
      constructor
      · simpa using (show
            0 < leftBoundaryCoeff α β ((1 : ℝ) • boundaryVec α + (1 : ℝ) • boundaryVec β) by
              rw [leftBoundaryCoeff_of_boundaryCombination α β 1 1 hsin]
              norm_num)
      · simpa using (show
            0 < rightBoundaryCoeff α β ((1 : ℝ) • boundaryVec α + (1 : ℝ) • boundaryVec β) by
              rw [rightBoundaryCoeff_of_boundaryCombination α β 1 1 hsin]
              norm_num)
    refine ⟨hsector_inter_neg, ?_⟩
    rcases hwedge_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hwedge_open.mem_nhds hx) hwedge_subset

/-
Let K ⊆ ℝ² be a closed convex cone, and define x ⪯_K y to mean y - x ∈ K. Prove that x ⪯_K y if and
only if y ∈ x + K.
-/
theorem generalizedInequality_iff_mem_translate
    (K : Set (Fin 2 → ℝ))
    (x y : Fin 2 → ℝ) :
    generalizedInequality K x y ↔ y ∈ ((fun z : Fin 2 → ℝ => x + z) '' K) := by
  -- Rewriting the generalized inequality is exactly translating the cone by the base point `x`.
  unfold generalizedInequality
  constructor
  · intro h
    refine ⟨y - x, h, ?_⟩
    ext i
    simp
  · rintro ⟨z, hz, rfl⟩
    simpa
end «problem-19»
