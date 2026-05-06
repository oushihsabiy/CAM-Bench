import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-127»
/-
For a cone K ⊆ ℝ^n, its dual cone is K* = {y ∈ ℝ^n | yᵀ x ≥ 0 for all x ∈ K}.
-/
open scoped RealInnerProductSpace

def dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ K, 0 ≤ ⟪y, x⟫}

/-- The coordinatewise nonnegative cone in `EuclideanSpace ℝ (Fin m)`. -/
private def positiveOrthant (m : ℕ) : ProperCone ℝ (EuclideanSpace ℝ (Fin m)) where
  toSubmodule :=
    PointedCone.ofConeComb
      {v : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, 0 ≤ v i}
      ⟨0, by simp⟩
      (by
        intro x hx y hy a ha b hb i
        exact add_nonneg (smul_nonneg ha (hx i)) (smul_nonneg hb (hy i)))
  isClosed' := by
    have hclosed : IsClosed {v : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, 0 ≤ v i} := by
      classical
      rw [show ({v : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, 0 ≤ v i} :
          Set (EuclideanSpace ℝ (Fin m))) =
          ⋂ i : Fin m, {v : EuclideanSpace ℝ (Fin m) | (0 : ℝ) ≤ v i} by
        ext v
        simp]
      exact isClosed_iInter
        (fun i : Fin m => isClosed_le continuous_const (by fun_prop))
    exact hclosed

/-- Membership in the coordinatewise nonnegative cone is coordinatewise nonnegativity. -/
@[simp] private lemma mem_positiveOrthant {m : ℕ} {x : EuclideanSpace ℝ (Fin m)} :
    x ∈ positiveOrthant m ↔ ∀ i : Fin m, 0 ≤ x i := Iff.rfl

/-- The coordinatewise nonnegative cone is self-dual for the Euclidean inner product. -/
private lemma innerDual_positiveOrthant {m : ℕ} :
    ProperCone.innerDual (positiveOrthant m : Set (EuclideanSpace ℝ (Fin m))) =
      positiveOrthant m := by
  ext y
  constructor
  · intro hy
    rw [ProperCone.mem_innerDual] at hy
    -- Test the dual inequality on the standard basis vector to recover one coordinate.
    exact fun i => by
      have h := hy (x := EuclideanSpace.single i (1 : ℝ)) (by
        intro j
        by_cases hji : j = i
        · subst hji
          rw [EuclideanSpace.single_apply]
          positivity
        · rw [EuclideanSpace.single_apply]
          simp [hji])
      simpa [EuclideanSpace.inner_single_left] using h
  · intro hy
    rw [ProperCone.mem_innerDual]
    intro x hx
    -- Expand the inner product as a finite sum of coordinatewise nonnegative terms.
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hy i) (hx i)

/-- `Matrix.toEuclideanLin` agrees with `mulVec` on Euclidean space coordinates. -/
private lemma toEuclideanLin_eq_mulVec {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin A x = A.mulVec x := by
  -- Read the bundled map back in coordinates.
  ext i
  exact congrArg (fun y : EuclideanSpace ℝ (Fin m) => y i)
    (Matrix.toLpLin_apply (p := 2) (q := 2) A x)

/-- The adjoint of the transpose map is the original matrix map. -/
private lemma adjoint_toEuclideanLin_transpose {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ((Matrix.toEuclideanLin Aᵀ).toContinuousLinearMap).adjoint =
      (Matrix.toEuclideanLin A).toContinuousLinearMap := by
  -- Convert the continuous adjoint statement back to the linear-map adjoint theorem.
  change (LinearMap.adjoint (Matrix.toEuclideanLin Aᵀ)).toContinuousLinearMap =
    (Matrix.toEuclideanLin A).toContinuousLinearMap
  simpa using congrArg LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := Aᵀ)).symm

/-- The abstract cone image from `relative_hyperplane_separation` is the closure of the explicit
transpose image cone. -/
private lemma positiveOrthant_map_eq_closure_transpose_nonnegative_image
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ((positiveOrthant m).map ((Matrix.toEuclideanLin Aᵀ).toContinuousLinearMap) :
        Set (EuclideanSpace ℝ (Fin n))) =
      closure {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  have himage :
      ((Matrix.toEuclideanLin Aᵀ) '' (positiveOrthant m : Set (EuclideanSpace ℝ (Fin m)))) =
        {y : EuclideanSpace ℝ (Fin n) |
          ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
    ext y
    constructor
    · rintro ⟨v, hv, hvy⟩
      have hmul : ((Matrix.toEuclideanLin Aᵀ) v).ofLp = Aᵀ *ᵥ v.ofLp := by
        exact toEuclideanLin_eq_mulVec Aᵀ v
      exact ⟨v, hv, (congrArg (fun z => z.ofLp) hvy).symm.trans hmul⟩
    · rintro ⟨v, hv, hvy⟩
      have hmul : ((Matrix.toEuclideanLin Aᵀ) v).ofLp = Aᵀ *ᵥ v.ofLp := by
        exact toEuclideanLin_eq_mulVec Aᵀ v
      refine ⟨v, hv, ?_⟩
      ext i
      exact congrArg (fun z : Fin n → ℝ => z i) (hmul.trans hvy.symm)
  -- `ProperCone.map` is defined as the closure of the pointed-cone image.
  simpa [ProperCone.coe_map, PointedCone.coe_map] using congrArg closure himage

/-- The dual cone is exactly the closure of the transpose image of the nonnegative orthant. -/
private lemma dualCone_eq_closure_transpose_nonnegative_image
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    dualCone {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, 0 ≤ (A.mulVec x) i} =
      closure {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  calc
    dualCone {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, 0 ≤ (A.mulVec x) i} =
        ((positiveOrthant m).map ((Matrix.toEuclideanLin Aᵀ).toContinuousLinearMap) :
          Set (EuclideanSpace ℝ (Fin n))) := by
          ext y
          -- Route correction: use a custom positive orthant on `EuclideanSpace` rather than
          -- `ProperCone.positive`, since this checkout has no order instance on `EuclideanSpace`.
          simpa [dualCone, adjoint_toEuclideanLin_transpose, innerDual_positiveOrthant,
            mem_positiveOrthant, toEuclideanLin_eq_mulVec, real_inner_comm,
            forall_and_left] using
            (ProperCone.relative_hyperplane_separation
              (C := positiveOrthant m)
              (f := (Matrix.toEuclideanLin Aᵀ).toContinuousLinearMap)
              (b := y)).symm
    _ = closure {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} :=
      positiveOrthant_map_eq_closure_transpose_nonnegative_image A

/-- The `i`-th row of `A`, viewed as a vector in Euclidean space. -/
private noncomputable def rowVector {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (A i)

/-- The coordinate subspace consisting of vectors supported on `s`. -/
private noncomputable abbrev supportedSubmodule {m : ℕ} (s : Finset (Fin m)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  ⨅ i : {i // i ∉ s}, LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (i := i.1))

/-- Membership in the supported subspace is exactly vanishing off the chosen support. -/
@[simp] private lemma mem_supportedSubmodule {m : ℕ}
    (s : Finset (Fin m)) (v : EuclideanSpace ℝ (Fin m)) :
    v ∈ supportedSubmodule s ↔ ∀ i ∉ s, v i = 0 := by
  -- Unfold the infimum of coordinate kernels into coordinatewise vanishing.
  simp [supportedSubmodule]

/-- Expanding `Aᵀ.mulVec v` as a finite sum of row vectors. -/
private lemma transpose_mulVec_eq_sum_rows {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin m)) :
    Matrix.toEuclideanLin Aᵀ v = ∑ i : Fin m, v i • rowVector A i := by
  -- Compare coordinates and rewrite the matrix-vector product as a dot product.
  ext j
  simp [rowVector, Matrix.mulVec, dotProduct, mul_comm]

/-- For a supported vector, the row expansion only depends on the chosen support. -/
private lemma sum_rows_eq_sum_rows_support {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) (v : supportedSubmodule s) :
    ∑ i : Fin m, v.1 i • rowVector A i = ∑ i ∈ s, v.1 i • rowVector A i := by
  -- Terms outside `s` vanish because the vector is zero there.
  refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
  intro i _ hi
  have hvi : v.1 i = 0 := (mem_supportedSubmodule s v.1).mp v.2 i hi
  simp [hvi]

/-- The transpose map is injective on vectors supported on an independent row family. -/
private lemma supported_row_map_ker_eq_bot {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m))
    (hli : LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s) :
    LinearMap.ker ((Matrix.toEuclideanLin Aᵀ).comp (supportedSubmodule s).subtype) = ⊥ := by
  ext v
  constructor
  · intro hv
    -- Show each supported coefficient vanishes by the linear independence on `s`.
    rw [Submodule.mem_bot]
    ext i
    by_cases hi : i ∈ s
    · have hsum : ∑ j ∈ s, v.1 j • rowVector A j = 0 := by
        simpa [transpose_mulVec_eq_sum_rows, sum_rows_eq_sum_rows_support] using hv
      exact (linearIndepOn_finset_iff.mp hli) (fun j => v.1 j) hsum i hi
    · -- Outside `s`, support membership already forces the coordinate to be zero.
      exact (mem_supportedSubmodule s v.1).mp v.2 i hi
  · intro hv
    -- The converse direction is immediate from `v = 0`.
    have hv0 : v = 0 := by simpa [Submodule.mem_bot] using hv
    simp [hv0]

/-- The transpose map restricted to the coordinate subspace supported on `s`. -/
private noncomputable def supportedRowMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) :
    supportedSubmodule s →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toEuclideanLin Aᵀ).comp (supportedSubmodule s).subtype

/-- The cone generated by rows indexed by `s`, written using supported nonnegative coefficients. -/
private noncomputable def rowSubsetCone {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ v : supportedSubmodule s, (∀ i : Fin m, 0 ≤ v.1 i) ∧ y = supportedRowMap A s v}

/-- An independent-support row cone is closed as the image of a closed orthant under an injective
linear map. -/
private lemma isClosed_rowSubsetCone {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m))
    (hli : LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s) :
    IsClosed (rowSubsetCone A s) := by
  have hclosed : IsClosed {v : supportedSubmodule s | ∀ i : Fin m, 0 ≤ v.1 i} := by
    -- The coefficient orthant is the intersection of coordinatewise closed half-spaces.
    rw [show ({v : supportedSubmodule s | ∀ i : Fin m, 0 ≤ v.1 i} :
        Set (supportedSubmodule s)) =
        ⋂ i : Fin m, {v : supportedSubmodule s | (0 : ℝ) ≤ v.1 i} by
      ext v
      simp]
    exact isClosed_iInter (fun i : Fin m => isClosed_le continuous_const (by fun_prop))
  have himage :
      rowSubsetCone A s =
        supportedRowMap A s '' {v : supportedSubmodule s | ∀ i : Fin m, 0 ≤ v.1 i} := by
    -- Rewrite the cone as the image of the supported orthant.
    ext y
    simp [rowSubsetCone, supportedRowMap, eq_comm]
  rw [himage]
  exact
    (LinearMap.isClosedEmbedding_of_injective (supported_row_map_ker_eq_bot A s hli)).isClosedMap
      _ hclosed

/-- Any supported row cone is contained in the full transpose image cone. -/
private lemma rowSubsetCone_subset_transpose_image {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) :
    rowSubsetCone A s ⊆
      {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  rintro y ⟨v, hvnonneg, rfl⟩
  -- Forget the support constraint and view the same coefficients in the ambient space.
  refine ⟨v.1, hvnonneg, ?_⟩
  simpa [supportedRowMap, toEuclideanLin_eq_mulVec]

/-- A nonnegative coefficient vector belongs to the row cone generated by its nonzero support. -/
private lemma rowSubsetCone_of_nonnegative_support {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (v : EuclideanSpace ℝ (Fin m)) (hvnonneg : ∀ i : Fin m, 0 ≤ v i)
    (hy : y = Aᵀ.mulVec v) :
    y ∈ rowSubsetCone A (Finset.univ.filter fun i : Fin m => v i ≠ 0) := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter fun i : Fin m => v i ≠ 0
  have hvsupport : v ∈ supportedSubmodule s := by
    -- Coordinates outside the filtered support vanish by definition.
    rw [mem_supportedSubmodule]
    intro i hi
    by_cases hvi : v i = 0
    · exact hvi
    · exfalso
      exact hi (by simp [s, hvi])
  -- Package the ambient coefficient vector as a supported witness for the same row sum.
  refine ⟨⟨v, hvsupport⟩, hvnonneg, ?_⟩
  change y = Matrix.toEuclideanLin Aᵀ v
  ext i
  simpa [toEuclideanLin_eq_mulVec] using congrArg (fun z : Fin n → ℝ => z i) hy

/-- A supported row-cone witness with a zero coefficient at `i` already belongs to the erased
support cone. -/
private lemma rowSubsetCone_erase_of_zero_coordinate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {s : Finset (Fin m)} {y : EuclideanSpace ℝ (Fin n)}
    (v : supportedSubmodule s) (hvnonneg : ∀ i : Fin m, 0 ≤ v.1 i)
    (hy : y = supportedRowMap A s v) {i : Fin m} (_hi : i ∈ s) (hvi : v.1 i = 0) :
    y ∈ rowSubsetCone A (s.erase i) := by
  have hvsupport : v.1 ∈ supportedSubmodule (s.erase i) := by
    -- Off the erased support, either we are outside `s` already or at the new zero coordinate.
    rw [mem_supportedSubmodule]
    intro j hj
    by_cases hji : j = i
    · simpa [hji] using hvi
    · exact (mem_supportedSubmodule s v.1).mp v.2 j (by
        intro hjs
        exact hj (Finset.mem_erase.mpr ⟨hji, hjs⟩))
  -- Reuse the same ambient coefficient vector after shrinking the support.
  refine ⟨⟨v.1, hvsupport⟩, hvnonneg, ?_⟩
  simpa [supportedRowMap] using hy

/-- A dependent positive-support row representation can be shrunk to a strict subset. -/
private lemma rowSubsetCone_shrink_of_dependent {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {s : Finset (Fin m)} {y : EuclideanSpace ℝ (Fin n)}
    (v : supportedSubmodule s) (hvnonneg : ∀ i : Fin m, 0 ≤ v.1 i)
    (hvpos : ∀ i ∈ s, 0 < v.1 i) (hy : y = supportedRowMap A s v)
    (hdep : ¬ LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s) :
    ∃ i ∈ s, y ∈ rowSubsetCone A (s.erase i) := by
  classical
  -- Extract a nontrivial linear relation among the rows indexed by `s`.
  rw [not_linearIndepOn_finset_iff] at hdep
  rcases hdep with ⟨f, hfsum, i₀, hi₀s, hfi₀⟩
  -- Reorient the relation so that some coefficient is strictly positive.
  let g : Fin m → ℝ := if ∃ i ∈ s, 0 < f i then f else fun i => -f i
  have hgsum : ∑ i ∈ s, g i • rowVector A i = 0 := by
    by_cases hpos : ∃ i ∈ s, 0 < f i
    · simp [g, hpos, hfsum]
    · have : ∑ i ∈ s, (-f i) • rowVector A i = 0 := by
        simpa [neg_smul, Finset.sum_neg_distrib] using congrArg Neg.neg hfsum
      simpa [g, hpos] using this
  have hgpos : ∃ i ∈ s, 0 < g i := by
    by_cases hpos : ∃ i ∈ s, 0 < f i
    · simpa [g, hpos] using hpos
    · have hfi₀_neg : f i₀ < 0 := lt_of_le_of_ne (le_of_not_gt fun hgt =>
        hpos ⟨i₀, hi₀s, hgt⟩) hfi₀
      exact ⟨i₀, hi₀s, by simpa [g, hpos] using neg_pos.mpr hfi₀_neg⟩
  let p : Finset (Fin m) := s.filter fun i => 0 < g i
  have hp_nonempty : p.Nonempty := by
    rcases hgpos with ⟨i, his, hgi⟩
    exact ⟨i, by simp [p, his, hgi]⟩
  -- Choose a positive relation coefficient minimizing the ratio `v i / g i`.
  obtain ⟨iStar, hiStarP, hmin⟩ := p.exists_min_image (fun i => v.1 i / g i) hp_nonempty
  have hiStarS : iStar ∈ s := by
    exact (Finset.mem_filter.mp hiStarP).1
  have hgiStar : 0 < g iStar := by
    exact (Finset.mem_filter.mp hiStarP).2
  let lam : ℝ := v.1 iStar / g iStar
  let c : EuclideanSpace ℝ (Fin m) :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm fun i => if i ∈ s then g i else 0
  have hc_apply : ∀ i : Fin m, c i = if i ∈ s then g i else 0 := by
    intro i
    simp [c]
  have hcsum :
      ∑ i : Fin m, c i • rowVector A i = ∑ i ∈ s, g i • rowVector A i := by
    -- The correction vector agrees with `g` on `s` and vanishes outside `s`.
    calc
      ∑ i : Fin m, c i • rowVector A i = ∑ i ∈ s, c i • rowVector A i := by
        refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
        intro i _ hi
        have hci : c i = 0 := by
          rw [hc_apply i]
          simp [hi]
        simp [hci]
      _ = ∑ i ∈ s, g i • rowVector A i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hc_apply i]
        simp [hi]
  have hcmap : Matrix.toEuclideanLin Aᵀ c = 0 := by
    -- Convert the relation into a vanishing image under the transpose row map.
    simpa [transpose_mulVec_eq_sum_rows, hcsum] using hgsum
  let wFun : EuclideanSpace ℝ (Fin m) := v.1 - lam • c
  have hw_support : wFun ∈ supportedSubmodule s := by
    -- The correction is supported on `s`, so the adjusted vector stays supported on `s`.
    rw [mem_supportedSubmodule]
    intro i hi
    have hvi : v.1 i = 0 := (mem_supportedSubmodule s v.1).mp v.2 i hi
    have hci : c i = 0 := by
      rw [hc_apply i]
      simp [hi]
    simp [wFun, hvi, hci]
  let w : supportedSubmodule s := ⟨wFun, hw_support⟩
  have hlam_nonneg : 0 ≤ lam := by
    exact div_nonneg (le_of_lt (hvpos iStar hiStarS)) (le_of_lt hgiStar)
  have hw_nonneg : ∀ i : Fin m, 0 ≤ w.1 i := by
    intro i
    by_cases his : i ∈ s
    · by_cases hgi : 0 < g i
      · have hip : i ∈ p := by
          simp [p, his, hgi]
        have hratio : lam ≤ v.1 i / g i := by
          simpa [lam] using hmin i hip
        have hmul : lam * g i ≤ v.1 i := by
          calc
            lam * g i ≤ (v.1 i / g i) * g i :=
              mul_le_mul_of_nonneg_right hratio (le_of_lt hgi)
            _ = v.1 i := by
              rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (show g i ≠ 0 from ne_of_gt hgi),
                mul_one]
        have hci : c i = g i := by
          rw [hc_apply i]
          simp [his]
        -- Minimality of the ratio makes the positive coordinates stay nonnegative.
        simpa [w, wFun, hci] using sub_nonneg.mpr hmul
      · have hmul : lam * g i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam_nonneg
            (le_of_not_gt hgi)
        -- Nonpositive correction coefficients only increase the original nonnegative entry.
        have : 0 ≤ v.1 i - lam * g i := by
          linarith [hvnonneg i, hmul]
        have hci : c i = g i := by
          rw [hc_apply i]
          simp [his]
        simpa [w, wFun, hci] using this
    · have hvi : v.1 i = 0 := (mem_supportedSubmodule s v.1).mp v.2 i his
      have hci : c i = 0 := by
        rw [hc_apply i]
        simp [his]
      -- Outside `s`, both the original vector and the correction vanish.
      simpa [w, wFun, hvi, hci]
  have hwiStar : w.1 iStar = 0 := by
    -- The minimizing coordinate is forced to hit zero exactly.
    have hciStar : c iStar = g iStar := by
      rw [hc_apply iStar]
      simp [hiStarS]
    calc
      w.1 iStar = v.1 iStar - lam * g iStar := by simp [w, wFun, hciStar]
      _ = 0 := by
        simp [lam, div_eq_mul_inv, mul_assoc, ne_of_gt hgiStar]
  have hyw : y = supportedRowMap A s w := by
    -- The correction lies in the kernel because it is built from a dependence relation.
    calc
      y = supportedRowMap A s v := hy
      _ = Matrix.toEuclideanLin Aᵀ v.1 := rfl
      _ = Matrix.toEuclideanLin Aᵀ w.1 := by
            change Matrix.toEuclideanLin Aᵀ v.1 =
              Matrix.toEuclideanLin Aᵀ (v.1 - lam • c)
            rw [LinearMap.map_sub, LinearMap.map_smul, hcmap, smul_zero, sub_zero]
      _ = supportedRowMap A s w := rfl
  -- Erase the new zero coordinate to get a representation on a strict subset.
  exact ⟨iStar, hiStarS,
    rowSubsetCone_erase_of_zero_coordinate A w hw_nonneg hyw hiStarS hwiStar⟩

/-- Every point in the transpose image cone should admit a representation on an independent support.

This is the remaining combinatorial support-shrinking step. -/
private lemma exists_independent_rowSubsetCone {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ {y : EuclideanSpace ℝ (Fin n) |
      ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v}) :
    ∃ s : Finset (Fin m), LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s ∧
      y ∈ rowSubsetCone A s := by
  classical
  rcases hy with ⟨v₀, hv₀nonneg, hy₀⟩
  let s₀ : Finset (Fin m) := Finset.univ.filter fun i : Fin m => v₀ i ≠ 0
  have hs₀cone : y ∈ rowSubsetCone A s₀ := by
    -- Start from the obvious support of the original nonnegative witness.
    exact rowSubsetCone_of_nonnegative_support A v₀ hv₀nonneg hy₀
  let candidates : Finset (Finset (Fin m)) := s₀.powerset.filter fun s =>
    y ∈ rowSubsetCone A s
  have hs₀cand : s₀ ∈ candidates := by
    -- The initial support is one admissible candidate.
    simp [candidates, s₀, hs₀cone]
  obtain ⟨s, hsCand, hsMin⟩ := candidates.exists_min_image Finset.card ⟨s₀, hs₀cand⟩
  have hs_subset : s ⊆ s₀ := by
    exact Finset.mem_powerset.mp ((Finset.mem_filter.mp hsCand).1)
  have hy_s : y ∈ rowSubsetCone A s := by
    exact (Finset.mem_filter.mp hsCand).2
  rcases hy_s with ⟨v, hvnonneg, hyv⟩
  have hvpos : ∀ i ∈ s, 0 < v.1 i := by
    intro i hi
    -- A zero coefficient would allow us to erase `i` and contradict minimality.
    have hnonneg := hvnonneg i
    by_contra hnot
    have hzero : v.1 i = 0 := by linarith
    have hy_erase : y ∈ rowSubsetCone A (s.erase i) :=
      rowSubsetCone_erase_of_zero_coordinate A v hvnonneg hyv hi hzero
    have hs_erase_subset : s.erase i ⊆ s₀ := by
      exact (Finset.erase_subset i s).trans hs_subset
    have hs_erase_cand : s.erase i ∈ candidates := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs_erase_subset, hy_erase⟩
    exact (not_lt_of_ge (hsMin (s.erase i) hs_erase_cand)) (Finset.card_erase_lt_of_mem hi)
  by_cases hsli : LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s
  · -- The minimal support is already independent.
    exact ⟨s, hsli, ⟨v, hvnonneg, hyv⟩⟩
  · -- Route correction: dependent minimal support contradicts the shrink lemma.
    obtain ⟨i, hi, hy_erase⟩ := rowSubsetCone_shrink_of_dependent A v hvnonneg hvpos hyv hsli
    have hs_erase_subset : s.erase i ⊆ s₀ := by
      exact (Finset.erase_subset i s).trans hs_subset
    have hs_erase_cand : s.erase i ∈ candidates := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs_erase_subset, hy_erase⟩
    exact False.elim <|
      (not_lt_of_ge (hsMin (s.erase i) hs_erase_cand)) (Finset.card_erase_lt_of_mem hi)

/-- The transpose image of the coordinatewise nonnegative orthant is closed.

TODO: prove this finite-dimensional polyhedral cone is closed, for example by decomposing it into
a finite union of simplicial cones generated by linearly independent subsets of the rows of `A`. -/
private lemma isClosed_transpose_nonnegative_image
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    IsClosed {y : EuclideanSpace ℝ (Fin n) |
      ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  classical
  let supports : Finset (Finset (Fin m)) :=
    Finset.univ.powerset.filter fun s =>
      LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s
  have hEq :
      {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} =
      ⋃ s ∈ supports, rowSubsetCone A s := by
    ext y
    constructor
    · intro hy
      -- Use the support-shrinking lemma to land in one closed independent-support piece.
      obtain ⟨s, hsli, hys⟩ := exists_independent_rowSubsetCone A hy
      exact Set.mem_iUnion₂.2 ⟨s, by simp [supports, hsli], hys⟩
    · intro hy
      -- Every independent-support piece is visibly contained in the full transpose image cone.
      rw [Set.mem_iUnion₂] at hy
      rcases hy with ⟨s, _, hys⟩
      exact rowSubsetCone_subset_transpose_image A s hys
  rw [hEq]
  exact isClosed_biUnion_finset fun s hs =>
    isClosed_rowSubsetCone A s ((by simpa [supports] using hs) : _)

/-
Let A ∈ ℝ^{m \times n}, and let V = {x ∈ ℝ^n | Ax succeq 0}, where Ax succeq 0 means that every
component of Ax ∈ ℝ^m is nonnegative. For a cone K ⊆ ℝ^n, define its dual cone by K* = {y ∈ ℝ^n | yᵀ
x ≥ 0 ext{for all} x ∈ K}. Show that V* = {Aᵀ v | v succeq 0}, where v succeq 0 means that every
component of v ∈ ℝ^m is nonnegative.
-/
theorem dualCone_of_nonnegative_preimage_eq_range_transpose_nonnegative
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    dualCone {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, 0 ≤ (A.mulVec x) i} =
      {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  -- Reduce the theorem to the closedness of the explicit transpose image cone.
  rw [dualCone_eq_closure_transpose_nonnegative_image]
  exact (isClosed_transpose_nonnegative_image A).closure_eq
end «problem-127»
