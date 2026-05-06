import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-126»
/-
A linear program is an optimization problem of the form (min {c^T x mid Gx le h, Ex = d});
equivalently, it has a linear objective function and linear equality and inequality constraints.
-/
structure LinearProgram (m n p : ℕ) where
  c : Fin n → ℝ
  G : Matrix (Fin m) (Fin n) ℝ
  h : Fin m → ℝ
  E : Matrix (Fin p) (Fin n) ℝ
  d : Fin p → ℝ

def LinearProgram.objective {m n p : ℕ} (P : LinearProgram m n p) (x : Fin n → ℝ) : ℝ :=
  dotProduct P.c x

def LinearProgram.IsFeasible {m n p : ℕ} (P : LinearProgram m n p) (x : Fin n → ℝ) : Prop :=
  (∀ i : Fin m, (P.G.mulVec x) i ≤ P.h i) ∧ (P.E.mulVec x = P.d)

def ComponentwiseGE {m : ℕ} (u v : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, v i ≤ u i

/-
For primal inequality constraints (Ax ge b) with dual variable (y ge 0), complementary slackness
means that (y_i (Ax - b)_i = 0) for every (i); equivalently, (y^T(Ax - b) = 0).
-/
def ComplementarySlackness {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (b y : Fin m → ℝ) : Prop :=
  (∀ i : Fin m, 0 ≤ y i) ∧ ∀ i : Fin m, y i * ((A.mulVec x) i - b i) = 0

/-
For the dual of (min {c^T x mid Ax ge b}), a vector (y in mathbf{R}^m) is dual feasible if (y ge
0) and (A^T y = c).
-/
def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  ComponentwiseGE (A.mulVec x) b

/-
Consider the linear program, with unknown cost vector (c in mathbf{R}^n), [ begin{} text{minimize}
& c^T x text{subject to} & Ax ge b, end{} ] where the decision variable is (x in mathbf{R}^n), and
the inequalities are understood componentwise.
-/
structure LinearProgramWithUnknownCost (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def LinearProgramWithUnknownCost.isFeasible {m n : ℕ} (P : LinearProgramWithUnknownCost m n)
    (x : Fin n → ℝ) : Prop :=
  PrimalFeasible P.A P.b x

def LinearProgramWithUnknownCost.objective {m n : ℕ} (_P : LinearProgramWithUnknownCost m n)
    (c x : Fin n → ℝ) : ℝ :=
  dotProduct c x

/-- The dual cone of a set of Euclidean vectors, written using the real inner product. -/
private def dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
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
    -- The positive orthant is an intersection of coordinatewise closed half-spaces.
    have hclosed : IsClosed {v : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, 0 ≤ v i} := by
      classical
      rw [show ({v : EuclideanSpace ℝ (Fin m) | ∀ i : Fin m, 0 ≤ v i} :
          Set (EuclideanSpace ℝ (Fin m))) =
          ⋂ i : Fin m, {v : EuclideanSpace ℝ (Fin m) | (0 : ℝ) ≤ v i} by
        ext v
        simp]
      exact isClosed_iInter (fun i : Fin m => isClosed_le continuous_const (by fun_prop))
    exact hclosed

/-- Membership in `positiveOrthant` is coordinatewise nonnegativity. -/
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
    -- Test the dual inequality on standard basis vectors to recover coordinates of `y`.
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
    -- Expand the inner product as a finite sum of nonnegative coordinatewise products.
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hy i) (hx i)

/-- `Matrix.toEuclideanLin` agrees with `mulVec` after reading Euclidean vectors in coordinates. -/
private lemma toEuclideanLin_eq_mulVec {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin A x = A.mulVec x := by
  -- Compare both sides coordinatewise.
  ext i
  rfl

/-- The adjoint of `Aᵀ` as a Euclidean linear map is the map associated to `A`. -/
private lemma adjoint_toEuclideanLin_transpose {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ((Matrix.toEuclideanLin Aᵀ).toContinuousLinearMap).adjoint =
      (Matrix.toEuclideanLin A).toContinuousLinearMap := by
  -- Convert the continuous statement back to the linear-map adjoint theorem.
  change (LinearMap.adjoint (Matrix.toEuclideanLin Aᵀ)).toContinuousLinearMap =
    (Matrix.toEuclideanLin A).toContinuousLinearMap
  simpa using congrArg LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := Aᵀ)).symm

/-- The abstract `ProperCone.map` image is the closure of the explicit transpose-image cone. -/
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

/-- Finite-dimensional Farkas lemma, first in closure form. -/
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
          -- Route correction: handle the closure issue via the positive-orthant image first.
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

/-- The `i`-th row of `A`, regarded as a Euclidean vector. -/
private noncomputable def rowVector {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (A i)

/-- The subspace of Euclidean vectors supported on a chosen finite set of coordinates. -/
private noncomputable abbrev supportedSubmodule {m : ℕ} (s : Finset (Fin m)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  ⨅ i : {i // i ∉ s}, LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (i := i.1))

/-- Membership in `supportedSubmodule s` means vanishing outside `s`. -/
@[simp] private lemma mem_supportedSubmodule {m : ℕ}
    (s : Finset (Fin m)) (v : EuclideanSpace ℝ (Fin m)) :
    v ∈ supportedSubmodule s ↔ ∀ i ∉ s, v i = 0 := by
  -- Unfold the infimum of coordinate kernels into coordinatewise vanishing.
  simp [supportedSubmodule]

/-- Expand `Aᵀ.mulVec v` as a finite sum of row vectors. -/
private lemma transpose_mulVec_eq_sum_rows {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin m)) :
    Matrix.toEuclideanLin Aᵀ v = ∑ i : Fin m, v i • rowVector A i := by
  -- Compare coordinates and rewrite the transpose product as a row expansion.
  ext j
  simp [rowVector, Matrix.mulVec, dotProduct, mul_comm]

/-- For a supported vector, only the chosen support contributes to the row expansion. -/
private lemma sum_rows_eq_sum_rows_support {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) (v : supportedSubmodule s) :
    ∑ i : Fin m, v.1 i • rowVector A i = ∑ i ∈ s, v.1 i • rowVector A i := by
  -- Terms outside `s` vanish because the vector is supported on `s`.
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
    -- On the support, linear independence forces every coefficient to vanish.
    rw [Submodule.mem_bot]
    ext i
    by_cases hi : i ∈ s
    · have hsum : ∑ j ∈ s, v.1 j • rowVector A j = 0 := by
        simpa [transpose_mulVec_eq_sum_rows, sum_rows_eq_sum_rows_support] using hv
      exact (linearIndepOn_finset_iff.mp hli) (fun j => v.1 j) hsum i hi
    · exact (mem_supportedSubmodule s v.1).mp v.2 i hi
  · intro hv
    -- The converse direction is immediate from `v = 0`.
    have hv0 : v = 0 := by simpa [Submodule.mem_bot] using hv
    simp [hv0]

/-- The transpose map restricted to vectors supported on `s`. -/
private noncomputable def supportedRowMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) :
    supportedSubmodule s →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toEuclideanLin Aᵀ).comp (supportedSubmodule s).subtype

/-- The cone generated by the rows of `A` indexed by `s`, via supported nonnegative coefficients. -/
private noncomputable def rowSubsetCone {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ v : supportedSubmodule s, (∀ i : Fin m, 0 ≤ v.1 i) ∧ y = supportedRowMap A s v}

/-- An independent-support row cone is closed as the image of a closed orthant. -/
private lemma isClosed_rowSubsetCone {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m))
    (hli : LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s) :
    IsClosed (rowSubsetCone A s) := by
  have hclosed : IsClosed {v : supportedSubmodule s | ∀ i : Fin m, 0 ≤ v.1 i} := by
    -- The supported orthant is an intersection of coordinatewise closed half-spaces.
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

/-- Any supported row-cone witness is also a witness for the full transpose-image cone. -/
private lemma rowSubsetCone_subset_transpose_image {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin m)) :
    rowSubsetCone A s ⊆
      {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  rintro y ⟨v, hvnonneg, rfl⟩
  -- Forget the support restriction and reuse the same coefficient vector in the ambient space.
  refine ⟨v.1, hvnonneg, ?_⟩
  simp [supportedRowMap]

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
  refine ⟨⟨v, hvsupport⟩, hvnonneg, ?_⟩
  change y = Matrix.toEuclideanLin Aᵀ v
  ext i
  simpa [toEuclideanLin_eq_mulVec] using congrArg (fun z : Fin n → ℝ => z i) hy

/-- If a supported row witness has a zero coefficient, that coordinate can be erased. -/
private lemma rowSubsetCone_erase_of_zero_coordinate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {s : Finset (Fin m)} {y : EuclideanSpace ℝ (Fin n)}
    (v : supportedSubmodule s) (hvnonneg : ∀ i : Fin m, 0 ≤ v.1 i)
    (hy : y = supportedRowMap A s v) {i : Fin m} (_hi : i ∈ s) (hvi : v.1 i = 0) :
    y ∈ rowSubsetCone A (s.erase i) := by
  have hvsupport : v.1 ∈ supportedSubmodule (s.erase i) := by
    -- Off the erased support, either we were already outside `s` or we are at the new zero.
    rw [mem_supportedSubmodule]
    intro j hj
    by_cases hji : j = i
    · simpa [hji] using hvi
    · exact (mem_supportedSubmodule s v.1).mp v.2 j (by
        intro hjs
        exact hj (Finset.mem_erase.mpr ⟨hji, hjs⟩))
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
  -- Reorient the relation so that some coefficient becomes strictly positive.
  let g : Fin m → ℝ := if ∃ i ∈ s, 0 < f i then f else fun i => -f i
  have hgsum : ∑ i ∈ s, g i • rowVector A i = 0 := by
    by_cases hpos : ∃ i ∈ s, 0 < f i
    · simp [g, hpos, hfsum]
    · have : ∑ i ∈ s, (-f i) • rowVector A i = 0 := by
        simpa [neg_smul, Finset.sum_neg_distrib] using congrArg Neg.neg hfsum
      simpa [g, hpos] using this
  have hgpos : ∃ i ∈ s, 0 < g i := by
    by_cases hpos : ∃ i ∈ s, 0 < f i
    · simp [g, hpos]
    · have hfi₀_neg : f i₀ < 0 := lt_of_le_of_ne (le_of_not_gt fun hgt =>
        hpos ⟨i₀, hi₀s, hgt⟩) hfi₀
      exact ⟨i₀, hi₀s, by simpa [g, hpos] using neg_pos.mpr hfi₀_neg⟩
  let p : Finset (Fin m) := s.filter fun i => 0 < g i
  have hp_nonempty : p.Nonempty := by
    rcases hgpos with ⟨i, his, hgi⟩
    exact ⟨i, by simp [p, his, hgi]⟩
  -- Choose a positive relation coefficient minimizing the ratio `v i / g i`.
  obtain ⟨iStar, hiStarP, hmin⟩ := p.exists_min_image (fun i => v.1 i / g i) hp_nonempty
  have hiStarS : iStar ∈ s := (Finset.mem_filter.mp hiStarP).1
  have hgiStar : 0 < g iStar := (Finset.mem_filter.mp hiStarP).2
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
    -- Convert the dependence relation into a vanishing transpose image.
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
      · have hip : i ∈ p := by simp [p, his, hgi]
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
        -- Minimality of the ratio keeps every positive-support coordinate nonnegative.
        simpa [w, wFun, hci] using sub_nonneg.mpr hmul
      · have hmul : lam * g i ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hlam_nonneg (le_of_not_gt hgi)
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
      -- Outside the support, both the original vector and the correction vanish.
      simp [w, wFun, hvi, hci]
  have hwiStar : w.1 iStar = 0 := by
    -- The minimizing coordinate hits zero exactly.
    have hciStar : c iStar = g iStar := by
      rw [hc_apply iStar]
      simp [hiStarS]
    calc
      w.1 iStar = v.1 iStar - lam * g iStar := by simp [w, wFun, hciStar]
      _ = 0 := by
        simp [lam, div_eq_mul_inv, ne_of_gt hgiStar]
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
  exact ⟨iStar, hiStarS,
    rowSubsetCone_erase_of_zero_coordinate A w hw_nonneg hyw hiStarS hwiStar⟩

/-- Every point in the transpose-image cone admits a representation on an independent support. -/
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
  have hs_subset : s ⊆ s₀ := (Finset.mem_powerset.mp ((Finset.mem_filter.mp hsCand).1))
  have hy_s : y ∈ rowSubsetCone A s := (Finset.mem_filter.mp hsCand).2
  rcases hy_s with ⟨v, hvnonneg, hyv⟩
  have hvpos : ∀ i ∈ s, 0 < v.1 i := by
    intro i hi
    -- A zero coefficient would let us erase `i` and contradict minimality.
    have hnonneg := hvnonneg i
    by_contra hnot
    have hzero : v.1 i = 0 := by linarith
    have hy_erase : y ∈ rowSubsetCone A (s.erase i) :=
      rowSubsetCone_erase_of_zero_coordinate A v hvnonneg hyv hi hzero
    have hs_erase_subset : s.erase i ⊆ s₀ := (Finset.erase_subset i s).trans hs_subset
    have hs_erase_cand : s.erase i ∈ candidates := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs_erase_subset, hy_erase⟩
    exact (not_lt_of_ge (hsMin (s.erase i) hs_erase_cand)) (Finset.card_erase_lt_of_mem hi)
  by_cases hsli : LinearIndepOn ℝ (fun i : Fin m => rowVector A i) s
  · exact ⟨s, hsli, ⟨v, hvnonneg, hyv⟩⟩
  · -- Route correction: a dependent minimal support contradicts the shrink lemma.
    obtain ⟨i, hi, hy_erase⟩ := rowSubsetCone_shrink_of_dependent A v hvnonneg hvpos hyv hsli
    have hs_erase_subset : s.erase i ⊆ s₀ := (Finset.erase_subset i s).trans hs_subset
    have hs_erase_cand : s.erase i ∈ candidates := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs_erase_subset, hy_erase⟩
    exact False.elim <|
      (not_lt_of_ge (hsMin (s.erase i) hs_erase_cand)) (Finset.card_erase_lt_of_mem hi)

/-- The transpose-image cone of the coordinatewise nonnegative orthant is closed. -/
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
      -- Use support shrinking to land in a closed independent-support piece.
      obtain ⟨s, hsli, hys⟩ := exists_independent_rowSubsetCone A hy
      exact Set.mem_iUnion₂.2 ⟨s, by simp [supports, hsli], hys⟩
    · intro hy
      -- Every independent-support piece lies in the full transpose-image cone.
      rw [Set.mem_iUnion₂] at hy
      rcases hy with ⟨s, _, hys⟩
      exact rowSubsetCone_subset_transpose_image A s hys
  rw [hEq]
  exact isClosed_biUnion_finset fun s hs =>
    isClosed_rowSubsetCone A s ((by simpa [supports] using hs) : _)

/-- Finite-dimensional Farkas lemma for the coordinatewise nonnegative cone. -/
private theorem dualCone_of_nonnegative_preimage_eq_range_transpose_nonnegative
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    dualCone {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, 0 ≤ (A.mulVec x) i} =
      {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  -- Reduce exact image membership to the closedness of the explicit polyhedral cone.
  rw [dualCone_eq_closure_transpose_nonnegative_image]
  exact (isClosed_transpose_nonnegative_image A).closure_eq

/-- The active-row matrix keeps only the rows of `A` that are tight at `x0`. -/
private def activeMatrix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 : Fin n → ℝ) :
    Matrix {i : Fin m // Matrix.mulVec A x0 i = bj i} (Fin n) ℝ :=
  fun i k => A i.1 k

/-- Multiplying the active-row matrix by a direction just restricts `A.mulVec` to active indices. -/
@[simp] private lemma mulVec_activeMatrix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 d : Fin n → ℝ)
    (i : {i : Fin m // Matrix.mulVec A x0 i = bj i}) :
    Matrix.mulVec (activeMatrix A bj x0) d i = Matrix.mulVec A d i.1 := by
  simp [activeMatrix, Matrix.mulVec, dotProduct]

/-- Extend multipliers on the active set by zero outside the active constraints. -/
private def extendByZero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 : Fin n → ℝ)
    (μ : {i : Fin m // Matrix.mulVec A x0 i = bj i} → ℝ) :
    Fin m → ℝ :=
  fun i => if hi : Matrix.mulVec A x0 i = bj i then μ ⟨i, hi⟩ else 0

/-- The zero extension is nonnegative when the active multipliers are nonnegative. -/
private lemma extendByZero_nonneg {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 : Fin n → ℝ)
    {μ : {i : Fin m // Matrix.mulVec A x0 i = bj i} → ℝ}
    (hμ : ∀ i, 0 ≤ μ i) :
    ∀ i : Fin m, 0 ≤ extendByZero A bj x0 μ i := by
  intro i
  -- On active indices we read off `μ`; elsewhere the extension is zero.
  by_cases hi : Matrix.mulVec A x0 i = bj i
  · simp [extendByZero, hi, hμ ⟨i, hi⟩]
  · simp [extendByZero, hi]

/-- On active indices, the zero extension agrees with the original multiplier. -/
private lemma extendByZero_eq_active {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 : Fin n → ℝ)
    (μ : {i : Fin m // Matrix.mulVec A x0 i = bj i} → ℝ)
    (i : {i : Fin m // Matrix.mulVec A x0 i = bj i}) :
    extendByZero A bj x0 μ i.1 = μ i := by
  simp [extendByZero, i.2]

/-- Outside the active set, the zero extension vanishes. -/
private lemma extendByZero_eq_zero_of_inactive {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 : Fin n → ℝ)
    (μ : {i : Fin m // Matrix.mulVec A x0 i = bj i} → ℝ)
    {i : Fin m} (hi : Matrix.mulVec A x0 i ≠ bj i) :
    extendByZero A bj x0 μ i = 0 := by
  simp [extendByZero, hi]

/-- Zero extension preserves the transpose-image vector produced by the active-row matrix. -/
private lemma mulVec_transpose_extendByZero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 : Fin n → ℝ)
    (μ : {i : Fin m // Matrix.mulVec A x0 i = bj i} → ℝ) :
    Matrix.mulVec Aᵀ (extendByZero A bj x0 μ) =
      Matrix.mulVec (activeMatrix A bj x0)ᵀ μ := by
  let s : Finset (Fin m) := Finset.univ.filter fun i : Fin m => Matrix.mulVec A x0 i = bj i
  ext k
  -- Expand both sides coordinatewise and filter the ambient sum to active indices.
  calc
    (Matrix.mulVec Aᵀ (extendByZero A bj x0 μ)) k
        = ∑ i : Fin m, A i k * extendByZero A bj x0 μ i := by
            simp [Matrix.mulVec, dotProduct]
    _ = Finset.sum s (fun i => A i k * extendByZero A bj x0 μ i) := by
            rw [show s = Finset.univ.filter fun i : Fin m => Matrix.mulVec A x0 i = bj i by
              rfl]
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro i _
            by_cases hi : Matrix.mulVec A x0 i = bj i
            · simp [extendByZero, hi]
            · simp [extendByZero, hi]
    _ = ∑ i : {i : Fin m // Matrix.mulVec A x0 i = bj i}, A i.1 k * μ i := by
          symm
          simpa [extendByZero_eq_active] using
            (Finset.sum_subtype_eq_sum_filter
              (s := Finset.univ)
              (p := fun i : Fin m => Matrix.mulVec A x0 i = bj i)
              (f := fun i : Fin m => A i k * extendByZero A bj x0 μ i))
    _ = (Matrix.mulVec (activeMatrix A bj x0)ᵀ μ) k := by
          simp [Matrix.mulVec, activeMatrix, dotProduct]

/-- If a multiplier is supported on active constraints, replacing `bj` by `A x0` preserves the dot
product. -/
private lemma dotProduct_eq_dotProduct_active_mulVec {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 : Fin n → ℝ)
    (y : Fin m → ℝ)
    (hy : ∀ i : Fin m, Matrix.mulVec A x0 i ≠ bj i → y i = 0) :
    dotProduct bj y = dotProduct (Matrix.mulVec A x0) y := by
  -- On inactive indices the coefficient vanishes, while active indices satisfy `bj i = (A x0) i`.
  unfold dotProduct
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hi : Matrix.mulVec A x0 i = bj i
  · simp [hi]
  · simp [hy i hi]

/-- A positive step size exists along any direction that preserves the active inequalities. -/
private lemma exists_positive_feasibleStep_of_active_nonneg
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 d : Fin n → ℝ)
    (hfeas0 : ∀ i : Fin m, bj i ≤ Matrix.mulVec A x0 i)
    (hdactive :
      ∀ i : {i : Fin m // Matrix.mulVec A x0 i = bj i},
        0 ≤ Matrix.mulVec (activeMatrix A bj x0) d i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i : Fin m, bj i ≤ Matrix.mulVec A (x0 + t • d) i := by
  classical
  let bound : Fin m → ℝ := fun i =>
    if hactive : Matrix.mulVec A x0 i = bj i then
      1
    else if hnonnegd : 0 ≤ Matrix.mulVec A d i then
      1
    else
      (Matrix.mulVec A x0 i - bj i) / (-(Matrix.mulVec A d i))
  let bounds : Finset ℝ := Finset.univ.image bound
  let t : ℝ := if h : bounds.Nonempty then bounds.min' h else 1
  have hbound_pos : ∀ i : Fin m, 0 < bound i := by
    intro i
    -- Every local bound is positive: either it is `1`, or it is a positive slack ratio.
    by_cases hactive : Matrix.mulVec A x0 i = bj i
    · simp [bound, hactive]
    · by_cases hnonnegd : 0 ≤ Matrix.mulVec A d i
      · simp [bound, hactive, hnonnegd]
      · have hstrict : bj i < Matrix.mulVec A x0 i :=
          lt_of_le_of_ne (hfeas0 i) (by
            intro hEq
            exact hactive hEq.symm)
        have hslack : 0 < Matrix.mulVec A x0 i - bj i := by
          linarith
        have hdenom : 0 < -(Matrix.mulVec A d i) := by
          linarith [lt_of_not_ge hnonnegd]
        simp [bound, hactive, hnonnegd, div_pos hslack hdenom]
  have ht_pos : 0 < t := by
    -- The chosen step is the minimum of finitely many positive bounds.
    by_cases hnonempty : bounds.Nonempty
    · have hmem : bounds.min' hnonempty ∈ bounds := Finset.min'_mem bounds hnonempty
      rcases Finset.mem_image.mp hmem with ⟨i, -, hi⟩
      simpa [t, hnonempty, hi] using hbound_pos i
    · simp [t, hnonempty]
  have ht_le_bound : ∀ i : Fin m, t ≤ bound i := by
    intro i
    by_cases hnonempty : bounds.Nonempty
    · have hmem : bound i ∈ bounds := by
        refine Finset.mem_image.mpr ?_
        exact ⟨i, Finset.mem_univ i, rfl⟩
      simpa [t, hnonempty] using Finset.min'_le bounds (bound i) hmem
    · have hmem : bound i ∈ bounds := by
        refine Finset.mem_image.mpr ?_
        exact ⟨i, Finset.mem_univ i, rfl⟩
      exact False.elim <| hnonempty ⟨bound i, hmem⟩
  refine ⟨t, ht_pos, ?_⟩
  intro i
  have hmul :
      Matrix.mulVec A (x0 + t • d) i = Matrix.mulVec A x0 i + t * Matrix.mulVec A d i := by
    -- Expand the matrix-vector product along the affine step.
    simp [Matrix.mulVec_add, Matrix.mulVec_smul, smul_eq_mul, mul_comm]
  by_cases hactive : Matrix.mulVec A x0 i = bj i
  · have hdir : 0 ≤ Matrix.mulVec A d i := by
      simpa [hactive] using hdactive ⟨i, hactive⟩
    -- Active inequalities stay feasible because their directional derivative is nonnegative.
    nlinarith [hmul, hdir, ht_pos, hactive]
  · by_cases hnonnegd : 0 ≤ Matrix.mulVec A d i
    · -- Inactive constraints with nonnegative directional derivative are automatically preserved.
      nlinarith [hmul, hfeas0 i, hnonnegd, le_of_lt ht_pos]
    · have hstrict : bj i < Matrix.mulVec A x0 i :=
          lt_of_le_of_ne (hfeas0 i) (by
            intro hEq
            exact hactive hEq.symm)
      have hslack : 0 < Matrix.mulVec A x0 i - bj i := by
        linarith
      have hdenom : 0 < -(Matrix.mulVec A d i) := by
        linarith [lt_of_not_ge hnonnegd]
      have hratio : t ≤ (Matrix.mulVec A x0 i - bj i) / (-(Matrix.mulVec A d i)) := by
        simpa [bound, hactive, hnonnegd] using ht_le_bound i
      have hstep :
          t * (-(Matrix.mulVec A d i)) ≤ Matrix.mulVec A x0 i - bj i := by
        exact (le_div_iff₀ hdenom).mp hratio
      -- The step-size bound is chosen so that strictly inactive constraints stay feasible.
      nlinarith [hmul, hstep]

/-- A dual certificate proves fixed-index primal optimality by weak duality. -/
private lemma dualCertificate_implies_fixedIndexOptimality
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 c : Fin n → ℝ)
    (_hfeas0 : ∀ i : Fin m, bj i ≤ Matrix.mulVec A x0 i)
    (hcert : ∃ y : Fin m → ℝ,
      (∀ i : Fin m, 0 ≤ y i) ∧
      Matrix.mulVec Aᵀ y = c ∧
      dotProduct bj y = dotProduct c x0) :
    ∀ z : Fin n → ℝ, (∀ i : Fin m, bj i ≤ Matrix.mulVec A z i) → dotProduct c x0 ≤ dotProduct c z := by
  rcases hcert with ⟨y, hy_nonneg, hyA, hyEq⟩
  intro z hz
  have hweak : dotProduct bj y ≤ dotProduct (Matrix.mulVec A z) y := by
    -- Compare the primal right-hand side against `A z` coordinatewise using `y ≥ 0`.
    unfold dotProduct
    refine Finset.sum_le_sum ?_
    intro i _
    exact mul_le_mul_of_nonneg_right (hz i) (hy_nonneg i)
  calc
    dotProduct c x0 = dotProduct bj y := hyEq.symm
    _ ≤ dotProduct (Matrix.mulVec A z) y := hweak
    _ = dotProduct c z := by
      -- Rewrite the middle term via `Aᵀ y = c`.
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose A y, hyA]

/-- Primal optimality forces the objective to be nonnegative on directions preserving all active
inequalities. -/
private lemma optimality_nonneg_on_activeDirections
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 c : Fin n → ℝ)
    (hfeas0 : ∀ i : Fin m, bj i ≤ Matrix.mulVec A x0 i)
    (hopt :
      ∀ z : Fin n → ℝ, (∀ i : Fin m, bj i ≤ Matrix.mulVec A z i) →
        dotProduct c x0 ≤ dotProduct c z) :
    ∀ d : Fin n → ℝ,
      (∀ i : {i : Fin m // Matrix.mulVec A x0 i = bj i},
        0 ≤ Matrix.mulVec (activeMatrix A bj x0) d i) →
      0 ≤ dotProduct c d := by
  intro d hd
  obtain ⟨t, ht_pos, hfeas_t⟩ :=
    exists_positive_feasibleStep_of_active_nonneg A bj x0 d hfeas0 hd
  have hopt_t := hopt (x0 + t • d) hfeas_t
  have hexpand :
      dotProduct c (x0 + t • d) = dotProduct c x0 + t * dotProduct c d := by
    -- Expand the objective along the affine step.
    rw [dotProduct_add, dotProduct_smul]
    simp [smul_eq_mul]
  have hscaled : 0 ≤ t * dotProduct c d := by
    nlinarith [hopt_t, hexpand]
  -- Divide out the positive step size.
  nlinarith [hscaled, ht_pos]

/-- Fixed-index primal optimality yields a dual certificate supported on the active constraints. -/
private lemma exists_dualCertificate_of_fixedIndexOptimality
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bj : Fin m → ℝ) (x0 c : Fin n → ℝ)
    (hfeas0 : ∀ i : Fin m, bj i ≤ Matrix.mulVec A x0 i)
    (hopt :
      ∀ z : Fin n → ℝ, (∀ i : Fin m, bj i ≤ Matrix.mulVec A z i) →
        dotProduct c x0 ≤ dotProduct c z) :
    ∃ y : Fin m → ℝ,
      (∀ i : Fin m, 0 ≤ y i) ∧
      Matrix.mulVec Aᵀ y = c ∧
      dotProduct bj y = dotProduct c x0 := by
  let I : Type := {i : Fin m // Matrix.mulVec A x0 i = bj i}
  let eI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let Aact : Matrix (Fin (Fintype.card I)) (Fin n) ℝ :=
    fun i k => A (eI.symm i).1 k
  let cE : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm c
  have hdualCone :
      cE ∈ dualCone {d : EuclideanSpace ℝ (Fin n) |
        ∀ i : Fin (Fintype.card I), 0 ≤ Matrix.mulVec Aact d i} := by
    rw [dualCone]
    intro d hd
    -- Convert active-set optimality into the dual-cone condition.
    have hd' :
        ∀ i : I, 0 ≤ Matrix.mulVec (activeMatrix A bj x0) d i := by
      intro i
      simpa [Aact, activeMatrix, eI, Matrix.mulVec, dotProduct] using hd (eI i)
    simpa [cE, PiLp.inner_apply, RCLike.inner_apply, dotProduct, mul_comm] using
      optimality_nonneg_on_activeDirections A bj x0 c hfeas0 hopt d hd'
  have himage :
      cE ∈ {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin (Fintype.card I)),
          (∀ i : Fin (Fintype.card I), 0 ≤ v i) ∧
          y = Matrix.mulVec Aactᵀ v} := by
    let hEq := dualCone_of_nonnegative_preimage_eq_range_transpose_nonnegative Aact
    simpa [hEq] using hdualCone
  rcases himage with ⟨μFin, hμ_nonneg, hμA⟩
  let μ : I → ℝ := fun i => μFin (eI i)
  have hμA_subtype : Matrix.mulVec (activeMatrix A bj x0)ᵀ μ = c := by
    ext k
    have hcoord : c k = ∑ j : Fin (Fintype.card I), A (eI.symm j).1 k * μFin j := by
      simpa [Aact, cE, Matrix.mulVec, dotProduct] using congrArg (fun v : Fin n → ℝ => v k) hμA
    calc
      (Matrix.mulVec (activeMatrix A bj x0)ᵀ μ) k = ∑ i : I, A i.1 k * μ i := by
        rfl
      _ = ∑ j : Fin (Fintype.card I), A (eI.symm j).1 k * μFin j := by
        simpa [μ] using
          (Equiv.sum_comp eI (fun j : Fin (Fintype.card I) => A (eI.symm j).1 k * μFin j))
      _ = c k := hcoord.symm
  let y : Fin m → ℝ := extendByZero A bj x0 μ
  have hμ_nonneg_subtype : ∀ i : I, 0 ≤ μ i := by
    intro i
    simpa [μ] using hμ_nonneg (eI i)
  have hyA : Matrix.mulVec Aᵀ y = c := by
    -- Extending by zero preserves the transpose-image equality.
    calc
      Matrix.mulVec Aᵀ y = Matrix.mulVec (activeMatrix A bj x0)ᵀ μ := by
        simpa [y] using mulVec_transpose_extendByZero A bj x0 μ
      _ = c := hμA_subtype
  refine ⟨y, extendByZero_nonneg A bj x0 hμ_nonneg_subtype, hyA, ?_⟩
  · -- Because the support is active, the primal and dual objectives agree automatically.
    have hy_support :
        ∀ i : Fin m, Matrix.mulVec A x0 i ≠ bj i → y i = 0 := by
      intro i hi
      simpa [y] using extendByZero_eq_zero_of_inactive A bj x0 μ hi
    calc
      dotProduct bj y = dotProduct (Matrix.mulVec A x0) y :=
        dotProduct_eq_dotProduct_active_mulVec A bj x0 y hy_support
      _ = dotProduct y (Matrix.mulVec A x0) := by rw [dotProduct_comm]
      _ = dotProduct (Matrix.mulVec Aᵀ y) x0 := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose A y]
      _ = dotProduct c x0 := by
        rw [hyA]

/-- Zero duality gap implies complementary slackness. -/
private lemma complementarySlackness_of_zero_duality_gap
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x c : Fin n → ℝ) (y : Fin m → ℝ)
    (hfeas : PrimalFeasible A b x)
    (hy_nonneg : ∀ i : Fin m, 0 ≤ y i)
    (hyA : A.transpose.mulVec y = c)
    (hgap : dotProduct b y = dotProduct c x) :
    ComplementarySlackness A x b y := by
  refine ⟨hy_nonneg, ?_⟩
  have hsum_nonneg :
      ∀ i : Fin m, 0 ≤ y i * ((A.mulVec x) i - b i) := by
    intro i
    exact mul_nonneg (hy_nonneg i) (sub_nonneg.mpr (hfeas i))
  have hsum_eq_zero :
      ∑ i : Fin m, y i * ((A.mulVec x) i - b i) = 0 := by
    have hmain : dotProduct y (A.mulVec x) = dotProduct y b := by
      calc
        dotProduct y (A.mulVec x) = dotProduct (A.transpose.mulVec y) x := by
          rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose A y]
        _ = dotProduct c x := by rw [hyA]
        _ = dotProduct b y := hgap.symm
        _ = dotProduct y b := by rw [dotProduct_comm]
    -- Package the duality-gap equality directly as a zero dot product on the slack vector.
    have hz : dotProduct y (A.mulVec x - b) = 0 := by
      rw [dotProduct_sub, hmain, sub_self]
    simpa [dotProduct] using hz
  have hzero_each :=
    (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun i : Fin m => y i * ((A.mulVec x) i - b i))
      (by
        intro i _
        exact hsum_nonneg i)).mp hsum_eq_zero
  intro i
  exact hzero_each i (Finset.mem_univ i)

/-- Complementary slackness plus dual feasibility identifies the primal and dual objectives. -/
private lemma dualObjective_eq_of_complementarySlackness
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x c : Fin n → ℝ) (y : Fin m → ℝ)
    (_hfeas : PrimalFeasible A b x)
    (hcs : ComplementarySlackness A x b y)
    (hyA : A.transpose.mulVec y = c) :
    dotProduct b y = dotProduct c x := by
  rcases hcs with ⟨_, hzero⟩
  have hsumzero : dotProduct y (A.mulVec x - b) = 0 := by
    -- Every summand is exactly one complementary-slackness equation.
    unfold dotProduct
    simp [Pi.sub_apply, hzero]
  have hmain : dotProduct y (A.mulVec x) = dotProduct y b := by
    rw [dotProduct_sub] at hsumzero
    linarith
  calc
    dotProduct b y = dotProduct y b := by rw [dotProduct_comm]
    _ = dotProduct y (A.mulVec x) := hmain.symm
    _ = dotProduct c x := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose A y, hyA]

/-
Let (A in mathbf{R}^{m \times n}) be given. For each (j = 1, ..., r), let (b^{(j)} in mathbf{R}^m)
and (x^{(j)} in mathbf{R}^n). Consider the linear program with unknown cost. Prove that there
exists a vector (c in mathbf{R}^n) such that, for every (j = 1, ..., r), the point (x^{(j)}) is an
optimal solution of the above linear program with (b = b^{(j)}) if and only if there exist vectors
(y^{(1)}, ..., y^{(r)} in mathbf{R}^m) such that: [ Ax^{(j)} ge b^{(j)}, y^{(j)} ge 0, A^T y^{(j)} =
A^T y^{(1)} (j = 1, ..., r), ] and [ big(y^{(j)} big)^T big(Ax^{(j)} - b^{(j)} big) = 0 (j = 1, ...,
r).
]
-/
theorem exists_common_cost_vector_iff_exists_dual_certificates
    {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin r → Fin m → ℝ) (x : Fin r → Fin n → ℝ) :
    (∃ c : Fin n → ℝ,
      ∀ j : Fin r,
        PrimalFeasible A (b j) (x j) ∧
        ∀ z : Fin n → ℝ, PrimalFeasible A (b j) z → dotProduct c (x j) ≤ dotProduct c z) ↔
    ∃ y : Fin r → Fin m → ℝ,
      (∀ j : Fin r, PrimalFeasible A (b j) (x j)) ∧
      (∀ j : Fin r, ComponentwiseGE (y j) 0) ∧
      (∀ j1 j2 : Fin r, A.transpose.mulVec (y j1) = A.transpose.mulVec (y j2)) ∧
      (∀ j : Fin r, ComplementarySlackness A (x j) (b j) (y j)) := by
  constructor
  · rintro ⟨c, hc⟩
    classical
    choose y hy using fun j =>
      exists_dualCertificate_of_fixedIndexOptimality A (b j) (x j) c (hc j).1 (hc j).2
    refine ⟨y, ?_, ?_, ?_, ?_⟩
    · -- The primal feasibility facts are already part of the optimality hypothesis.
      intro j
      exact (hc j).1
    · -- Each extracted dual certificate is coordinatewise nonnegative.
      intro j i
      exact (hy j).1 i
    · -- All dual certificates share the same cost vector `c`.
      intro j1 j2
      exact (hy j1).2.1.trans (hy j2).2.1.symm
    · -- Zero duality gap upgrades the certificates to complementary slackness.
      intro j
      exact complementarySlackness_of_zero_duality_gap A (b j) (x j) c (y j)
        (hc j).1 (hy j).1 (hy j).2.1 (hy j).2.2
  · rintro ⟨y, hfeas, hy_nonneg, hy_common, hcs⟩
    classical
    by_cases hr : IsEmpty (Fin r)
    · refine ⟨0, ?_⟩
      intro j
      exact (hr.false j).elim
    · obtain ⟨j0⟩ := not_isEmpty_iff.mp hr
      let c : Fin n → ℝ := A.transpose.mulVec (y j0)
      refine ⟨c, ?_⟩
      intro j
      refine ⟨hfeas j, ?_⟩
      have hyA : A.transpose.mulVec (y j) = c := by
        simpa [c] using hy_common j j0
      have hgap : dotProduct (b j) (y j) = dotProduct c (x j) := by
        exact dualObjective_eq_of_complementarySlackness A (b j) (x j) c (y j)
          (hfeas j) (hcs j) hyA
      exact dualCertificate_implies_fixedIndexOptimality A (b j) (x j) c (hfeas j)
        ⟨y j, hy_nonneg j, by simpa [Matrix.mulVec] using hyA, hgap⟩

end «problem-126»
