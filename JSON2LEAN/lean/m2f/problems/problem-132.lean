import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-132»

-- Exercise_7_17__b_

/- [BLOCK Exercise 7.17-(b) | 18 | defn]
For a set C ⊆ ℝ^n, its polar is defined by
C^circ = {x ∈ ℝ^n | uᵀ x ≤ 1 for all u ∈ C}.
-/
def polar (C : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ u ∈ C, ∑ i, u i * x i ≤ 1}

/- [BLOCK Exercise 7.17-(b) | 19 | defn]
A set C ⊆ ℝ^n is a polyhedron if there exist A ∈ ℝ^m × n and b ∈ ℝ^m such that
C = {x ∈ ℝ^n | Ax ≤ b},
where the inequality is componentwise.
-/
def IsPolyhedron (C : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
    C = {x | ∀ i, ∑ j, A i j * x j ≤ b i}

/- [BLOCK Exercise 7.17-(b) | 20 | defn]
A quadratic program is an optimization problem of the form
min_x tfrac12 xᵀ Q x + cᵀ x + r
subject to finitely many affine equality and affine inequality constraints, where Q is symmetric.
-/
structure QuadraticProgram where
  n : ℕ
  meq : ℕ
  mineq : ℕ
  Q : Fin n → Fin n → ℝ
  c : Fin n → ℝ
  r : ℝ
  Aeq : Fin meq → Fin n → ℝ
  beq : Fin meq → ℝ
  Aineq : Fin mineq → Fin n → ℝ
  bineq : Fin mineq → ℝ
  Q_symm : Matrix.IsSymm Q

def QuadraticProgram.objective (P : QuadraticProgram) (x : Fin P.n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, x i * P.Q i j * x j) + (∑ i, P.c i * x i) + P.r

def QuadraticProgram.eqFeasible (P : QuadraticProgram) (x : Fin P.n → ℝ) : Prop :=
  ∀ i, ∑ j, P.Aeq i j * x j = P.beq i

def QuadraticProgram.ineqFeasible (P : QuadraticProgram) (x : Fin P.n → ℝ) : Prop :=
  ∀ i, ∑ j, P.Aineq i j * x j ≤ P.bineq i

def QuadraticProgram.FeasibleSet (P : QuadraticProgram) : Set (Fin P.n → ℝ) :=
  {x | QuadraticProgram.eqFeasible P x ∧ QuadraticProgram.ineqFeasible P x}

/- [BLOCK Exercise 7.17-(b) | 21 | opt_prob]
array{ll}
minimize & ‖x₁-x₂‖_2^2 ;
subject\ to & x₁ ∈ C₁^circ, ;
& x₂ ∈ C₂^circ
array
with variables x₁, x₂ ∈ ℝ^n.
-/
structure PolarDistanceMinimization where
  n : ℕ
  C₁ : Set (Fin n → ℝ)
  C₂ : Set (Fin n → ℝ)

def PolarDistanceMinimization.isFeasible
    (P : PolarDistanceMinimization) (x₁ x₂ : Fin P.n → ℝ) : Prop :=
  x₁ ∈ polar P.C₁ ∧ x₂ ∈ polar P.C₂

def PolarDistanceMinimization.objective
    (P : PolarDistanceMinimization) (x₁ x₂ : Fin P.n → ℝ) : ℝ :=
  ∑ i, (x₁ i - x₂ i) ^ 2

def PolarDistanceMinimization.feasibleSet
    (P : PolarDistanceMinimization) : Set ((Fin P.n → ℝ) × (Fin P.n → ℝ)) :=
  {(x₁, x₂) | P.isFeasible x₁ x₂}

/- [BLOCK Exercise 7.17-(b) | 22 | opt_prob]
array{ll}
minimize & ‖x₁-x₂‖_2^2 ;
subject\ to & A_1ᵀ λ_1 = x₁, ;
& b_1ᵀ λ_1 ≤ 1, ;
& λ_1 succeq 0, ;
& A_2ᵀ λ_2 = x₂, ;
& b_2ᵀ λ_2 ≤ 1, ;
& λ_2 succeq 0
array
with variables x₁, x₂ ∈ ℝ^n, λ_1 ∈ ℝ^m₁, and λ_2 ∈ ℝ^m₂.
-/
structure PolarDistanceQP where
  n : ℕ
  m₁ : ℕ
  m₂ : ℕ
  A₁ : Fin m₁ → Fin n → ℝ
  b₁ : Fin m₁ → ℝ
  A₂ : Fin m₂ → Fin n → ℝ
  b₂ : Fin m₂ → ℝ

def PolarDistanceQP.isFeasible
    (P : PolarDistanceQP)
    (x₁ x₂ : Fin P.n → ℝ)
    (lam₁ : Fin P.m₁ → ℝ)
    (lam₂ : Fin P.m₂ → ℝ) : Prop :=
  (∀ i, ∑ j, P.A₁ j i * lam₁ j = x₁ i) ∧
  (∑ j, P.b₁ j * lam₁ j ≤ 1) ∧
  (∀ j, 0 ≤ lam₁ j) ∧
  (∀ i, ∑ j, P.A₂ j i * lam₂ j = x₂ i) ∧
  (∑ j, P.b₂ j * lam₂ j ≤ 1) ∧
  (∀ j, 0 ≤ lam₂ j)

def PolarDistanceQP.objective
    (P : PolarDistanceQP) (x₁ x₂ : Fin P.n → ℝ) : ℝ :=
  ∑ i, (x₁ i - x₂ i) ^ 2

def PolarDistanceQP.feasibleSet
    (P : PolarDistanceQP) :
    Set ((Fin P.n → ℝ) × (Fin P.n → ℝ) × (Fin P.m₁ → ℝ) × (Fin P.m₂ → ℝ)) :=
  {y | P.isFeasible y.1 y.2.1 y.2.2.1 y.2.2.2}

/-- The Euclidean dual cone of a set in `ℝ^n`, expressed using the standard inner product. -/
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
  simpa using Matrix.toEuclideanLin_apply A x

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
  change Matrix.toEuclideanLin Aᵀ v.1 = Aᵀ.mulVec v.1
  exact toEuclideanLin_eq_mulVec Aᵀ v.1

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
    · rcases hpos with ⟨i, his, hfi⟩
      have hpos' : ∃ i ∈ s, 0 < f i := ⟨i, his, hfi⟩
      have hgi : 0 < g i := by
        have hg_eq : g i = f i := by
          simp [g, hpos']
        rw [hg_eq]
        exact hfi
      exact ⟨i, his, hgi⟩
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
      simp [w, wFun, hvi, hci]
  have hwiStar : w.1 iStar = 0 := by
    -- The minimizing coordinate is forced to hit zero exactly.
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
  -- Erase the new zero coordinate to get a representation on a strict subset.
  exact ⟨iStar, hiStarS,
    rowSubsetCone_erase_of_zero_coordinate A w hw_nonneg hyw hiStarS hwiStar⟩

/-- Every point in the transpose image cone admits a representation on an independent support. -/
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

/-- The transpose image of the coordinatewise nonnegative orthant is closed. -/
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

/-- Finite-dimensional Farkas lemma for coordinatewise nonnegative matrix preimages. -/
private theorem dualCone_of_nonnegative_preimage_eq_range_transpose_nonnegative
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    dualCone {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, 0 ≤ (A.mulVec x) i} =
      {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  -- Reduce the theorem to the closedness of the explicit transpose image cone.
  rw [dualCone_eq_closure_transpose_nonnegative_image]
  exact (isClosed_transpose_nonnegative_image A).closure_eq

/-- The augmented matrix whose nonnegative preimage is the homogenized cone
`{(t,u) | 0 ≤ t ∧ A u ≤ t b}`. -/
private def polarCertificateMatrix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ :=
  fun i j =>
    Fin.cases
      (Fin.cases 1 (fun _ => 0) j)
      (fun i => Fin.cases (b i) (fun j => -A i j) j)
      i

/-- The Euclidean vector obtained by adjoining a head coordinate to a tail vector. -/
private def liftEuclidean {n : ℕ} (t : ℝ) (u : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (Fin.cons t u)

/-- The head coordinate of `liftEuclidean` is the adjoined scalar. -/
@[simp] private lemma liftEuclidean_zero {n : ℕ} (t : ℝ) (u : Fin n → ℝ) :
    liftEuclidean t u 0 = t := by
  simp [liftEuclidean]

/-- The tail coordinates of `liftEuclidean` recover the original vector. -/
@[simp] private lemma liftEuclidean_succ {n : ℕ} (t : ℝ) (u : Fin n → ℝ) (i : Fin n) :
    liftEuclidean t u i.succ = u i := by
  simp [liftEuclidean]

/-- Forgetting the Euclidean structure on `liftEuclidean` yields the original `Fin.cons` tuple. -/
@[simp] private lemma liftEuclidean_ofLp {n : ℕ} (t : ℝ) (u : Fin n → ℝ) :
    (liftEuclidean t u).ofLp = Fin.cons t u := by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [liftEuclidean]

/-- The first row of the augmented matrix encodes the scalar constraint `0 ≤ t`. -/
@[simp] private lemma polarCertificateMatrix_mulVec_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (t : ℝ) (u : Fin n → ℝ) :
    (polarCertificateMatrix A b).mulVec (Fin.cons t u) 0 = t := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp [polarCertificateMatrix]

/-- The remaining rows of the augmented matrix encode `A u ≤ t b`. -/
@[simp] private lemma polarCertificateMatrix_mulVec_succ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (t : ℝ) (u : Fin n → ℝ) (i : Fin m) :
    (polarCertificateMatrix A b).mulVec (Fin.cons t u) i.succ =
      t * b i - (A.mulVec u) i := by
  calc
    (polarCertificateMatrix A b).mulVec (Fin.cons t u) i.succ
        = b i * t + ∑ j, (-A i j) * u j := by
            rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
            simp [polarCertificateMatrix]
    _ = t * b i - ∑ j, A i j * u j := by
          rw [mul_comm (b i) t]
          have hsum : ∑ j, (-A i j) * u j = -∑ j, A i j * u j := by
            calc
              ∑ j, (-A i j) * u j = ∑ j, -(A i j * u j) := by
                congr with j
                ring
              _ = -∑ j, A i j * u j := by
                rw [Finset.sum_neg_distrib]
          calc
            t * b i + ∑ j, (-A i j) * u j = t * b i + -∑ j, A i j * u j := by
              exact congrArg (fun s => t * b i + s) hsum
            _ = t * b i - ∑ j, A i j * u j := by
              rw [sub_eq_add_neg]
    _ = t * b i - (A.mulVec u) i := by
          rfl

/-- The head coordinate of the transpose image reads off the slack equation
`s + bᵀ λ = 1`. -/
@[simp] private lemma polarCertificateMatrix_transpose_mulVec_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (μ : Fin (m + 1) → ℝ) :
    (polarCertificateMatrix A b)ᵀ.mulVec μ 0 = μ 0 + dotProduct b (Fin.tail μ) := by
  calc
    (polarCertificateMatrix A b)ᵀ.mulVec μ 0 = μ 0 + ∑ j, b j * μ j.succ := by
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      simp [polarCertificateMatrix]
    _ = μ 0 + dotProduct b (Fin.tail μ) := by
      rfl

/-- The tail coordinates of the transpose image recover `-Aᵀ λ`. -/
@[simp] private lemma polarCertificateMatrix_transpose_mulVec_succ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (μ : Fin (m + 1) → ℝ) (i : Fin n) :
    (polarCertificateMatrix A b)ᵀ.mulVec μ i.succ = -((Aᵀ).mulVec (Fin.tail μ)) i := by
  calc
    (polarCertificateMatrix A b)ᵀ.mulVec μ i.succ = ∑ j, (-A j i) * μ j.succ := by
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      simp [polarCertificateMatrix]
    _ = -∑ j, A j i * μ j.succ := by
      calc
        ∑ j, (-A j i) * μ j.succ = ∑ j, -(A j i * μ j.succ) := by
          congr with j
          ring
        _ = -∑ j, A j i * μ j.succ := by
          rw [Finset.sum_neg_distrib]
    _ = -((Aᵀ).mulVec (Fin.tail μ)) i := by
      rfl

/-- Pairing `(1,-x)` with `(t,u)` produces the scalar slack `t - uᵀx`. -/
private lemma inner_lift_neg_eq_scalar_sub_dot {n : ℕ}
    (t : ℝ) (u x : Fin n → ℝ) :
    dotProduct (Fin.cons 1 (-x)) (Fin.cons t u) = t - dotProduct u x := by
  simp [dotProduct, Fin.sum_univ_succ, sub_eq_add_neg, mul_comm]

/-- A vector in the polar is nonpositive on every recession direction of the underlying
polyhedron. -/
private lemma polar_polyhedron_recession_nonpos
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {x d : Fin n → ℝ}
    (hx : x ∈ polar {u : Fin n → ℝ | ∀ i, (A.mulVec u) i ≤ b i})
    (hC : {u : Fin n → ℝ | ∀ i, (A.mulVec u) i ≤ b i} ≠ (∅ : Set (Fin n → ℝ)))
    (hd : ∀ i, (A.mulVec d) i ≤ 0) :
    dotProduct d x ≤ 0 := by
  -- Pick one feasible base point and push it along the recession direction.
  obtain ⟨u₀, hu₀⟩ := Set.nonempty_iff_ne_empty.mpr hC
  by_contra hdx
  have hdx_pos : 0 < dotProduct d x := by linarith
  let s : ℝ := (|1 - dotProduct u₀ x| + 1) / dotProduct d x
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hs_mul : s * dotProduct d x = |1 - dotProduct u₀ x| + 1 := by
    dsimp [s]
    field_simp [hdx_pos.ne']
  have hfeasible : u₀ + s • d ∈ {u : Fin n → ℝ | ∀ i, (A.mulVec u) i ≤ b i} := by
    -- Each inequality stays feasible because the recession term is nonpositive.
    intro i
    have hstep : (A.mulVec (u₀ + s • d)) i = (A.mulVec u₀) i + s * (A.mulVec d) i := by
      simp [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have hscaled : s * (A.mulVec d) i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs_nonneg (hd i)
    linarith [hu₀ i, hstep]
  have hpolar_step : dotProduct (u₀ + s • d) x ≤ 1 := hx _ hfeasible
  have hdot_step : dotProduct (u₀ + s • d) x = dotProduct u₀ x + s * dotProduct d x := by
    rw [add_dotProduct, smul_dotProduct]
    simp [smul_eq_mul]
  have hbase : 1 ≤ dotProduct u₀ x + |1 - dotProduct u₀ x| := by
    have habs : 1 - dotProduct u₀ x ≤ |1 - dotProduct u₀ x| := le_abs_self (1 - dotProduct u₀ x)
    linarith
  have hstrict : 1 < dotProduct u₀ x + s * dotProduct d x := by
    rw [hs_mul]
    linarith
  linarith [hpolar_step, hdot_step, hstrict]

/-- A polyhedral polar point is equivalent to a nonnegative dual multiplier certificate. -/
private lemma polar_polyhedron_iff_exists_dual_certificate
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hC : {u : Fin n → ℝ | ∀ i, (A.mulVec u) i ≤ b i} ≠ (∅ : Set (Fin n → ℝ)))
    (x : Fin n → ℝ) :
    x ∈ polar {u : Fin n → ℝ | ∀ i, (A.mulVec u) i ≤ b i} ↔
      ∃ lam : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ lam i) ∧
        Aᵀ.mulVec lam = x ∧
        dotProduct b lam ≤ 1 := by
  let B : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ := polarCertificateMatrix A b
  let K : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {z | ∀ i : Fin (m + 1), 0 ≤ (B.mulVec z) i}
  let y : EuclideanSpace ℝ (Fin (n + 1)) := liftEuclidean 1 (-x)
  constructor
  · intro hx
    have hyDual : y ∈ dualCone K := by
      rw [dualCone]
      intro z hz
      let t : ℝ := z 0
      let u : Fin n → ℝ := Fin.tail z.ofLp
      have hz_eq : z.ofLp = Fin.cons t u := by
        ext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      have ht : 0 ≤ t := by
        have hz0 : 0 ≤ (B.mulVec z) 0 := hz 0
        rw [show (z : Fin (n + 1) → ℝ) = Fin.cons t u by simp [hz_eq]] at hz0
        simpa [B] using hz0
      have hcone : ∀ i : Fin m, (A.mulVec u) i ≤ t * b i := by
        intro i
        have hrow : 0 ≤ (B.mulVec z) i.succ := hz i.succ
        rw [show (z : Fin (n + 1) → ℝ) = Fin.cons t u by simp [hz_eq]] at hrow
        simpa [B] using hrow
      by_cases ht0 : t = 0
      · -- When `t = 0`, the homogenized point is a recession direction.
        have hd : ∀ i : Fin m, (A.mulVec u) i ≤ 0 := by
          intro i
          simpa [ht0] using hcone i
        have hrec : dotProduct u x ≤ 0 := polar_polyhedron_recession_nonpos A b hx hC hd
        have hinner0 : 0 ≤ t - dotProduct u x := by
          linarith
        rw [real_inner_comm]
        rw [PiLp.inner_apply]
        simp only [RCLike.inner_apply]
        rw [hz_eq]
        rw [show y.ofLp = Fin.cons 1 (-x) by simp [y]]
        have hsum :
            ∑ i, (Fin.cons 1 (-x) : Fin (n + 1) → ℝ) i *
              (starRingEnd ℝ) ((Fin.cons t u : Fin (n + 1) → ℝ) i) =
              t - dotProduct u x := by
          simpa [dotProduct] using inner_lift_neg_eq_scalar_sub_dot t u x
        nlinarith [hinner0, hsum]
      · -- When `t > 0`, scale back to a feasible point in the original polyhedron.
        have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        let uScaled : Fin n → ℝ := (1 / t) • u
        have huScaled :
            uScaled ∈ {u : Fin n → ℝ | ∀ i, (A.mulVec u) i ≤ b i} := by
          intro i
          have hscale : (A.mulVec uScaled) i = (1 / t) * (A.mulVec u) i := by
            simp [uScaled, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
          have hscaled : (1 / t) * (A.mulVec u) i ≤ b i := by
            have hmul :=
              mul_le_mul_of_nonneg_left (hcone i) (show 0 ≤ 1 / t by positivity)
            simpa [ht_pos.ne', mul_assoc] using hmul
          simpa [hscale] using hscaled
        have hpolar_scaled : dotProduct uScaled x ≤ 1 := hx _ huScaled
        have hdot_scaled : dotProduct uScaled x = (1 / t) * dotProduct u x := by
          rw [smul_dotProduct]
          simp [smul_eq_mul]
        have hdot : dotProduct u x ≤ t := by
          have hmul :=
            mul_le_mul_of_nonneg_left hpolar_scaled (show 0 ≤ t by linarith)
          simpa [hdot_scaled, ht_pos.ne', mul_assoc] using hmul
        have hinner0 : 0 ≤ t - dotProduct u x := by
          linarith
        rw [real_inner_comm]
        rw [PiLp.inner_apply]
        simp only [RCLike.inner_apply]
        rw [hz_eq]
        rw [show y.ofLp = Fin.cons 1 (-x) by simp [y]]
        have hsum :
            ∑ i, (Fin.cons 1 (-x) : Fin (n + 1) → ℝ) i *
              (starRingEnd ℝ) ((Fin.cons t u : Fin (n + 1) → ℝ) i) =
              t - dotProduct u x := by
          simpa [dotProduct] using inner_lift_neg_eq_scalar_sub_dot t u x
        nlinarith [hinner0, hsum]
    rw [show K = {z : EuclideanSpace ℝ (Fin (n + 1)) |
        ∀ i : Fin (m + 1), 0 ≤ (B.mulVec z) i} by rfl] at hyDual
    rw [dualCone_of_nonnegative_preimage_eq_range_transpose_nonnegative B] at hyDual
    rcases hyDual with ⟨μ, hμ_nonneg, hμEq⟩
    let lam : Fin m → ℝ := Fin.tail μ
    have hlam_nonneg : ∀ i : Fin m, 0 ≤ lam i := by
      intro i
      simpa [lam] using hμ_nonneg i.succ
    have hhead : 1 = μ 0 + dotProduct b lam := by
      -- Read the scalar slack equation from the head coordinate.
      simpa [y, B, lam] using
        congrArg (fun v : Fin (n + 1) → ℝ => v 0) hμEq
    have hlam_eq : Aᵀ.mulVec lam = x := by
      -- Read the multiplier equation from the tail coordinates.
      ext i
      have hcoord : -x i = -((Aᵀ).mulVec lam) i := by
        simpa [y, B, lam] using
          congrArg (fun v : Fin (n + 1) → ℝ => v i.succ) hμEq
      linarith
    have hblam : dotProduct b lam ≤ 1 := by
      have hs_nonneg : 0 ≤ μ 0 := hμ_nonneg 0
      linarith
    exact ⟨lam, hlam_nonneg, hlam_eq, hblam⟩
  · rintro ⟨lam, hlam_nonneg, hlam_eq, hblam⟩
    let s : ℝ := 1 - dotProduct b lam
    let μ : EuclideanSpace ℝ (Fin (m + 1)) := liftEuclidean s lam
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      linarith
    have hμ_nonneg : ∀ i : Fin (m + 1), 0 ≤ μ i := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simpa [μ, s]
      · intro j
        simpa [μ] using hlam_nonneg j
    have hyEq : y = Bᵀ.mulVec μ := by
      -- Package the multiplier and the slack into the augmented transpose equation.
      ext i
      refine Fin.cases ?_ ?_ i
      · simp [y, B, μ, s, dotProduct]
      · intro j
        have hcoord : -x j = -((Aᵀ).mulVec lam) j := by
          have hxj : ((Aᵀ).mulVec lam) j = x j := by
            simpa using congrArg (fun v : Fin n → ℝ => v j) hlam_eq
          linarith
        simpa [y, B, μ] using hcoord
    have hyDual : y ∈ dualCone K := by
      rw [show K = {z : EuclideanSpace ℝ (Fin (n + 1)) |
          ∀ i : Fin (m + 1), 0 ≤ (B.mulVec z) i} by rfl]
      rw [dualCone_of_nonnegative_preimage_eq_range_transpose_nonnegative B]
      exact ⟨μ, hμ_nonneg, hyEq⟩
    -- Test the dual-cone condition on `(1,u)` for an arbitrary feasible `u`.
    intro u hu
    let zu : EuclideanSpace ℝ (Fin (n + 1)) := liftEuclidean 1 u
    have hKu : zu ∈ K := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simp [B, zu]
      · intro j
        have hrow : 0 ≤ b j - (A.mulVec u) j := by
          linarith [hu j]
        simpa [K, B, zu, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hrow
    have hyDual' := by
      simpa [dualCone] using hyDual
    have hinner := hyDual' zu hKu
    have hpolar : 0 ≤ 1 - dotProduct u x := by
      rw [real_inner_comm] at hinner
      rw [PiLp.inner_apply] at hinner
      simp only [RCLike.inner_apply] at hinner
      rw [show zu.ofLp = Fin.cons 1 u by simp [zu]] at hinner
      rw [show y.ofLp = Fin.cons 1 (-x) by simp [y]] at hinner
      have hsum :
          ∑ i, (Fin.cons 1 (-x) : Fin (n + 1) → ℝ) i *
            (starRingEnd ℝ) ((Fin.cons 1 u : Fin (n + 1) → ℝ) i) =
            1 - dotProduct u x := by
        simpa [dotProduct] using inner_lift_neg_eq_scalar_sub_dot 1 u x
      nlinarith [hinner, hsum]
    simpa [dotProduct] using hpolar

/- [BLOCK Exercise 7.17-(b) | 23 | thm]
Let the polar of a set C ⊆ ℝ^n be defined by C^{circ}={x ∈ ℝ^n | uᵀ x ≤ 1 for all u ∈ C}. Let C₁={u
∈ ℝ^n | A_1u ≤ b₁} and C₂={v ∈ ℝ^n | A_2v ≤ b₂}, where C₁ and C₂ are nonempty polyhedra, A₁ ∈ ℝ^{m₁
× n}, A₂ ∈ ℝ^{m₂ × n}, b₁ ∈ ℝ^{m₁}, and b₂ ∈ ℝ^{m₂}, and the inequalities are componentwise. Prove
that the optimization problem polar distance minimization is equivalent to the quadratic program
quadratic program reformulation.
-/
theorem polar_distance_minimization_equivalent_to_quadratic_program_reformulation
    (n m₁ m₂ : ℕ)
    (A₁ : Fin m₁ → Fin n → ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Fin m₂ → Fin n → ℝ)
    (b₂ : Fin m₂ → ℝ)
    (hC₁ :
      {u : Fin n → ℝ | ∀ i, ∑ j, A₁ i j * u j ≤ b₁ i} ≠ (∅ : Set (Fin n → ℝ)))
    (hC₂ :
      {v : Fin n → ℝ | ∀ i, ∑ j, A₂ i j * v j ≤ b₂ i} ≠ (∅ : Set (Fin n → ℝ))) :
    let P : PolarDistanceMinimization := {
      n := n
      C₁ := {u : Fin n → ℝ | ∀ i, ∑ j, A₁ i j * u j ≤ b₁ i}
      C₂ := {v : Fin n → ℝ | ∀ i, ∑ j, A₂ i j * v j ≤ b₂ i}
    }
    let QP : PolarDistanceQP := {
      n := n
      m₁ := m₁
      m₂ := m₂
      A₁ := A₁
      b₁ := b₁
      A₂ := A₂
      b₂ := b₂
    }
    ∀ x₁ x₂ : Fin n → ℝ,
      P.isFeasible x₁ x₂ ↔
        ∃ lam₁ : Fin m₁ → ℝ, ∃ lam₂ : Fin m₂ → ℝ,
          QP.isFeasible x₁ x₂ lam₁ lam₂ := by
  -- Unfold both optimization models so the theorem becomes two independent polar-certificate
  -- equivalences.
  dsimp [PolarDistanceMinimization.isFeasible, PolarDistanceQP.isFeasible]
  intro x₁ x₂
  constructor
  · rintro ⟨hx₁, hx₂⟩
    rcases (polar_polyhedron_iff_exists_dual_certificate
        (A := A₁) (b := b₁) (hC := by simpa [Matrix.mulVec] using hC₁) x₁).mp
        (by simpa [Matrix.mulVec] using hx₁) with ⟨lam₁, hlam₁_nonneg, hlam₁_eq, hblam₁⟩
    rcases (polar_polyhedron_iff_exists_dual_certificate
        (A := A₂) (b := b₂) (hC := by simpa [Matrix.mulVec] using hC₂) x₂).mp
        (by simpa [Matrix.mulVec] using hx₂) with ⟨lam₂, hlam₂_nonneg, hlam₂_eq, hblam₂⟩
    -- Package the two one-set certificates into the QP feasibility predicate.
    refine ⟨lam₁, lam₂, ?_⟩
    refine ⟨?_, ?_, hlam₁_nonneg, ?_, ?_, hlam₂_nonneg⟩
    · intro i
      simpa [Matrix.mulVec] using congrArg (fun v : Fin n → ℝ => v i) hlam₁_eq
    · simpa [dotProduct] using hblam₁
    · intro i
      simpa [Matrix.mulVec] using congrArg (fun v : Fin n → ℝ => v i) hlam₂_eq
    · simpa [dotProduct] using hblam₂
  · rintro ⟨lam₁, lam₂, hfeas⟩
    rcases hfeas with ⟨hA₁, hb₁, hlam₁_nonneg, hA₂, hb₂, hlam₂_nonneg⟩
    -- Unpack the QP witnesses and apply the same one-set equivalence in reverse.
    refine ⟨?_, ?_⟩
    · exact (polar_polyhedron_iff_exists_dual_certificate
        (A := A₁) (b := b₁) (hC := by simpa [Matrix.mulVec] using hC₁) x₁).mpr
        ⟨lam₁, hlam₁_nonneg, by
          ext i
          simpa [Matrix.mulVec] using hA₁ i, by simpa [dotProduct] using hb₁⟩
    · exact (polar_polyhedron_iff_exists_dual_certificate
        (A := A₂) (b := b₂) (hC := by simpa [Matrix.mulVec] using hC₂) x₂).mpr
        ⟨lam₂, hlam₂_nonneg, by
          ext i
          simpa [Matrix.mulVec] using hA₂ i, by simpa [dotProduct] using hb₂⟩

end «problem-132»
