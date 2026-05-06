import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open scoped Pointwise
open Filter
open scoped BigOperators

namespace «problem-21»
/-
Let C be the copositive cone of real symmetric matrices, C = {X ∈ S^n | zᵀ X z ≥ 0 for every z ≥ 0}.
The dual cone is C* = {Y ∈ S^n | trace(Y X) ≥ 0 for every X ∈ C}. Prove that C* is the convex hull
of the rank - one matrices z zᵀ with z ≥ 0.
-/

/-- The trace pairing with a rank-one generator is exactly the copositive quadratic form. -/
lemma trace_vecMulVec_mul_eq_dotProduct {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    Matrix.trace (Matrix.vecMulVec z z * X) = dotProduct z (X.mulVec z) := by
  -- Rotate the trace so the standard `mul_vecMulVec` lemma applies on the left.
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- Every nonnegative rank-one generator belongs to the trace-dual of the copositive cone. -/
lemma rankOne_nonneg_mem_copositiveDualCone {n : ℕ} {z : Fin n → ℝ}
    (hz : ∀ i, 0 ≤ z i) :
    Matrix.vecMulVec z z ∈
      {Y : Matrix (Fin n) (Fin n) ℝ |
        Y.IsSymm ∧
          ∀ X,
            X ∈ {X : Matrix (Fin n) (Fin n) ℝ |
              X.IsSymm ∧ ∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) → 0 ≤ dotProduct z (X.mulVec z)} →
            0 ≤ Matrix.trace (Y * X)} := by
  constructor
  · -- Rank-one outer products are symmetric by construction.
    simp [Matrix.IsSymm]
  · intro X hX
    rcases hX with ⟨_, hXcopositive⟩
    -- Rewrite the trace pairing into the defining copositive quadratic form.
    rw [trace_vecMulVec_mul_eq_dotProduct]
    exact hXcopositive z hz

/-- The trace-dual of the copositive cone is convex. -/
lemma copositiveDualCone_convex {n : ℕ} :
    Convex ℝ
      {Y : Matrix (Fin n) (Fin n) ℝ |
        Y.IsSymm ∧
          ∀ X,
            X ∈ {X : Matrix (Fin n) (Fin n) ℝ |
              X.IsSymm ∧ ∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) → 0 ≤ dotProduct z (X.mulVec z)} →
            0 ≤ Matrix.trace (Y * X)} := by
  intro Y₁ hY₁ Y₂ hY₂ a b ha hb _hab
  rcases hY₁ with ⟨hY₁symm, hY₁dual⟩
  rcases hY₂ with ⟨hY₂symm, hY₂dual⟩
  constructor
  · -- Symmetry is preserved by linear combinations.
    simpa using (hY₁symm.smul a).add (hY₂symm.smul b)
  · intro X hX
    have h₁ : 0 ≤ Matrix.trace (Y₁ * X) := hY₁dual X hX
    have h₂ : 0 ≤ Matrix.trace (Y₂ * X) := hY₂dual X hX
    -- Expand the trace pairing linearly and combine the two nonnegative pieces.
    calc
      0 ≤ a * Matrix.trace (Y₁ * X) + b * Matrix.trace (Y₂ * X) :=
        add_nonneg (mul_nonneg ha h₁) (mul_nonneg hb h₂)
      _ = Matrix.trace ((a • Y₁ + b • Y₂) * X) := by
        simp [Matrix.add_mul]

/-- The convex hull of the nonnegative rank-one generators is contained in the dual copositive cone. -/
lemma convexHull_rankOne_nonneg_subset_copositiveDualCone {n : ℕ} :
    convexHull ℝ {Y : Matrix (Fin n) (Fin n) ℝ |
      ∃ z : Fin n → ℝ, (∀ i, 0 ≤ z i) ∧ Y = Matrix.vecMulVec z z} ⊆
      {Y : Matrix (Fin n) (Fin n) ℝ |
        Y.IsSymm ∧
          ∀ X,
            X ∈ {X : Matrix (Fin n) (Fin n) ℝ |
              X.IsSymm ∧ ∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) → 0 ≤ dotProduct z (X.mulVec z)} →
            0 ≤ Matrix.trace (Y * X)} := by
  -- It suffices to show the target set is convex and contains every generator.
  refine convexHull_min ?_ copositiveDualCone_convex
  rintro Y ⟨z, hz, rfl⟩
  exact rankOne_nonneg_mem_copositiveDualCone hz

/-- The trace-one nonnegative vectors used to normalize the rank-one generators. -/
def nonnegativeUnitVectors (n : ℕ) : Set (Fin n → ℝ) :=
  {z | (∀ i, 0 ≤ z i) ∧ dotProduct z z = 1}

/-- The normalized nonnegative rank-one generators with trace equal to `1`. -/
def normalizedNonnegativeRankOneBase (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {Y | ∃ z : Fin n → ℝ, (∀ i, 0 ≤ z i) ∧ dotProduct z z = 1 ∧ Y = Matrix.vecMulVec z z}

/-- The nonnegative unit vectors form a compact slice of the unit sphere. -/
lemma nonnegativeUnitVectors_compact {n : ℕ} :
    IsCompact (nonnegativeUnitVectors n) := by
  -- The coordinatewise nonnegative orthant is closed.
  have hclosedNonneg : IsClosed {z : Fin n → ℝ | ∀ i, 0 ≤ z i} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter (fun i : Fin n => isClosed_le continuous_const (continuous_apply i))
  -- The quadratic constraint is also closed because `z ↦ z ⬝ᵥ z` is continuous.
  have hclosedDot : IsClosed {z : Fin n → ℝ | dotProduct z z = 1} := by
    exact isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
  have hclosed : IsClosed (nonnegativeUnitVectors n) := by
    change IsClosed ({z : Fin n → ℝ | ∀ i, 0 ≤ z i} ∩ {z : Fin n → ℝ | dotProduct z z = 1})
    exact hclosedNonneg.inter hclosedDot
  have hcube :
      IsCompact (Set.pi (Set.univ : Set (Fin n)) (fun _ => Set.Icc (0 : ℝ) 1)) := by
    exact isCompact_univ_pi fun _ => isCompact_Icc
  -- The nonnegative trace-one slice sits inside the compact cube `[0, 1]^n`.
  refine hcube.of_isClosed_subset hclosed ?_
  intro z hz i _
  refine ⟨hz.1 i, ?_⟩
  have hterm : z i * z i ≤ dotProduct z z := by
    simpa [dotProduct] using
      Finset.single_le_sum (fun j _ => mul_nonneg (hz.1 j) (hz.1 j)) (Finset.mem_univ i)
  nlinarith [hz.1 i, hz.2, hterm]

/-- The normalized rank-one base is compact because it is a continuous image of the compact
nonnegative unit sphere slice. -/
lemma normalizedNonnegativeRankOneBase_compact {n : ℕ} :
    IsCompact (normalizedNonnegativeRankOneBase n) := by
  let f : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun z => Matrix.vecMulVec z z
  have hcont : Continuous f := by
    simpa [f] using
      (Continuous.matrix_vecMulVec
        (A := fun z : Fin n → ℝ => z)
        (B := fun z : Fin n → ℝ => z)
        continuous_id continuous_id)
  have himage : f '' nonnegativeUnitVectors n = normalizedNonnegativeRankOneBase n := by
    ext Y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz.1, hz.2, rfl⟩
    · rintro ⟨z, hznonneg, hznorm, rfl⟩
      exact ⟨z, ⟨hznonneg, hznorm⟩, rfl⟩
  -- Push the compact parameter set forward through `z ↦ zzᵀ`.
  rw [← himage]
  exact (nonnegativeUnitVectors_compact (n := n)).image hcont

/-- Every normalized rank-one generator has trace equal to `1`. -/
lemma trace_eq_one_of_mem_normalizedNonnegativeRankOneBase {n : ℕ}
    {Y : Matrix (Fin n) (Fin n) ℝ}
    (hY : Y ∈ normalizedNonnegativeRankOneBase n) :
    Matrix.trace Y = 1 := by
  rcases hY with ⟨z, _hznonneg, hznorm, rfl⟩
  -- The trace of `zzᵀ` is the squared Euclidean norm of `z`.
  calc
    Matrix.trace (Matrix.vecMulVec z z) = dotProduct z z := Matrix.trace_vecMulVec _ _
    _ = 1 := hznorm

/-- Convex combinations of normalized generators still have trace equal to `1`. -/
lemma convexHull_normalizedNonnegativeRankOneBase_subset_trace_eq_one {n : ℕ} :
    convexHull ℝ (normalizedNonnegativeRankOneBase n) ⊆
      {Y : Matrix (Fin n) (Fin n) ℝ | Matrix.trace Y = 1} := by
  -- The trace-one hyperplane is convex and already contains the normalized generators.
  refine convexHull_min ?_ ?_
  · intro Y hY
    exact trace_eq_one_of_mem_normalizedNonnegativeRankOneBase hY
  · intro Y₁ hY₁ Y₂ hY₂ a b ha hb hab
    -- Trace is affine, so convex combinations preserve the value `1`.
    have htrace₁ : Matrix.trace Y₁ = 1 := hY₁
    have htrace₂ : Matrix.trace Y₂ = 1 := hY₂
    change Matrix.trace (a • Y₁ + b • Y₂) = 1
    calc
      Matrix.trace (a • Y₁ + b • Y₂) = a * Matrix.trace Y₁ + b * Matrix.trace Y₂ := by
        simp [Matrix.trace_add]
      _ = 1 := by
        nlinarith [htrace₁, htrace₂, hab]

/-- The convex hull of the normalized nonnegative rank-one base is compact.

This uses Carathéodory's theorem to reduce every convex combination to one with at most
`finrank + 1` points, so the hull becomes a finite union of compact images of simplices times
finite products of the compact base. -/
lemma convexHull_normalizedNonnegativeRankOneBase_compact {n : ℕ} :
    IsCompact (convexHull ℝ (normalizedNonnegativeRankOneBase n)) := by
  let M := Matrix (Fin n) (Fin n) ℝ
  let d : ℕ := Module.finrank ℝ M + 1
  let piece : ℕ → Set M := fun k =>
    (fun p : stdSimplex ℝ (Fin k) × (Fin k → normalizedNonnegativeRankOneBase n) =>
      ∑ i, (p.1 i : ℝ) • ((p.2 i : M))) '' Set.univ
  have hpieceCompact : ∀ k, IsCompact (piece k) := by
    intro k
    letI : CompactSpace ↥(normalizedNonnegativeRankOneBase n) :=
      isCompact_iff_compactSpace.mp (normalizedNonnegativeRankOneBase_compact (n := n))
    let F : stdSimplex ℝ (Fin k) × (Fin k → normalizedNonnegativeRankOneBase n) → M :=
      fun p => ∑ i, (p.1 i : ℝ) • ((p.2 i : M))
    -- Each piece is a continuous image of a compact simplex-times-tuples parameter space.
    have hF : Continuous F := by
      dsimp [F]
      refine continuous_finset_sum _ fun i _ => ?_
      exact
        (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))
    simpa [piece, F] using (isCompact_univ : IsCompact (Set.univ : Set
      (stdSimplex ℝ (Fin k) × (Fin k → normalizedNonnegativeRankOneBase n)))).image hF
  have hsubset :
      convexHull ℝ (normalizedNonnegativeRankOneBase n) ⊆ ⋃ k ∈ Finset.range (d + 1), piece k := by
    intro x hx
    -- Carathéodory gives a positive convex combination indexed by a finite type of bounded size.
    obtain ⟨ι, _, z, w, hz, hAff, hwpos, hwsum, rfl⟩ :=
      eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) hx
    let k : ℕ := Fintype.card ι
    have hk_le : k ≤ d := by
      calc
        k ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 := by
          simpa [k] using (AffineIndependent.card_le_finrank_succ (k := ℝ) (p := z) hAff)
        _ ≤ Module.finrank ℝ M + 1 := Nat.add_le_add_right (Submodule.finrank_le _) 1
    have hk : k ∈ Finset.range (d + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le)
    let e : ι ≃ Fin k := Fintype.equivFin ι
    let w' : stdSimplex ℝ (Fin k) :=
      ⟨fun i => w (e.symm i), by
        constructor
        · intro i
          exact (hwpos (e.symm i)).le
        · simpa using (e.symm.sum_comp w).trans hwsum⟩
    let z' : Fin k → normalizedNonnegativeRankOneBase n :=
      fun i => ⟨z (e.symm i), hz ⟨e.symm i, rfl⟩⟩
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, ?_⟩⟩
    refine ⟨(w', z'), Set.mem_univ _, ?_⟩
    -- Reindex the finite convex combination along the equivalence `ι ≃ Fin k`.
    simpa [w', z'] using (e.symm.sum_comp (fun i : ι => w i • z i))
  have hsuperset :
      (⋃ k ∈ Finset.range (d + 1), piece k) ⊆ convexHull ℝ (normalizedNonnegativeRankOneBase n) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨k, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hk, hx⟩
    rcases hx with ⟨p, -, rfl⟩
    -- Every simplex-weighted finite family in the compact base is a convex combination.
    refine (mem_convexHull_iff_exists_fintype (R := ℝ)
      (s := normalizedNonnegativeRankOneBase n)
      (x := ∑ i : Fin k, (p.1 i : ℝ) • ((p.2 i : M)))).2 ?_
    refine ⟨Fin k, inferInstance, fun i => (p.1 i : ℝ), fun i => ((p.2 i : M)), ?_, ?_, ?_, rfl⟩
    · intro i
      exact p.1.2.1 i
    · exact p.1.2.2
    · intro i
      exact (p.2 i).2
  -- A finite union of compact pieces is compact.
  refine (subset_antisymm hsubset hsuperset) ▸ ?_
  exact (Finset.range (d + 1)).isCompact_biUnion fun k hk => hpieceCompact k

/-- The trace pairing on square matrices. -/
def tracePairing {n : ℕ} :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun A :=
    { toFun := fun B => Matrix.trace (A * B)
      map_add' := by
        intro B₁ B₂
        simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        intro r B
        simp }
  map_add' := by
    intro A₁ A₂
    ext B
    simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' := by
    intro r A
    ext B
    simp

/-- Every continuous linear functional on the matrix space is represented by trace against a matrix.
-/
lemma strongDual_matrix_eq_trace_mul {n : ℕ}
    (f : StrongDual ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, ∀ X, f X = Matrix.trace (A * X) := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => f (Matrix.single j i 1)
  refine ⟨A, ?_⟩
  intro X
  -- Expand `X` in the standard matrix basis and read off the coefficients through trace.
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  calc
    f (∑ i : Fin n, ∑ j : Fin n, Matrix.single i j (X i j))
        = ∑ i : Fin n, ∑ j : Fin n, f (Matrix.single i j (X i j)) := by
      simp
    _ = ∑ i : Fin n, ∑ j : Fin n, X i j * f (Matrix.single i j 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsingle : Matrix.single i j (X i j) = (X i j) • Matrix.single i j (1 : ℝ) := by
        ext a b
        by_cases ha : a = i <;> by_cases hb : b = j <;> simp [Matrix.single, ha, hb]
      rw [hsingle, map_smul, smul_eq_mul]
    _ = ∑ i : Fin n, ∑ j : Fin n, Matrix.trace (A * Matrix.single i j (X i j)) := by
      simp [A, Matrix.trace_mul_single, mul_comm]
    _ = Matrix.trace (A * ∑ i : Fin n, ∑ j : Fin n, Matrix.single i j (X i j)) := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
      congr with i
      rw [Matrix.mul_sum, Matrix.trace_sum]
    _ = Matrix.trace (A * X) := by
      exact congrArg (fun M => Matrix.trace (A * M)) (Matrix.matrix_eq_sum_single X).symm

/-- The trace pairing is a continuous perfect pairing on the matrix space. -/
instance tracePairing_isContPerfPair {n : ℕ} : (tracePairing (n := n)).IsContPerfPair where
  continuous_uncurry := by
    -- The matrix multiplication and trace maps are continuous.
    change Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ =>
      Matrix.trace (p.1 * p.2))
    fun_prop
  bijective_left := by
    constructor
    · intro A B hAB
      apply (Matrix.ext_iff_trace_mul_right).2
      intro X
      exact DFunLike.congr_fun hAB X
    · intro f
      rcases strongDual_matrix_eq_trace_mul f with ⟨A, hA⟩
      refine ⟨A, ?_⟩
      ext X
      simpa [tracePairing] using (hA X).symm
  bijective_right := by
    constructor
    · intro A B hAB
      apply (Matrix.ext_iff_trace_mul_left).2
      intro X
      exact DFunLike.congr_fun hAB X
    · intro f
      rcases strongDual_matrix_eq_trace_mul f with ⟨A, hA⟩
      refine ⟨A, ?_⟩
      ext X
      change Matrix.trace (X * A) = f X
      rw [Matrix.trace_mul_comm]
      exact (hA X).symm

/-- The symmetric part of a real matrix. -/
def matrixSymmPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((1 / 2 : ℝ) • (A + Aᵀ))

/-- The symmetric part is symmetric. -/
lemma matrixSymmPart_isSymm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (matrixSymmPart A).IsSymm := by
  -- Transposing the symmetric part leaves it unchanged.
  ext i j
  simp [matrixSymmPart, add_comm]
  ring

/-- A symmetric matrix is unchanged by taking the symmetric part. -/
lemma matrixSymmPart_eq_self_of_isSymm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsSymm) :
    matrixSymmPart A = A := by
  -- Replace the transpose by the original matrix and simplify the scalar factor.
  rw [Matrix.IsSymm] at hA
  ext i j
  simp [matrixSymmPart, hA]
  ring

/-- Pairing a symmetric matrix on the left is unchanged by replacing the right factor by its
  symmetric part. -/
lemma trace_mul_matrixSymmPart_eq_of_isSymm_left {n : ℕ}
    {Y X : Matrix (Fin n) (Fin n) ℝ} (hY : Y.IsSymm) :
    Matrix.trace (Y * matrixSymmPart X) = Matrix.trace (Y * X) := by
  -- Route correction: the reverse-inclusion proof only needs to compare against symmetric test
  -- matrices, so we symmetrize the nonsymmetric factor and use trace-transpose identities.
  have hYt : Yᵀ = Y := by simpa [Matrix.IsSymm] using hY
  have htranspose : Matrix.trace (Y * Xᵀ) = Matrix.trace (Y * X) := by
    calc
      Matrix.trace (Y * Xᵀ) = Matrix.trace ((Y * Xᵀ)ᵀ) := by rw [Matrix.trace_transpose]
      _ = Matrix.trace (X * Yᵀ) := by simp [Matrix.transpose_mul]
      _ = Matrix.trace (X * Y) := by simpa [hYt]
      _ = Matrix.trace (Y * X) := by rw [Matrix.trace_mul_comm]
  calc
    Matrix.trace (Y * matrixSymmPart X)
        = (1 / 2 : ℝ) * (Matrix.trace (Y * X) + Matrix.trace (Y * Xᵀ)) := by
          simp [matrixSymmPart, Matrix.trace_add, mul_add]
    _ = (1 / 2 : ℝ) * (Matrix.trace (Y * X) + Matrix.trace (Y * X)) := by rw [htranspose]
    _ = Matrix.trace (Y * X) := by ring

/-- The normalized nonnegative rank-one base is nonempty in positive dimension. -/
lemma normalizedNonnegativeRankOneBase_nonempty (m : ℕ) :
    Set.Nonempty (normalizedNonnegativeRankOneBase (m + 1)) := by
  let z : Fin (m + 1) → ℝ := Pi.single 0 1
  refine ⟨Matrix.vecMulVec z z, z, ?_, ?_, rfl⟩
  · -- The coordinate vector `e₀` is coordinatewise nonnegative.
    intro i
    by_cases hi : i = 0
    · simp [z, hi]
    · simp [z, hi]
  · -- Its squared norm is `1`, so it lies on the normalized trace-one slice.
    rw [dotProduct, Finset.sum_eq_single 0]
    · simp [z]
    · intro i hi
      simp [z, Pi.single_apply]
    · intro h
      exact (h (Finset.mem_univ 0)).elim

/-- In positive dimension, the convex hull of nonnegative rank-one generators is exactly the cone
over the compact normalized trace-one base. -/
lemma convexHull_rankOne_nonneg_eq_nonneg_smul_normalizedHull (m : ℕ) :
    convexHull ℝ {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ |
      ∃ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) ∧ Y = Matrix.vecMulVec z z} =
      {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ |
        ∃ t : ℝ, 0 ≤ t ∧
          ∃ Z ∈ convexHull ℝ (normalizedNonnegativeRankOneBase (m + 1)), Y = t • Z} := by
  let S : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :=
    {Y | ∃ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) ∧ Y = Matrix.vecMulVec z z}
  let B : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :=
    convexHull ℝ (normalizedNonnegativeRankOneBase (m + 1))
  have hBnonempty : Set.Nonempty B := by
    rcases normalizedNonnegativeRankOneBase_nonempty m with ⟨Z, hZ⟩
    exact ⟨Z, subset_convexHull ℝ _ hZ⟩
  have hTconvex :
      Convex ℝ {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ |
        ∃ t : ℝ, 0 ≤ t ∧ ∃ Z ∈ B, Y = t • Z} := by
    intro Y₁ hY₁ Y₂ hY₂ a b ha hb hab
    rcases hY₁ with ⟨t₁, ht₁, Z₁, hZ₁, rfl⟩
    rcases hY₂ with ⟨t₂, ht₂, Z₂, hZ₂, rfl⟩
    let t : ℝ := a * t₁ + b * t₂
    have ht : 0 ≤ t := add_nonneg (mul_nonneg ha ht₁) (mul_nonneg hb ht₂)
    by_cases htzero : t = 0
    · -- If the total scalar vanishes, the convex combination is the zero matrix.
      rcases hBnonempty with ⟨Z₀, hZ₀⟩
      refine ⟨0, le_rfl, Z₀, hZ₀, ?_⟩
      have hat₁ : a * t₁ = 0 := by
        have hbt₂ : 0 ≤ b * t₂ := mul_nonneg hb ht₂
        nlinarith
      have hbt₂ : b * t₂ = 0 := by
        have hat₁' : 0 ≤ a * t₁ := mul_nonneg ha ht₁
        nlinarith
      simpa [smul_smul, hat₁, hbt₂]
    · -- Otherwise divide by the total scalar to obtain a convex combination inside `B`.
      have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
      have ha' : 0 ≤ a * t₁ / t := div_nonneg (mul_nonneg ha ht₁) ht
      have hb' : 0 ≤ b * t₂ / t := div_nonneg (mul_nonneg hb ht₂) ht
      have hsum : a * t₁ / t + b * t₂ / t = 1 := by
        field_simp [t, htzero]
        ring
      refine ⟨t, ht, ((a * t₁ / t) • Z₁ + (b * t₂ / t) • Z₂), ?_, ?_⟩
      · -- The normalized slice is convex, so the rescaled barycenter stays in `B`.
        exact convex_convexHull ℝ _ hZ₁ hZ₂ ha' hb' hsum
      · -- Expanding the scalar arithmetic recovers the original convex combination.
        have ht_ne : t ≠ 0 := htzero
        have hfac₁ : a * t₁ = t * (a * t₁ / t) := by
          field_simp [t, ht_ne]
        have hfac₂ : b * t₂ = t * (b * t₂ / t) := by
          field_simp [t, ht_ne]
        have hleft₁ : (a * t₁) • Z₁ = (t * (a * t₁ / t)) • Z₁ :=
          congrArg (fun r : ℝ => r • Z₁) hfac₁
        have hleft₂ : (b * t₂) • Z₂ = (t * (b * t₂ / t)) • Z₂ :=
          congrArg (fun r : ℝ => r • Z₂) hfac₂
        calc
          a • (t₁ • Z₁) + b • (t₂ • Z₂)
              = (a * t₁) • Z₁ + (b * t₂) • Z₂ := by simp [smul_smul]
          _ = (t * (a * t₁ / t)) • Z₁ + (t * (b * t₂ / t)) • Z₂ := by
            rw [hleft₁, hleft₂]
          _ = t • (((a * t₁ / t) • Z₁) + ((b * t₂ / t) • Z₂)) := by
            simpa only [smul_add, smul_smul]
  have hsubsetT :
      S ⊆ {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ |
        ∃ t : ℝ, 0 ≤ t ∧ ∃ Z ∈ B, Y = t • Z} := by
    intro Y hY
    rcases hY with ⟨z, hz, rfl⟩
    let t : ℝ := dotProduct z z
    have ht : 0 ≤ t := by
      dsimp [t]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (hz i)
    by_cases htzero : t = 0
    · -- Zero generators reduce to the origin, which lies in the cone over any base point.
      rcases hBnonempty with ⟨Z₀, hZ₀⟩
      have hzzero : z = 0 := dotProduct_self_eq_zero.mp htzero
      refine ⟨0, le_rfl, Z₀, hZ₀, ?_⟩
      simp [hzzero]
    · -- Nonzero generators can be normalized to trace `1`.
      have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
      let u : Fin (m + 1) → ℝ := (Real.sqrt t)⁻¹ • z
      have hu_nonneg : ∀ i, 0 ≤ u i := by
        intro i
        have hsqrt_nonneg : 0 ≤ (Real.sqrt t)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg t)
        simpa [u, smul_eq_mul] using mul_nonneg hsqrt_nonneg (hz i)
      have hu_norm : dotProduct u u = 1 := by
        dsimp [u]
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        have hsqrt : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.2 htp
        field_simp [hsqrt]
        nlinarith [Real.sq_sqrt ht]
      have hzrepr : z = Real.sqrt t • u := by
        have hsqrt : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.2 htp
        ext i
        simp [u, hsqrt]
      refine ⟨t, ht, Matrix.vecMulVec u u, subset_convexHull ℝ _ ⟨u, hu_nonneg, hu_norm, rfl⟩, ?_⟩
      calc
        Matrix.vecMulVec z z
            = Matrix.vecMulVec (Real.sqrt t • u) (Real.sqrt t • u) := by rw [hzrepr]
        _ = t • Matrix.vecMulVec u u := by
          rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
          have hsq : Real.sqrt t * Real.sqrt t = t := by nlinarith [Real.sq_sqrt ht]
          simp [hsq]
  apply le_antisymm
  · -- The hull is included in the conical model because the latter is convex and contains
    -- every generator.
    refine convexHull_min hsubsetT hTconvex
  · have hconeHull :
        ∀ {c : ℝ}, 0 ≤ c →
          c • convexHull ℝ S ⊆ convexHull ℝ S := by
        intro c hc
        -- Scaling preserves the hull because the generator set is itself closed under
        -- nonnegative scaling.
        rw [← convexHull_smul]
        refine convexHull_min ?_ (convex_convexHull ℝ S)
        rintro Y ⟨X, hX, rfl⟩
        rcases hX with ⟨z, hz, rfl⟩
        refine subset_convexHull ℝ S ?_
        refine ⟨Real.sqrt c • z, ?_, ?_⟩
        · intro i
          exact mul_nonneg (Real.sqrt_nonneg c) (hz i)
        · rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
          have hsq : Real.sqrt c * Real.sqrt c = c := by nlinarith [Real.sq_sqrt hc]
          simp [hsq]
    · intro Y hY
      rcases hY with ⟨t, ht, Z, hZB, rfl⟩
      have hZ : Z ∈ convexHull ℝ S := by
        refine convexHull_min ?_ (convex_convexHull ℝ S) hZB
        rintro _ ⟨z, hz, hnorm, rfl⟩
        exact subset_convexHull ℝ S ⟨z, hz, rfl⟩
      have hsmulZ : t • Z ∈ t • convexHull ℝ S := ⟨Z, hZ, rfl⟩
      exact hconeHull ht hsmulZ

/-- In positive dimension, the completely positive cone generated by nonnegative rank-one matrices
is closed. -/
lemma convexHull_rankOne_nonneg_isClosed (m : ℕ) :
    IsClosed
      (convexHull ℝ {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ |
        ∃ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) ∧ Y = Matrix.vecMulVec z z}) := by
  let B : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :=
    convexHull ℝ (normalizedNonnegativeRankOneBase (m + 1))
  let T : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :=
    {Y | ∃ t : ℝ, 0 ≤ t ∧ ∃ Z ∈ B, Y = t • Z}
  have hcompactB : IsCompact B := convexHull_normalizedNonnegativeRankOneBase_compact (n := m + 1)
  have htraceB : B ⊆ {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ | Matrix.trace Y = 1} :=
    convexHull_normalizedNonnegativeRankOneBase_subset_trace_eq_one (n := m + 1)
  have hTclosed : IsClosed T := by
    rw [← isSeqClosed_iff_isClosed]
    intro x p hx hp
    classical
    choose t ht Z hZ hEq using hx
    obtain ⟨W, hW, φ, hφmono, hWφ⟩ := hcompactB.tendsto_subseq hZ
    have hxφ : Filter.Tendsto (x ∘ φ) atTop (𝓝 p) := hp.comp hφmono.tendsto_atTop
    -- Tracing the subsequence recovers the scaling parameters.
    have htraceφ :
        Filter.Tendsto (fun n => Matrix.trace (x (φ n))) atTop (𝓝 (Matrix.trace p)) := by
      simpa [Function.comp] using
        (Filter.Tendsto.comp ((Continuous.matrix_trace continuous_id).tendsto p) hxφ)
    have htrace_nonneg : 0 ≤ Matrix.trace p := by
      refine ge_of_tendsto' htraceφ fun n => ?_
      have htraceW : Matrix.trace (Z (φ n)) = 1 := htraceB (hZ (φ n))
      have htraceEq : Matrix.trace (x (φ n)) = t (φ n) := by
        have htrace := congrArg Matrix.trace (hEq (φ n))
        simpa [Matrix.trace_smul, htraceW] using htrace
      simpa [htraceEq] using ht (φ n)
    have hsame :
        Filter.Tendsto
          (fun n => Matrix.trace (x (φ n)) • Z (φ n))
          atTop (𝓝 (Matrix.trace p • W)) := htraceφ.smul hWφ
    have hxφ_eq :
        (fun n => x (φ n)) = fun n => Matrix.trace (x (φ n)) • Z (φ n) := by
      funext n
      have htraceW : Matrix.trace (Z (φ n)) = 1 := htraceB (hZ (φ n))
      have htraceEq : Matrix.trace (x (φ n)) = t (φ n) := by
        have htrace := congrArg Matrix.trace (hEq (φ n))
        simpa [Matrix.trace_smul, htraceW] using htrace
      calc
        x (φ n) = t (φ n) • Z (φ n) := hEq (φ n)
        _ = Matrix.trace (x (φ n)) • Z (φ n) := by rw [htraceEq]
    have hsame' : Filter.Tendsto (x ∘ φ) atTop (𝓝 (Matrix.trace p • W)) := by
      change Filter.Tendsto (fun n => x (φ n)) atTop (𝓝 (Matrix.trace p • W))
      rw [hxφ_eq]
      exact hsame
    have hp_eq : p = Matrix.trace p • W := tendsto_nhds_unique hxφ hsame'
    exact ⟨Matrix.trace p, htrace_nonneg, W, hW, hp_eq⟩
  rw [convexHull_rankOne_nonneg_eq_nonneg_smul_normalizedHull m]
  exact hTclosed

/-- Membership in the trace-dual of the completely positive cone is exactly copositivity on
nonnegative vectors. -/
lemma mem_traceDual_convexHull_rankOne_nonneg_iff {n : ℕ}
    (CP : ProperCone ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hCP :
      (CP : Set (Matrix (Fin n) (Fin n) ℝ)) =
        convexHull ℝ {Y : Matrix (Fin n) (Fin n) ℝ |
          ∃ z : Fin n → ℝ, (∀ i, 0 ≤ z i) ∧ Y = Matrix.vecMulVec z z})
    (X : Matrix (Fin n) (Fin n) ℝ) :
    X ∈ ProperCone.dual (tracePairing (n := n)).flip (CP : Set _) ↔
      ∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) → 0 ≤ dotProduct z (X.mulVec z) := by
  constructor
  · intro hX z hz
    -- Test the dual inequality on a single rank-one generator.
    have hmem :
        Matrix.vecMulVec z z ∈ (CP : Set (Matrix (Fin n) (Fin n) ℝ)) := by
      rw [hCP]
      exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩
    have htrace : 0 ≤ Matrix.trace (X * Matrix.vecMulVec z z) := hX hmem
    rw [Matrix.trace_mul_comm, trace_vecMulVec_mul_eq_dotProduct] at htrace
    exact htrace
  · intro hcop
    rw [ProperCone.mem_dual]
    intro Y hY
    let H : Set (Matrix (Fin n) (Fin n) ℝ) := {A | 0 ≤ Matrix.trace (A * X)}
    have hconvH : Convex ℝ H := by
      intro A hA B hB a b ha hb hab
      -- The trace halfspace is convex because the trace pairing is linear in its left input.
      change 0 ≤ Matrix.trace ((a • A + b • B) * X)
      calc
        0 ≤ a * Matrix.trace (A * X) + b * Matrix.trace (B * X) :=
          add_nonneg (mul_nonneg ha hA) (mul_nonneg hb hB)
        _ = Matrix.trace ((a • A + b • B) * X) := by
          simp [Matrix.add_mul]
    have hsubH :
        {Y : Matrix (Fin n) (Fin n) ℝ |
          ∃ z : Fin n → ℝ, (∀ i, 0 ≤ z i) ∧ Y = Matrix.vecMulVec z z} ⊆ H := by
      rintro _ ⟨z, hz, rfl⟩
      -- On a generator, the trace inequality is exactly the copositive quadratic form.
      change 0 ≤ Matrix.trace (Matrix.vecMulVec z z * X)
      simpa [trace_vecMulVec_mul_eq_dotProduct] using hcop z hz
    have hYH : Y ∈ H := by
      rw [hCP] at hY
      exact convexHull_min hsubH hconvH hY
    have hYX : 0 ≤ Matrix.trace (Y * X) := hYH
    change 0 ≤ Matrix.trace (X * Y)
    rw [Matrix.trace_mul_comm]
    exact hYX

/-- Symmetrizing a trace-dual witness produces a symmetric copositive matrix. -/
lemma matrixSymmPart_mem_copositive_of_mem_traceDual {n : ℕ}
    (CP : ProperCone ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hCP :
      (CP : Set (Matrix (Fin n) (Fin n) ℝ)) =
        convexHull ℝ {Y : Matrix (Fin n) (Fin n) ℝ |
          ∃ z : Fin n → ℝ, (∀ i, 0 ≤ z i) ∧ Y = Matrix.vecMulVec z z})
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ ProperCone.dual (tracePairing (n := n)).flip (CP : Set _)) :
    matrixSymmPart X ∈
      {A : Matrix (Fin n) (Fin n) ℝ |
        A.IsSymm ∧
          ∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) → 0 ≤ dotProduct z (A.mulVec z)} := by
  constructor
  · -- By construction, the symmetric part is symmetric.
    exact matrixSymmPart_isSymm X
  · intro z hz
    have hcop := (mem_traceDual_convexHull_rankOne_nonneg_iff CP hCP X).1 hX z hz
    have htraceEq :
        Matrix.trace (Matrix.vecMulVec z z * matrixSymmPart X) =
          Matrix.trace (Matrix.vecMulVec z z * X) := by
      exact trace_mul_matrixSymmPart_eq_of_isSymm_left (by simp [Matrix.IsSymm])
    -- The quadratic form only depends on the symmetric part of the matrix.
    rw [← trace_vecMulVec_mul_eq_dotProduct (X := matrixSymmPart X) (z := z),
      htraceEq, trace_vecMulVec_mul_eq_dotProduct (X := X) (z := z)]
    exact hcop

theorem copositive_dual_cone_eq_convex_hull_rankOne_nonneg {n : ℕ} :
    let C : Set (Matrix (Fin n) (Fin n) ℝ) :=
      {X | X.IsSymm ∧ ∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) → 0 ≤ dotProduct z (X.mulVec z)}
    let dualC : Set (Matrix (Fin n) (Fin n) ℝ) :=
      {Y | Y.IsSymm ∧ ∀ X ∈ C, 0 ≤ Matrix.trace (Y * X)}
    dualC =
      convexHull ℝ {Y | ∃ z : Fin n → ℝ, (∀ i, 0 ≤ z i) ∧ Y = Matrix.vecMulVec z z} := by
  -- Route correction: the reverse inclusion is handled by bundling the completely positive cone
  -- as a closed cone and then using a trace-pairing double-dual argument after symmetrization.
  dsimp
  refine Set.Subset.antisymm ?_ convexHull_rankOne_nonneg_subset_copositiveDualCone
  intro Y hY
  have hYsymm : Y.IsSymm := hY.1
  by_cases hn : n = 0
  · -- In dimension `0`, both sides are the singleton cone `{0}`.
    subst hn
    have hzero : Y = 0 := Subsingleton.elim _ _
    have hmem :
        (0 : Matrix (Fin 0) (Fin 0) ℝ) ∈
          convexHull ℝ {A : Matrix (Fin 0) (Fin 0) ℝ |
            ∃ z : Fin 0 → ℝ, (∀ i, 0 ≤ z i) ∧ A = Matrix.vecMulVec z z} := by
      refine subset_convexHull ℝ _ ?_
      refine ⟨0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · ext i
        exact Fin.elim0 i
    simpa [hzero] using hmem
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    let T : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :=
      {A | ∃ t : ℝ, 0 ≤ t ∧
        ∃ Z ∈ convexHull ℝ (normalizedNonnegativeRankOneBase (m + 1)), A = t • Z}
    have hKeq :
        convexHull ℝ {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ |
          ∃ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) ∧ A = Matrix.vecMulVec z z} = T :=
      convexHull_rankOne_nonneg_eq_nonneg_smul_normalizedHull m
    have hTclosed : IsClosed T := by
      rw [← hKeq]
      exact convexHull_rankOne_nonneg_isClosed m
    let CPcone : PointedCone ℝ (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :=
      PointedCone.ofConeComb T
        ⟨0, ⟨0, le_rfl, by
          rcases normalizedNonnegativeRankOneBase_nonempty m with ⟨Z, hZ⟩
          exact ⟨Z, subset_convexHull ℝ _ hZ, by simp⟩⟩⟩
        (fun A hA B hB a ha b hb => by
          rcases hA with ⟨t₁, ht₁, Z₁, hZ₁, rfl⟩
          rcases hB with ⟨t₂, ht₂, Z₂, hZ₂, rfl⟩
          let t : ℝ := a * t₁ + b * t₂
          have ht : 0 ≤ t := add_nonneg (mul_nonneg ha ht₁) (mul_nonneg hb ht₂)
          by_cases htzero : t = 0
          · rcases normalizedNonnegativeRankOneBase_nonempty m with ⟨Z₀, hZ₀⟩
            refine ⟨0, le_rfl, Z₀, subset_convexHull ℝ _ hZ₀, ?_⟩
            have hat₁ : a * t₁ = 0 := by
              have hbt₂ : 0 ≤ b * t₂ := mul_nonneg hb ht₂
              nlinarith
            have hbt₂ : b * t₂ = 0 := by
              have hat₁' : 0 ≤ a * t₁ := mul_nonneg ha ht₁
              nlinarith
            simpa [smul_smul, hat₁, hbt₂]
          · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
            have ha' : 0 ≤ a * t₁ / t := div_nonneg (mul_nonneg ha ht₁) ht
            have hb' : 0 ≤ b * t₂ / t := div_nonneg (mul_nonneg hb ht₂) ht
            have hsum : a * t₁ / t + b * t₂ / t = 1 := by
              field_simp [t, htzero]
              ring
            refine ⟨t, ht, ((a * t₁ / t) • Z₁ + (b * t₂ / t) • Z₂), ?_, ?_⟩
            · exact convex_convexHull ℝ _ hZ₁ hZ₂ ha' hb' hsum
            · have ht_ne : t ≠ 0 := htzero
              have hfac₁ : a * t₁ = t * (a * t₁ / t) := by
                field_simp [t, ht_ne]
              have hfac₂ : b * t₂ = t * (b * t₂ / t) := by
                field_simp [t, ht_ne]
              have hleft₁ : (a * t₁) • Z₁ = (t * (a * t₁ / t)) • Z₁ :=
                congrArg (fun r : ℝ => r • Z₁) hfac₁
              have hleft₂ : (b * t₂) • Z₂ = (t * (b * t₂ / t)) • Z₂ :=
                congrArg (fun r : ℝ => r • Z₂) hfac₂
              calc
                a • (t₁ • Z₁) + b • (t₂ • Z₂)
                    = (a * t₁) • Z₁ + (b * t₂) • Z₂ := by simp [smul_smul]
                _ = (t * (a * t₁ / t)) • Z₁ + (t * (b * t₂ / t)) • Z₂ := by
                  rw [hleft₁, hleft₂]
                _ = t • (((a * t₁ / t) • Z₁) + ((b * t₂ / t) • Z₂)) := by
                  simpa only [smul_add, smul_smul])
    let CP : ProperCone ℝ (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :=
      { toSubmodule := CPcone
        isClosed' := hTclosed }
    have hCP :
        (CP : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) =
          convexHull ℝ {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ |
            ∃ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) ∧ A = Matrix.vecMulVec z z} := by
      exact hKeq.symm
    have hYdd :
        Y ∈ ProperCone.dual (tracePairing (n := m + 1))
          (ProperCone.dual (tracePairing (n := m + 1)).flip (CP : Set _)) := by
      rw [ProperCone.mem_dual]
      intro X hX
      have hXcopo : matrixSymmPart X ∈
          {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ |
            A.IsSymm ∧
              ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → 0 ≤ dotProduct z (A.mulVec z)} :=
        matrixSymmPart_mem_copositive_of_mem_traceDual CP hCP hX
      have htrace : 0 ≤ Matrix.trace (Y * matrixSymmPart X) := hY.2 _ hXcopo
      -- The symmetric hypothesis on `Y` lets us replace `matrixSymmPart X` by `X`.
      have hYX : 0 ≤ Matrix.trace (Y * X) := by
        simpa [trace_mul_matrixSymmPart_eq_of_isSymm_left hYsymm] using htrace
      change 0 ≤ Matrix.trace (X * Y)
      rw [Matrix.trace_mul_comm]
      exact hYX
    have hYCP : Y ∈ CP := by
      have hdualEq :
          ProperCone.dual (tracePairing (n := m + 1))
            (ProperCone.dual (tracePairing (n := m + 1)).flip (CP : Set _)) = CP :=
        ProperCone.dual_flip_dual (p := (tracePairing (n := m + 1)).flip) CP
      rw [hdualEq] at hYdd
      exact hYdd
    have hYCPset : Y ∈ (CP : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) := hYCP
    rw [hCP] at hYCPset
    exact hYCPset

end «problem-21»
