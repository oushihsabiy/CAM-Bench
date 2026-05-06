import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open Module
open scoped BigOperators

namespace «problem-153»

def conicHull {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℝ)) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | ∀ C : Set (Matrix (Fin n) (Fin n) ℝ),
    S ⊆ C →
    (0 : Matrix (Fin n) (Fin n) ℝ) ∈ C →
    (∀ X Y : Matrix (Fin n) (Fin n) ℝ, X ∈ C → Y ∈ C → X + Y ∈ C) →
    (∀ X : Matrix (Fin n) (Fin n) ℝ, ∀ t : ℝ, 0 ≤ t → X ∈ C → t • X ∈ C) →
    A ∈ C}

/-- Every generating element belongs to its conic hull. -/
lemma subset_conicHull {n : ℕ} {S : Set (Matrix (Fin n) (Fin n) ℝ)}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ S) :
    A ∈ conicHull S := by
  -- The defining universal property lets us push generators into any test cone.
  intro C hSC h0 hAdd hSmul
  exact hSC hA

/-- Zero belongs to every conic hull. -/
lemma zero_mem_conicHull {n : ℕ} {S : Set (Matrix (Fin n) (Fin n) ℝ)} :
    (0 : Matrix (Fin n) (Fin n) ℝ) ∈ conicHull S := by
  -- Every test cone in the definition already contains zero.
  intro C hSC h0 hAdd hSmul
  exact h0

/-- Conic hulls are closed under addition. -/
lemma add_mem_conicHull {n : ℕ} {S : Set (Matrix (Fin n) (Fin n) ℝ)}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ conicHull S) (hB : B ∈ conicHull S) :
    A + B ∈ conicHull S := by
  -- We evaluate both membership proofs in the same ambient cone and then use its add-closure.
  intro C hSC h0 hAdd hSmul
  exact hAdd A B (hA C hSC h0 hAdd hSmul) (hB C hSC h0 hAdd hSmul)

/-- Conic hulls are closed under nonnegative scalar multiplication. -/
lemma smul_mem_conicHull {n : ℕ} {S : Set (Matrix (Fin n) (Fin n) ℝ)}
    {A : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (ht : 0 ≤ t) (hA : A ∈ conicHull S) :
    t • A ∈ conicHull S := by
  -- We reuse the scalar-closure of each test cone from the definition.
  intro C hSC h0 hAdd hSmul
  exact hSmul A t ht (hA C hSC h0 hAdd hSmul)

/-- Finite sums of conic-hull elements remain in the conic hull. -/
lemma sum_mem_conicHull {n : ℕ} {S : Set (Matrix (Fin n) (Fin n) ℝ)}
    {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℝ)
    (hf : ∀ i ∈ s, f i ∈ conicHull S) :
    s.sum f ∈ conicHull S := by
  -- We induct over the finite index set, using zero and add closure at each step.
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro hf
    simpa using (zero_mem_conicHull (S := S))
  · intro a s ha hs hf
    rw [Finset.sum_insert ha]
    apply add_mem_conicHull
    · exact hf a (by simp)
    · apply hs
      intro i hi
      exact hf i (by simp [hi])

/-- The cone rank condition is monotone under adding a positive semidefinite matrix. -/
lemma rank_le_rank_add_of_posSemidef (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Matrix.rank A ≤ Matrix.rank (A + B) := by
  set_option maxHeartbeats 800000 in
  -- Route correction: instead of searching for a dedicated rank monotonicity lemma,
  -- prove kernel inclusion `ker (A + B) ⊆ ker A` and convert it with rank-nullity.
  have hker : LinearMap.ker (A + B).mulVecLin ≤ LinearMap.ker A.mulVecLin := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hsum' : star x ⬝ᵥ (A *ᵥ x) + star x ⬝ᵥ (B *ᵥ x) = 0 := by
      simpa [Matrix.add_mulVec, dotProduct_add] using congrArg (fun y => star x ⬝ᵥ y) hx
    have hA_nonneg : 0 ≤ star x ⬝ᵥ (A *ᵥ x) := hA.dotProduct_mulVec_nonneg x
    have hB_nonneg : 0 ≤ star x ⬝ᵥ (B *ᵥ x) := hB.dotProduct_mulVec_nonneg x
    have hAx : star x ⬝ᵥ (A *ᵥ x) = 0 := by
      linarith
    exact (hA.dotProduct_mulVec_zero_iff x).1 hAx
  have hker_le :
      finrank ℝ (LinearMap.ker (A + B).mulVecLin) ≤
        finrank ℝ (LinearMap.ker A.mulVecLin) :=
    Submodule.finrank_mono hker
  have hnullA : Matrix.rank A + finrank ℝ (LinearMap.ker A.mulVecLin) = n := by
    simpa [Matrix.rank] using LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hnullAB : Matrix.rank (A + B) + finrank ℝ (LinearMap.ker (A + B).mulVecLin) = n := by
    simpa [Matrix.rank] using LinearMap.finrank_range_add_finrank_ker (A + B).mulVecLin
  omega

/-- The target cone on the right-hand side contains every rank-`k` Gram generator. -/
lemma gram_generator_mem_targetCone (n k : ℕ) {X : Matrix (Fin n) (Fin k) ℝ}
    (hX : Matrix.rank X = k) :
    X * X.transpose ∈
      ({A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef ∧ k ≤ Matrix.rank A} ∪ ({0} : Set _)) := by
  -- Each generator is positive semidefinite, and its rank is exactly the rank of `X`.
  left
  constructor
  · simpa using Matrix.posSemidef_self_mul_conjTranspose X
  · simp [Matrix.rank_self_mul_transpose, hX]

/-- The subtype of indices carrying nonzero eigenvalues of a Hermitian matrix. -/
abbrev NonzeroEigenIndex {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :=
  {i : Fin n // hA.eigenvalues i ≠ 0}

/-- The selector matrix that embeds the nonzero-eigenvalue subtype into the ambient coordinate
space. -/
def supportSelectorMatrix {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    Matrix (Fin n) (NonzeroEigenIndex hA) ℝ :=
  fun i a => if i = a.1 then 1 else 0

/-- The diagonal `k`-column matrix attached to a `k`-subset of the nonzero spectral support. -/
def supportSubsetColumnMatrix {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (t : Finset (NonzeroEigenIndex hA)) (ht : t.card = k) :
    Matrix (NonzeroEigenIndex hA) (Fin k) ℝ :=
  fun a j => if a = t.orderEmbOfFin ht j then Real.sqrt (hA.eigenvalues a.1) else 0

/-- Each support index belongs to exactly the expected number of `k`-subsets of a finite type. -/
lemma powersetCard_contains_index_count {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (hk : 1 ≤ k) (a : α) :
    ((Finset.univ.powersetCard k).filter fun t => a ∈ t).card =
      Nat.choose (Fintype.card α - 1) (k - 1) := by
  -- Split `k`-subsets of `univ` according to whether they contain the distinguished element `a`.
  have hsplit :=
    Finset.powersetCard_succ_insert (x := a) (s := Finset.univ.erase a) (by simp) (k - 1)
  have hsplit' :
      Finset.univ.powersetCard k =
        (Finset.univ.erase a).powersetCard k ∪
          ((Finset.univ.erase a).powersetCard (k - 1)).image (insert a) := by
    rw [← Nat.succ_pred_eq_of_pos hk]
    simpa [Finset.insert_erase (Finset.mem_univ a)] using hsplit
  rw [hsplit', Finset.filter_union]
  have hleft :
      (((Finset.univ.erase a).powersetCard k).filter fun t => a ∈ t) = ∅ := by
    -- A subset of `erase a` cannot contain `a`.
    ext t
    constructor
    · intro ht
      rw [Finset.mem_filter] at ht
      have : a ∈ Finset.univ.erase a := (Finset.mem_powersetCard.mp ht.1).1 ht.2
      simpa using this
    · intro ht
      simpa using ht
  have hright :
      ((((Finset.univ.erase a).powersetCard (k - 1)).image (insert a)).filter
        fun t => a ∈ t) =
        ((Finset.univ.erase a).powersetCard (k - 1)).image (insert a) := by
    -- Every set in the image contains `a` by construction.
    ext t
    constructor
    · intro ht
      exact (Finset.mem_filter.mp ht).1
    · intro ht
      refine Finset.mem_filter.mpr ⟨ht, ?_⟩
      rcases Finset.mem_image.mp ht with ⟨u, hu, rfl⟩
      simp
  have hinj :
      Set.InjOn (insert a) ((Finset.univ.erase a).powersetCard (k - 1) : Set (Finset α)) := by
    intro s hs t ht hst
    have hs' : a ∉ s := by
      intro hsa
      have : a ∈ Finset.univ.erase a := (Finset.mem_powersetCard.mp hs).1 hsa
      simpa using this
    have ht' : a ∉ t := by
      intro hta
      have : a ∈ Finset.univ.erase a := (Finset.mem_powersetCard.mp ht).1 hta
      simpa using this
    simpa [Finset.erase_insert, hs', ht'] using congrArg (fun u => u.erase a) hst
  have himage :
      (((Finset.univ.erase a).powersetCard (k - 1)).image (insert a)).card =
        ((Finset.univ.erase a).powersetCard (k - 1)).card := by
    simpa using
      (Finset.card_image_of_injOn (s := (Finset.univ.erase a).powersetCard (k - 1)) hinj)
  rw [hleft, Finset.empty_union, hright, himage]
  · simpa [Finset.card_erase_of_mem (Finset.mem_univ a)] using
      Finset.card_powersetCard (k - 1) (Finset.univ.erase a)

/-- The support selector is an isometric embedding of the nonzero spectral support. -/
lemma supportSelectorMatrix_transpose_mul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    (supportSelectorMatrix hA)ᵀ * supportSelectorMatrix hA = 1 := by
  classical
  -- Entrywise, the selector columns are distinct standard basis vectors.
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [supportSelectorMatrix, Matrix.mul_apply]
  · have hval : a.1 ≠ b.1 := by
      intro h
      apply hab
      exact Subtype.ext h
    have hval' : b.1 ≠ a.1 := hval.symm
    simp [supportSelectorMatrix, Matrix.mul_apply, hab, hval']

/-- The subset-column matrix has the expected diagonal Gram matrix on the selected columns. -/
lemma supportSubsetColumnMatrix_transpose_mul {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hpsd : A.PosSemidef)
    (t : Finset (NonzeroEigenIndex hA)) (ht : t.card = k) :
    (supportSubsetColumnMatrix hA t ht)ᵀ * supportSubsetColumnMatrix hA t ht =
      Matrix.diagonal (fun j : Fin k => hA.eigenvalues ((t.orderEmbOfFin ht j).1)) := by
  classical
  -- The columns are orthogonal, and each diagonal entry is the square of a chosen square root.
  ext i j
  by_cases hij : i = j
  · subst hij
    have hnonneg :
        0 ≤ hA.eigenvalues ((t.orderEmbOfFin ht i).1) := hpsd.eigenvalues_nonneg _
    rw [Matrix.diagonal_apply_eq, Matrix.mul_apply]
    simp [supportSubsetColumnMatrix]
    rw [← sq, Real.sq_sqrt hnonneg]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.mul_apply]
    have hji : ¬j = i := by simpa [eq_comm] using hij
    simp [supportSubsetColumnMatrix, hji]

/-- The subset-column matrix records exactly the chosen eigenvalues on the support subtype. -/
lemma supportSubsetColumnMatrix_mul_transpose {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hpsd : A.PosSemidef)
    (t : Finset (NonzeroEigenIndex hA)) (ht : t.card = k) :
    supportSubsetColumnMatrix hA t ht * (supportSubsetColumnMatrix hA t ht)ᵀ =
      Matrix.diagonal (fun a : NonzeroEigenIndex hA => if a ∈ t then hA.eigenvalues a.1 else 0) := by
  classical
  -- The rows are orthogonal, and a row is nonzero exactly when the corresponding support index
  -- belongs to the chosen subset.
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases ha : a ∈ t
    · rw [Matrix.mul_apply, Matrix.diagonal_apply_eq]
      have ha' : a ∈ Set.range (t.orderEmbOfFin ht) := by
        simpa [t.range_orderEmbOfFin ht] using ha
      rcases ha' with ⟨j, rfl⟩
      have hnonneg :
          0 ≤ hA.eigenvalues ((t.orderEmbOfFin ht j).1) := hpsd.eigenvalues_nonneg _
      simp [supportSubsetColumnMatrix, hnonneg]
    · rw [Matrix.mul_apply, Matrix.diagonal_apply_eq]
      have hnone : ∀ j : Fin k, a ≠ t.orderEmbOfFin ht j := by
        intro j hj
        apply ha
        simpa [hj] using t.orderEmbOfFin_mem ht j
      simp [supportSubsetColumnMatrix, hnone, ha]
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.mul_apply]
    refine Finset.sum_eq_zero ?_
    intro x hx
    by_cases hbx : b = t.orderEmbOfFin ht x
    · have hax : a ≠ t.orderEmbOfFin ht x := by
        intro hax
        apply hab
        exact hax.trans hbx.symm
      simp [supportSubsetColumnMatrix, hbx, hax]
    · simp [supportSubsetColumnMatrix, hbx]

/-- Pushing a diagonal matrix on the support subtype into ambient coordinates fills the same
entries on the nonzero spectral support and leaves the zero-eigenvalue coordinates at zero. -/
lemma supportSelectorMatrix_push_diagonal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (d : NonzeroEigenIndex hA → ℝ) :
    supportSelectorMatrix hA * Matrix.diagonal d * (supportSelectorMatrix hA)ᵀ =
      Matrix.diagonal (fun i : Fin n => if hi : hA.eigenvalues i ≠ 0 then d ⟨i, hi⟩ else 0) := by
  classical
  -- Entrywise, the selector either picks the unique support index over `i` or contributes zero.
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : hA.eigenvalues i ≠ 0
    · rw [Matrix.diagonal_apply_eq]
      have hentry :
          (supportSelectorMatrix hA * Matrix.diagonal d * (supportSelectorMatrix hA)ᵀ) i i =
            ∑ x : NonzeroEigenIndex hA, if i = ↑x then if i = ↑x then d x else 0 else 0 := by
        simp [Matrix.mul_apply, Matrix.diagonal, supportSelectorMatrix]
      rw [hentry]
      simpa [hi] using
        (calc
          (∑ x : NonzeroEigenIndex hA, if i = ↑x then if i = ↑x then d x else 0 else 0) =
              ∑ x : NonzeroEigenIndex hA, if x = ⟨i, hi⟩ then d x else 0 := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                by_cases hxi : x = ⟨i, hi⟩
                · subst hxi
                  simp
                · have hix : i ≠ x.1 := by
                    intro hix
                    apply hxi
                    exact Subtype.ext hix.symm
                  simp [hix, hxi]
          _ = d ⟨i, hi⟩ := by
            simp)
    · rw [Matrix.diagonal_apply_eq]
      have hentry :
          (supportSelectorMatrix hA * Matrix.diagonal d * (supportSelectorMatrix hA)ᵀ) i i =
            ∑ x : NonzeroEigenIndex hA, if i = ↑x then if i = ↑x then d x else 0 else 0 := by
        simp [Matrix.mul_apply, Matrix.diagonal, supportSelectorMatrix]
      rw [hentry]
      have hsum :
          (∑ x : NonzeroEigenIndex hA, if i = ↑x then if i = ↑x then d x else 0 else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hix : i ≠ x.1 := by
          intro hix
          apply hi
          simpa [hix] using x.2
        simp [hix]
      simpa [hi] using hsum
  · rw [Matrix.diagonal_apply_ne _ hij]
    have hentry :
        (supportSelectorMatrix hA * Matrix.diagonal d * (supportSelectorMatrix hA)ᵀ) i j =
          ∑ x : NonzeroEigenIndex hA, if j = ↑x then if i = ↑x then d x else 0 else 0 := by
      simp [Matrix.mul_apply, Matrix.diagonal, supportSelectorMatrix]
    rw [hentry]
    refine Finset.sum_eq_zero ?_
    intro x hx
    by_cases hjx : j = x.1
    · have hix : i ≠ x.1 := by
        intro hix
        apply hij
        exact hix.trans hjx.symm
      simp [hjx, hix]
    · simp [hjx]

/-  
Let 1 ≤ k ≤ n, and let S be the set of matrices X Xᵀ where X ∈ ℝ^{n × k} has rank k. Prove that the
conic hull of S is the union of {0} with the set of positive semidefinite n × n matrices of rank at
least k.
-/
theorem cone_eq_posSemidef_rank_ge_k_union_zero
    (n k : ℕ) (hk₁ : 1 ≤ k) (hk₂ : k ≤ n) :
    conicHull
      {A : Matrix (Fin n) (Fin n) ℝ |
        ∃ X : Matrix (Fin n) (Fin k) ℝ, Matrix.rank X = k ∧ A = X * X.transpose} =
      ({A : Matrix (Fin n) (Fin n) ℝ |
          A.PosSemidef ∧ k ≤ Matrix.rank A} ∪ {0}) := by
  -- We prove the two inclusions separately: closure bookkeeping forward, spectral averaging reverse.
  ext A
  constructor
  · intro hA
    -- We test the universal property of `conicHull` against the right-hand side cone.
    let T : Set (Matrix (Fin n) (Fin n) ℝ) :=
      ({A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef ∧ k ≤ Matrix.rank A} ∪ {0})
    have hS : {A : Matrix (Fin n) (Fin n) ℝ |
          ∃ X : Matrix (Fin n) (Fin k) ℝ, Matrix.rank X = k ∧ A = X * X.transpose} ⊆ T := by
      intro M hM
      rcases hM with ⟨X, hX, rfl⟩
      exact gram_generator_mem_targetCone n k hX
    have h0 : (0 : Matrix (Fin n) (Fin n) ℝ) ∈ T := by
      right
      simp
    have hAdd :
        ∀ X Y : Matrix (Fin n) (Fin n) ℝ, X ∈ T → Y ∈ T → X + Y ∈ T := by
      intro X Y hX hY
      rcases hX with hX | rfl
      · rcases hY with hY | rfl
        · left
          constructor
          · exact hX.1.add hY.1
          · exact le_trans hX.2 (rank_le_rank_add_of_posSemidef n X Y hX.1 hY.1)
        · simpa using Or.inl hX
      · simpa [zero_add] using hY
    have hSmul :
        ∀ X : Matrix (Fin n) (Fin n) ℝ, ∀ t : ℝ, 0 ≤ t → X ∈ T → t • X ∈ T := by
      intro X t ht hX
      rcases hX with hX | rfl
      · by_cases ht0 : t = 0
        · right
          simp [ht0]
        · left
          constructor
          · exact hX.1.smul ht
          · have hunit : IsUnit ((t • (1 : Matrix (Fin n) (Fin n) ℝ)).det) := by
              apply isUnit_iff_ne_zero.2
              rw [Matrix.det_smul, Matrix.det_one]
              exact mul_ne_zero (pow_ne_zero _ ht0) one_ne_zero
            simpa [smul_mul_assoc, one_mul] using
              (show k ≤ Matrix.rank ((t • (1 : Matrix (Fin n) (Fin n) ℝ)) * X) by
                simpa using (hX.2.trans_eq (Matrix.rank_mul_eq_right_of_isUnit_det _ _ hunit).symm))
      · right
        simp
    exact hA T hS h0 hAdd hSmul
  · intro hA
    rcases hA with hA | rfl
    · -- Route correction: work in the diagonal eigenbasis on the nonzero support first, and only
      -- conjugate back by the unitary eigenvector matrix after the subset-average identity is set up.
      have hH : A.IsHermitian := hA.1.isHermitian
      let α := NonzeroEigenIndex hH
      have hcard : k ≤ Fintype.card α := by
        -- The Hermitian rank formula turns the rank hypothesis into a cardinal bound on support.
        simpa [α, hH.rank_eq_card_non_zero_eigs] using hA.2
      let coeff : ℕ := Nat.choose (Fintype.card α - 1) (k - 1)
      have hcoeff_pos : 0 < coeff := by
        -- The averaging coefficient is positive because `k ≤ card α` and `k ≥ 1`.
        apply Nat.choose_pos
        exact Nat.pred_le_pred hcard
      have hcoeff_nonneg : 0 ≤ (coeff : ℝ) := by
        exact_mod_cast hcoeff_pos.le
      let subsets : Finset (Finset α) := Finset.univ.powersetCard k
      let Y : Finset α → Matrix (Fin n) (Fin k) ℝ := fun t =>
        if ht : t.card = k then
          supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht
        else 0
      let X : Finset α → Matrix (Fin n) (Fin k) ℝ := fun t =>
        (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) * Y t
      have hunitary_det :
          IsUnit (((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)).det) := by
        -- The eigenvector matrix is unitary, hence invertible.
        exact (Matrix.isUnit_iff_isUnit_det _).mp (Unitary.isUnit_coe (U := hH.eigenvectorUnitary))
      have hYgram :
          ∀ t ∈ subsets,
            Y t * (Y t)ᵀ =
              Matrix.diagonal (fun i : Fin n =>
                if hi : hH.eigenvalues i ≠ 0 then
                  if (⟨i, hi⟩ : α) ∈ t then hH.eigenvalues i else 0
                else 0) := by
        intro t htmem
        have ht : t.card = k := by simpa [subsets] using htmem
        -- Each subset contributes a diagonal ambient Gram matrix supported exactly on that subset.
        calc
          Y t * (Y t)ᵀ =
              supportSelectorMatrix hH *
                (supportSubsetColumnMatrix hH t ht *
                  (supportSubsetColumnMatrix hH t ht)ᵀ) *
                (supportSelectorMatrix hH)ᵀ := by
                  simp [Y, ht, Matrix.transpose_mul, Matrix.mul_assoc]
          _ =
              supportSelectorMatrix hH *
                Matrix.diagonal (fun a : α => if a ∈ t then hH.eigenvalues a.1 else 0) *
                (supportSelectorMatrix hH)ᵀ := by
                  rw [supportSubsetColumnMatrix_mul_transpose hH hA.1 t ht]
          _ = Matrix.diagonal (fun i : Fin n =>
                if hi : hH.eigenvalues i ≠ 0 then
                  if (⟨i, hi⟩ : α) ∈ t then hH.eigenvalues i else 0
                else 0) := by
                  simpa using
                    supportSelectorMatrix_push_diagonal hH
                      (fun a : α => if a ∈ t then hH.eigenvalues a.1 else 0)
      let Z : Finset α → Matrix α α ℝ := fun t =>
        if ht : t.card = k then
          supportSubsetColumnMatrix hH t ht * (supportSubsetColumnMatrix hH t ht)ᵀ
        else 0
      have hZdiag :
          ∀ t ∈ subsets,
            Z t =
              Matrix.diagonal (fun a : α => if a ∈ t then hH.eigenvalues a.1 else 0) := by
        intro t htmem
        have ht : t.card = k := by simpa [subsets] using htmem
        -- On the support subtype, each chosen subset contributes exactly its selected diagonal.
        simp [Z, ht, supportSubsetColumnMatrix_mul_transpose, hA.1]
      have hsumZ :
          subsets.sum Z =
            (coeff : ℝ) • Matrix.diagonal (fun a : α => hH.eigenvalues a.1) := by
        -- Route correction: count on the nonzero-eigenvalue subtype first, where the diagonal
        -- entries are plain eigenvalues rather than ambient nested `if` expressions.
        classical
        ext a b
        by_cases hab : a = b
        · subst hab
          have hentry :
              subsets.sum Z a a =
                subsets.sum (fun t : Finset α => if a ∈ t then hH.eigenvalues a.1 else (0 : ℝ)) := by
            rw [Finset.sum_apply, Finset.sum_apply]
            refine Finset.sum_congr rfl ?_
            intro t htmem
            have ht : t.card = k := by simpa [subsets] using htmem
            simp [Z, ht, supportSubsetColumnMatrix_mul_transpose, hA.1]
          rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, hentry]
          have hcountSum :
              subsets.sum (fun t : Finset α => if a ∈ t then hH.eigenvalues a.1 else (0 : ℝ)) =
                (((subsets.filter fun t : Finset α => a ∈ t).card : ℝ) * hH.eigenvalues a.1) := by
            induction subsets using Finset.induction_on with
            | empty =>
                simp
            | @insert t s ht ih =>
                by_cases hat : a ∈ t
                · rw [Finset.sum_insert ht, if_pos hat, ih]
                  have hcardNat :
                      {u ∈ insert t s | a ∈ u}.card = {u ∈ s | a ∈ u}.card + 1 := by
                    rw [Finset.filter_insert]
                    simp [hat, ht]
                  have hcard :
                      (({u ∈ insert t s | a ∈ u}.card : ℕ) : ℝ) =
                        (({u ∈ s | a ∈ u}.card : ℕ) : ℝ) + 1 := by
                    exact_mod_cast hcardNat
                  rw [hcard]
                  ring
                · rw [Finset.sum_insert ht, if_neg hat, ih]
                  have hcard :
                      ({u ∈ insert t s | a ∈ u}.card : ℕ) = {u ∈ s | a ∈ u}.card := by
                    rw [Finset.filter_insert]
                    simp [hat, ht]
                  rw [hcard]
                  simp
          rw [hcountSum]
          rw [powersetCard_contains_index_count hk₁ a]
          simp [coeff, subsets]
        · have hentry :
              subsets.sum Z a b = 0 := by
            rw [Finset.sum_apply, Finset.sum_apply]
            refine Finset.sum_eq_zero ?_
            intro t htmem
            have ht : t.card = k := by simpa [subsets] using htmem
            simp [Z, ht, supportSubsetColumnMatrix_mul_transpose, hA.1, Matrix.diagonal_apply_ne, hab]
          rw [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab]
          simp
          exact hentry
      have hpushDiag :
          supportSelectorMatrix hH * Matrix.diagonal (fun a : α => hH.eigenvalues a.1) *
              (supportSelectorMatrix hH)ᵀ =
            Matrix.diagonal hH.eigenvalues := by
        -- Pushing the subtype diagonal back to ambient coordinates restores the full eigenvalue
        -- diagonal because the omitted coordinates already have eigenvalue zero.
        ext i j
        by_cases hij : i = j
        · subst hij
          rw [supportSelectorMatrix_push_diagonal hH (fun a : α => hH.eigenvalues a.1)]
          rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
          by_cases hi : hH.eigenvalues i ≠ 0
          · simp [hi]
          · have hzero : hH.eigenvalues i = 0 := by
              simpa using hi
            simp [hi, hzero]
        · rw [supportSelectorMatrix_push_diagonal hH (fun a : α => hH.eigenvalues a.1)]
          simp [Matrix.diagonal_apply_ne, hij]
      have hsumY :
          subsets.sum (fun t => Y t * (Y t)ᵀ) = (coeff : ℝ) • Matrix.diagonal hH.eigenvalues := by
        -- We first rewrite each ambient Gram term through the support selector and then push the
        -- subtype sum to ambient coordinates.
        calc
          subsets.sum (fun t => Y t * (Y t)ᵀ)
              = subsets.sum (fun t => supportSelectorMatrix hH * Z t * (supportSelectorMatrix hH)ᵀ) := by
                  refine Finset.sum_congr rfl ?_
                  intro t htmem
                  have ht : t.card = k := by simpa [subsets] using htmem
                  simp [Y, Z, ht, Matrix.transpose_mul, Matrix.mul_assoc]
          _ = supportSelectorMatrix hH * subsets.sum Z * (supportSelectorMatrix hH)ᵀ := by
                  calc
                    subsets.sum (fun t => supportSelectorMatrix hH * Z t * (supportSelectorMatrix hH)ᵀ)
                        = subsets.sum (fun t => supportSelectorMatrix hH *
                            (Z t * (supportSelectorMatrix hH)ᵀ)) := by
                              refine Finset.sum_congr rfl ?_
                              intro t htmem
                              simp [Matrix.mul_assoc]
                    _ = supportSelectorMatrix hH *
                          subsets.sum (fun t => Z t * (supportSelectorMatrix hH)ᵀ) := by
                              induction subsets using Finset.induction_on with
                              | empty =>
                                  simp
                              | @insert a s ha ih =>
                                  simp [ha, Matrix.mul_add, ih]
                    _ = supportSelectorMatrix hH * (subsets.sum Z * (supportSelectorMatrix hH)ᵀ) := by
                              congr 1
                              induction subsets using Finset.induction_on with
                              | empty =>
                                  simp
                              | @insert a s ha ih =>
                                  simp [ha, Matrix.add_mul, ih]
                    _ = supportSelectorMatrix hH * subsets.sum Z * (supportSelectorMatrix hH)ᵀ := by
                              simp [Matrix.mul_assoc]
          _ = supportSelectorMatrix hH *
                ((coeff : ℝ) • Matrix.diagonal (fun a : α => hH.eigenvalues a.1)) *
                (supportSelectorMatrix hH)ᵀ := by
                  rw [hsumZ]
          _ = (coeff : ℝ) •
                (supportSelectorMatrix hH * Matrix.diagonal (fun a : α => hH.eigenvalues a.1) *
                  (supportSelectorMatrix hH)ᵀ) := by
                  simp [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
          _ = (coeff : ℝ) • Matrix.diagonal hH.eigenvalues := by
                  rw [hpushDiag]
      have hXrank :
          ∀ t ∈ subsets, Matrix.rank (X t) = k := by
        intro t htmem
        have ht : t.card = k := by simpa [subsets] using htmem
        have hSupportRank :
            Matrix.rank (supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht) = k := by
          have hgram :
              ((supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht)ᵀ *
                  (supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht)) =
                Matrix.diagonal
                  (fun j : Fin k => hH.eigenvalues ((t.orderEmbOfFin ht j).1)) := by
            -- Rewrite the Gram matrix so the selector contributes an identity factor.
            calc
              ((supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht)ᵀ *
                    (supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht))
                  = (supportSubsetColumnMatrix hH t ht)ᵀ *
                      ((supportSelectorMatrix hH)ᵀ * supportSelectorMatrix hH) *
                      supportSubsetColumnMatrix hH t ht := by
                        simp [Matrix.transpose_mul, Matrix.mul_assoc]
              _ = (supportSubsetColumnMatrix hH t ht)ᵀ *
                    supportSubsetColumnMatrix hH t ht := by
                      rw [supportSelectorMatrix_transpose_mul]
                      simp
              _ = Matrix.diagonal
                    (fun j : Fin k => hH.eigenvalues ((t.orderEmbOfFin ht j).1)) := by
                      rw [supportSubsetColumnMatrix_transpose_mul hH hA.1 t ht]
          -- The selected support columns have diagonal Gram matrix with exactly `k` nonzero
          -- entries, so their rank is `k`.
          calc
            Matrix.rank (supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht)
                = Matrix.rank
                    (((supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht)ᵀ) *
                      (supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht)) := by
                        symm
                        exact Matrix.rank_transpose_mul_self _
            _ = Matrix.rank
                  (Matrix.diagonal
                    (fun j : Fin k => hH.eigenvalues ((t.orderEmbOfFin ht j).1))) := by
                        rw [hgram]
            _ = k := by
                        rw [Matrix.rank_diagonal]
                        let e :
                            Fin k ≃ {j : Fin k //
                              hH.eigenvalues ((t.orderEmbOfFin ht j).1) ≠ 0} :=
                          { toFun := fun j => ⟨j, (t.orderEmbOfFin ht j).2⟩
                            invFun := fun j => j.1
                            left_inv := by intro j; rfl
                            right_inv := by intro j; cases j; rfl }
                        simpa using (Fintype.card_congr e).symm
        -- Left multiplication by the unitary eigenvector matrix preserves rank.
        calc
          Matrix.rank (X t)
              = Matrix.rank
                  ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
                    (supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht)) := by
                      simp [X, Y, ht, Matrix.mul_assoc]
          _ = Matrix.rank (supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht) := by
                simpa [Matrix.mul_assoc] using
                  Matrix.rank_mul_eq_right_of_isUnit_det
                    (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
                    (supportSelectorMatrix hH * supportSubsetColumnMatrix hH t ht) hunitary_det
          _ = k := hSupportRank
      have hspectral :
          (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
              Matrix.diagonal hH.eigenvalues *
              ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ))ᵀ =
            A := by
        -- The spectral theorem identifies the ambient conjugated diagonal with `A`.
        simpa [Unitary.conjStarAlgAut_apply] using hH.spectral_theorem.symm
      have hsumX :
          subsets.sum (fun t => X t * (X t)ᵀ) = (coeff : ℝ) • A := by
        -- Conjugating the ambient average by the unitary eigenvector matrix reconstructs `A`.
        calc
          subsets.sum (fun t => X t * (X t)ᵀ)
              = subsets.sum (fun t =>
                  (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
                    (Y t * (Y t)ᵀ) *
                    ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ))ᵀ) := by
                      refine Finset.sum_congr rfl ?_
                      intro t htmem
                      simp [X, Matrix.transpose_mul, Matrix.mul_assoc]
          _ = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
                subsets.sum (fun t => Y t * (Y t)ᵀ) *
                ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ))ᵀ := by
                  simp [Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
          _ = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
                ((coeff : ℝ) • Matrix.diagonal hH.eigenvalues) *
                ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ))ᵀ := by
                  rw [hsumY]
          _ = (coeff : ℝ) •
                ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
                  Matrix.diagonal hH.eigenvalues *
                  ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ))ᵀ) := by
                  simp [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
          _ = (coeff : ℝ) • A := by
                  rw [hspectral]
      have hcoeff_ne_zero : (coeff : ℝ) ≠ 0 := by
        exact_mod_cast hcoeff_pos.ne'
      have hcoeff_inv_nonneg : 0 ≤ (coeff : ℝ)⁻¹ := by
        exact inv_nonneg.mpr hcoeff_nonneg
      have hsum_mem :
          subsets.sum (fun t => X t * (X t)ᵀ) ∈
            conicHull
              {A : Matrix (Fin n) (Fin n) ℝ |
                ∃ X : Matrix (Fin n) (Fin k) ℝ, Matrix.rank X = k ∧ A = X * X.transpose} := by
        -- Each summand is one of the prescribed rank-`k` Gram generators, and the cone is
        -- closed under finite sums.
        refine sum_mem_conicHull subsets (fun t => X t * (X t)ᵀ) ?_
        intro t htmem
        apply subset_conicHull
        exact ⟨X t, hXrank t htmem, rfl⟩
      have hscaled_mem :
          ((coeff : ℝ)⁻¹) • subsets.sum (fun t => X t * (X t)ᵀ) ∈
            conicHull
              {A : Matrix (Fin n) (Fin n) ℝ |
                ∃ X : Matrix (Fin n) (Fin k) ℝ, Matrix.rank X = k ∧ A = X * X.transpose} := by
        -- Scaling by the inverse positive coefficient keeps us inside the conic hull.
        exact smul_mem_conicHull hcoeff_inv_nonneg hsum_mem
      -- The scaled finite sum is exactly `A`, so the reverse inclusion is complete.
      have hAeq :
          A = ((coeff : ℝ)⁻¹) • subsets.sum (fun t => X t * (X t)ᵀ) := by
        -- The positive inverse coefficient exactly rescales the averaged generator sum back to `A`.
        calc
          A = ((coeff : ℝ)⁻¹) • ((coeff : ℝ) • A) := by
                rw [smul_smul, inv_mul_cancel₀ hcoeff_ne_zero, one_smul]
          _ = ((coeff : ℝ)⁻¹) • subsets.sum (fun t => X t * (X t)ᵀ) := by
                rw [hsumX]
      exact hAeq ▸ hscaled_mem
    · exact
        zero_mem_conicHull
          (S := {A : Matrix (Fin n) (Fin n) ℝ |
            ∃ X : Matrix (Fin n) (Fin k) ℝ, Matrix.rank X = k ∧ A = X * X.transpose})

end «problem-153»
