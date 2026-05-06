import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-156»

/- [BLOCK Exercise 16.8 | 14 | thm]
Let A ∈ ℝ^{m × n} satisfy m< n and rank(A)=m. Show that there exist an orthogonal matrix Q ∈ ℝ^{n×n}
with Q^{T}Q=QQ^{T}=Iₙ, and an upper triangular matrix hat U ∈ ℝ^{m × m}, such that AQ=[ 0 & hat U ],
where 0 is the m × (n-m) zero matrix.
-/
open Matrix

/-- Full row rank implies that the family of rows of `A` is linearly independent. -/
lemma rows_linearIndependent
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hrank : Matrix.rank A = m) :
    LinearIndependent ℝ A.row := by
  -- The matrix rank is the finrank of the row span, so equality with `m` gives independence.
  rw [linearIndependent_iff_card_eq_finrank_span]
  simpa [Set.finrank, Matrix.rank_eq_finrank_span_row] using hrank.symm

/-- The row span of a full-row-rank matrix has dimension exactly the number of rows. -/
lemma rowSpan_finrank_eq
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hrank : Matrix.rank A = m) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) = m := by
  -- This is the rank characterization specialized to the row span.
  simpa [Set.finrank, Matrix.rank_eq_finrank_span_row] using hrank

/-- The block index type `Fin (n - m) ⊕ Fin m` has cardinality `n` when `m ≤ n`. -/
lemma rightBlock_card_eq
    {m n : ℕ} (hmn : m < n) :
    Fintype.card (Fin (n - m) ⊕ Fin m) = n := by
  -- This is the cardinal arithmetic needed to reindex the orthonormal basis back to `Fin n`.
  simp [Nat.sub_add_cancel hmn.le]

/-- The column reindexing convention that sends the left zero block to the later lex block and
reverses the upper-triangular block. -/
def blockLexEquiv (m n : ℕ) : Fin (n - m) ⊕ Fin m ≃ Fin m ⊕ₗ Fin (n - m) :=
  let e :
      Fin (n - m) ⊕ Fin m ≃ Fin m ⊕ₗ Fin (n - m) :=
    (Equiv.sumCongr (Equiv.refl _) (Fin.revPerm)).trans ((Equiv.sumComm _ _).trans toLex)
  { toFun := fun s ↦ toLex ((Sum.map id Fin.rev s).swap)
    invFun := e.symm
    left_inv := by
      intro s
      -- This is just the left inverse of the composed equivalence `e`, rewritten into a
      -- pointwise formula that `simp` can unfold in the main theorem.
      change e.symm (e s) = s
      exact e.left_inv s
    right_inv := by
      intro s
      -- The right inverse is the corresponding pointwise restatement of `e.apply_symm_apply`.
      change e (e.symm s) = s
      exact e.apply_symm_apply s }

/-- On the left block, `blockLexEquiv` lands in the later lex block unchanged. -/
@[simp]
lemma blockLexEquiv_apply_inl {m n : ℕ} (k : Fin (n - m)) :
    blockLexEquiv m n (Sum.inl k) = Sum.inrₗ k := by
  -- Unfold the explicit pointwise description of `blockLexEquiv`.
  simp [blockLexEquiv]

/-- On the right block, `blockLexEquiv` lands in the early lex block in reverse order. -/
@[simp]
lemma blockLexEquiv_apply_inr {m n : ℕ} (j : Fin m) :
    blockLexEquiv m n (Sum.inr j) = Sum.inlₗ (Fin.rev j) := by
  -- Unfold the explicit pointwise description of `blockLexEquiv`.
  simp [blockLexEquiv]

theorem exists_orthogonal_right_factor_with_zero_block_upperTriangular
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (hmn : m < n) (hrank : Matrix.rank A = m) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      Q.transpose * Q = 1 ∧
      Q * Q.transpose = 1 ∧
      ∃ U : Matrix (Fin m) (Fin m) ℝ,
        (∀ i j : Fin m, j < i → U i j = 0) ∧
        ∃ e : Fin n ≃ Fin (n - m) ⊕ Fin m,
          Matrix.reindex (Equiv.refl _) e (A * Q) =
            Matrix.fromCols (0 : Matrix (Fin m) (Fin (n - m)) ℝ) U := by
  let ι := Fin m ⊕ₗ Fin (n - m)
  let E := EuclideanSpace ℝ (Fin n)
  let f : ι → E := fun s ↦
    match s with
    | Sum.inlₗ j => WithLp.toLp 2 (A.row (Fin.rev j))
    | Sum.inrₗ _ => 0
  have hdim : Module.finrank ℝ E = Fintype.card ι := by
    -- The Gram-Schmidt index set has exactly `n` elements, so it can index a full orthonormal basis.
    simp [E, ι, hmn.le]
  let b : OrthonormalBasis ι ℝ E := InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  have heIndexCard : Fintype.card (Fin n) = Fintype.card ι := by
    -- This is the cardinality equality needed to reindex the Gram-Schmidt basis back to `Fin n`.
    simp [ι, hmn.le]
  let eIndex : Fin n ≃ ι := Fintype.equivOfCardEq heIndexCard
  let c : OrthonormalBasis (Fin n) ℝ E := b.reindex eIndex.symm
  let Q : Matrix (Fin n) (Fin n) ℝ := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix c
  let U : Matrix (Fin m) (Fin m) ℝ := fun i j ↦
    b.repr (WithLp.toLp 2 (A.row i)) (blockLexEquiv m n (Sum.inr j))
  let e : Fin n ≃ Fin (n - m) ⊕ Fin m := eIndex.trans (blockLexEquiv m n).symm
  refine ⟨Q, ?_, ?_, U, ?_, e, ?_⟩
  · -- The columns of `Q` are an orthonormal basis, so `Qᵀ * Q = I`.
    simpa [Q] using
      (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_conjTranspose_mul_self c
  · -- The same orthonormal-basis change-of-coordinates identity gives `Q * Qᵀ = I`.
    simpa [Q] using
      (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_self_mul_conjTranspose c
  · intro i j hij
    -- Route correction: instead of transporting the row span through `WithLp`, read the right block
    -- directly from the ambient-space Gram-Schmidt coordinates.
    have hij' : (Sum.inlₗ (Fin.rev i) : ι) < Sum.inlₗ (Fin.rev j) := by
      simpa using Fin.rev_strictAnti hij
    have hrow : f (Sum.inlₗ (Fin.rev i) : ι) = WithLp.toLp 2 (A.row i) := by
      -- The reversed row index is chosen so that Gram-Schmidt triangularity becomes upper triangularity.
      change WithLp.toLp 2 (A.row ((Fin.rev i).rev)) = WithLp.toLp 2 (A.row i)
      simp
    have htri :=
      InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular'
        (𝕜 := ℝ) (h := hdim) (f := f) hij'
    rw [hrow] at htri
    -- The reverse ordering turns the standard Gram-Schmidt triangularity into upper triangularity.
    simpa [b, U] using htri
  · have hrepr :
        ∀ i s, Matrix.reindex (Equiv.refl _) e (A * Q) i s =
          b.repr (WithLp.toLp 2 (A.row i)) (blockLexEquiv m n s) := by
      intro i s
      have hmul : ∀ j : Fin n,
          (A * Q) i j = inner ℝ (c j) (WithLp.toLp 2 (A.row i)) := by
        intro j
        change (A * ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix c)) i j =
          inner ℝ (c j) (WithLp.toLp 2 (A.row i))
        rw [Matrix.mul_apply, PiLp.inner_apply]
        simp [Module.Basis.toMatrix_apply]
      have hc : c (e.symm s) = b (blockLexEquiv m n s) := by
        rw [OrthonormalBasis.coe_reindex]
        change b (eIndex (e.symm s)) = b (blockLexEquiv m n s)
        have hs : e.symm s = eIndex.symm (blockLexEquiv m n s) := by
          apply e.symm_apply_eq.2
          change s =
            ((eIndex.trans (blockLexEquiv m n).symm) (eIndex.symm (blockLexEquiv m n s)))
          rw [Equiv.trans_apply, eIndex.apply_symm_apply]
          exact ((blockLexEquiv m n).symm_apply_apply s).symm
        have heq : eIndex (e.symm s) = blockLexEquiv m n s := by
          simpa using congrArg eIndex hs
        rw [heq]
      -- This identifies the reindexed product entry with the corresponding Gram-Schmidt coordinate.
      calc
        Matrix.reindex (Equiv.refl _) e (A * Q) i s = (A * Q) i (e.symm s) := by
          rfl
        _ = inner ℝ (c (e.symm s)) (WithLp.toLp 2 (A.row i)) := hmul _
        _ = inner ℝ (b (blockLexEquiv m n s)) (WithLp.toLp 2 (A.row i)) := by rw [hc]
        _ = b.repr (WithLp.toLp 2 (A.row i)) (blockLexEquiv m n s) := by
          simpa using
            (OrthonormalBasis.repr_apply_apply
              b (WithLp.toLp 2 (A.row i)) (blockLexEquiv m n s)).symm
    have hzero :
        ∀ i k, b.repr (WithLp.toLp 2 (A.row i)) (blockLexEquiv m n (Sum.inl k)) = 0 := by
      intro i k
      -- The left block vanishes because every row appears before every zero vector in the lex order.
      have hik : (Sum.inlₗ (Fin.rev i) : ι) < Sum.inrₗ k := by
        simp
      have hrow : f (Sum.inlₗ (Fin.rev i) : ι) = WithLp.toLp 2 (A.row i) := by
        -- The left-block vanishing uses the same row-identification as the upper-triangular step.
        change WithLp.toLp 2 (A.row ((Fin.rev i).rev)) = WithLp.toLp 2 (A.row i)
        simp
      have htri :=
        InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular'
          (𝕜 := ℝ) (h := hdim) (f := f) hik
      rw [hrow] at htri
      simpa [b] using htri
    ext i s
    cases s with
    | inl k =>
        -- The first block is zero because these coordinates lie in the orthogonal complement block.
        rw [hrepr, hzero]
        simp [Matrix.fromCols_apply_inl]
    | inr j =>
        -- The second block is exactly the matrix `U` by definition of the right-block coordinates.
        rw [hrepr]
        simp [U, Matrix.fromCols_apply_inr]

end «problem-156»
