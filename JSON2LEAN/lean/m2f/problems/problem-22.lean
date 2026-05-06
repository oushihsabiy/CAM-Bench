import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-22»
/-
On S^n, the trace inner product is the bilinear form langle A, Brangle = tr(AB) for all A, B ∈ S^n.
-/
def traceInnerProduct {n : Type} [Fintype n] [DecidableEq n]
    (A B : {M : Matrix n n ℝ // M.IsSymm}) : ℝ :=
  Matrix.trace (A.1 * B.1)

/-
A symmetric matrix D ∈ S^n with D_{ii} = 0 for all i is a Euclidean distance matrix if and only if
xᵀ D x ≤ 0 for all x ∈ ℝ^n satisfying 1ᵀ x = 0.
-/
def dualCone {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Set E) : Set E :=
  {y | ∀ x ∈ K, 0 ≤ ⟪y, x⟫}

/-- Diagonal matrices pair trivially with zero-diagonal matrices under the trace. -/
lemma trace_diagonal_mul_eq_zero_of_zero_diag {n : Type} [Fintype n] [DecidableEq n]
    (u : n → ℝ) {D : Matrix n n ℝ} (hD : ∀ i, D i i = 0) :
    Matrix.trace (Matrix.diagonal u * D) = 0 ∧ Matrix.trace (D * Matrix.diagonal u) = 0 := by
  constructor
  · -- Expand the trace entrywise so the zero-diagonal hypothesis annihilates each term.
    simp [Matrix.trace, Matrix.diagonal_mul, hD]
  · -- Commute the trace to reuse the first computation.
    rw [Matrix.trace_mul_comm]
    simp [Matrix.trace, Matrix.diagonal_mul, hD]

/-- The defining EDM conditions are preserved by nonnegative linear combinations. -/
lemma edm_mem_of_nonneg_combo {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : A.IsSymm ∧ (∀ i, A i i = 0) ∧
      ∀ x : Fin n → ℝ, (∑ i, x i) = 0 → dotProduct x (A.mulVec x) ≤ 0)
    (hB : B.IsSymm ∧ (∀ i, B i i = 0) ∧
      ∀ x : Fin n → ℝ, (∑ i, x i) = 0 → dotProduct x (B.mulVec x) ≤ 0) :
    (a • A + b • B).IsSymm ∧ (∀ i, (a • A + b • B) i i = 0) ∧
      ∀ x : Fin n → ℝ, (∑ i, x i) = 0 → dotProduct x ((a • A + b • B).mulVec x) ≤ 0 := by
  rcases hA with ⟨hA_symm, hA_diag, hA_quad⟩
  rcases hB with ⟨hB_symm, hB_diag, hB_quad⟩
  refine ⟨(hA_symm.smul a).add (hB_symm.smul b), ?_, ?_⟩
  · -- The diagonal constraint is pointwise linear.
    intro i
    simp [hA_diag i, hB_diag i]
  · -- Expand the quadratic form and use nonnegativity of the coefficients.
    intro x hx
    have hAqx : dotProduct x (A.mulVec x) ≤ 0 := hA_quad x hx
    have hBqx : dotProduct x (B.mulVec x) ≤ 0 := hB_quad x hx
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    nlinarith

/-- The concrete matrices `V` and `U` multiply to the centering projector `I - (1 / n) J`. -/
lemma v_mul_u_apply {n : ℕ} (hn : 1 < n) :
    let V : Matrix (Fin n) (Fin (n - 1)) ℝ :=
      fun i j => if (i : ℕ) = (j : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ))
    let U : Matrix (Fin (n - 1)) (Fin n) ℝ :=
      fun j i => if (i : ℕ) = (j : ℕ) then 1 else if (i : ℕ) = n - 1 then -1 else 0
    ∀ i k, (V * U) i k = if (i : ℕ) = (k : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ)) := by
  dsimp
  intro i k
  -- Split according to whether the column index is the distinguished last coordinate.
  rw [Matrix.mul_apply]
  by_cases hk : (k : ℕ) = n - 1
  · have hk_ne : ∀ j : Fin (n - 1), (k : ℕ) ≠ (j : ℕ) := by
      intro j hkj
      rw [hk] at hkj
      omega
    simp_rw [if_neg (hk_ne _), if_pos hk]
    rw [← Finset.sum_mul]
    rw [Fin.sum_univ_eq_sum_range (f := fun j : ℕ => if (i : ℕ) = j then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ)))]
    have hsplit :
        (fun j : ℕ => if (i : ℕ) = j then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ))) =
          fun j : ℕ => (if (i : ℕ) = j then (1 : ℝ) else 0) - (1 / (n : ℝ)) := by
      funext j
      by_cases hij : (i : ℕ) = j <;> simp [hij]
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
    by_cases hi : (i : ℕ) < n - 1
    · -- Off the last row, exactly one diagonal term contributes.
      rw [if_pos (by simpa [Finset.mem_range] using hi)]
      have hik : (i : ℕ) ≠ n - 1 := by omega
      simp [Finset.card_range, nsmul_eq_mul, hk, hik]
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast (show 0 < n by omega)
      have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      have hn1 : 1 ≤ n := by omega
      rw [Nat.cast_sub hn1]
      field_simp [hn0]
      ring
    · -- On the last row, every summand is the same constant.
      have hi_not_mem : ¬ (i : ℕ) ∈ Finset.range (n - 1) := by
        simpa [Finset.mem_range] using hi
      rw [if_neg hi_not_mem]
      have hi_last : (i : ℕ) = n - 1 := by omega
      simp [Finset.card_range, nsmul_eq_mul, hi_last, hk]
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast (show 0 < n by omega)
      have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      have hn1 : 1 ≤ n := by omega
      rw [Nat.cast_sub hn1]
      field_simp [hn0]
      ring
  · have hk_lt : (k : ℕ) < n - 1 := by omega
    simp_rw [if_neg hk]
    -- Away from the last column, the sum collapses to the unique matching index.
    rw [Finset.sum_eq_single ⟨k, hk_lt⟩]
    · simp
    · intro j _ hjk
      have hj_ne_k : (k : ℕ) ≠ (j : ℕ) := by
        intro h
        apply hjk
        ext
        simpa using h.symm
      simp [hj_ne_k]
    · intro hk_univ
      simp at hk_univ

/-- The one-dimensional squared-distance matrix belongs to the EDM cone. -/
lemma squared_difference_matrix_mem_edm_cone {n : ℕ} (z : Fin n → ℝ) :
    let sq : Fin n → ℝ := fun i => z i ^ 2
    let D : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.vecMulVec sq 1 + Matrix.vecMulVec 1 sq - 2 • Matrix.vecMulVec z z
    D.IsSymm ∧ (∀ i, D i i = 0) ∧
      ∀ x : Fin n → ℝ, (∑ i, x i) = 0 → dotProduct x (D.mulVec x) ≤ 0 := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · -- The squared-distance matrix is symmetric because its formula is symmetric in `i` and `j`.
    refine Matrix.IsSymm.ext ?_
    intro i j
    simp [Matrix.vecMulVec, mul_comm]
    ring_nf
  · -- Every diagonal entry is `(z i - z i)^2 = 0`.
    intro i
    simp [pow_two, Matrix.vecMulVec]
    ring_nf
  · -- The quadratic form simplifies to `-2 * (x • z)^2` on the hyperplane `∑ x_i = 0`.
    intro x hx
    have hsum1 : dotProduct x 1 = 0 := by
      simpa [dotProduct_one] using hx
    have hsum2 : dotProduct 1 x = 0 := by
      simpa [one_dotProduct] using hx
    have hA : dotProduct x ((Matrix.vecMulVec (fun i => z i ^ 2) 1).mulVec x) =
        (dotProduct x (fun i => z i ^ 2)) * (dotProduct 1 x) := by
      rw [Matrix.vecMulVec_mulVec, dotProduct_smul]
      simp
    have hB : dotProduct x ((Matrix.vecMulVec 1 (fun i => z i ^ 2)).mulVec x) =
        (dotProduct (fun i => z i ^ 2) x) * (dotProduct x 1) := by
      rw [Matrix.vecMulVec_mulVec, dotProduct_smul]
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    have hC : dotProduct x ((Matrix.vecMulVec z z).mulVec x) = (dotProduct x z) ^ 2 := by
      rw [Matrix.vecMulVec_mulVec, dotProduct_smul, dotProduct_comm z x]
      simp [pow_two]
    have h2C : dotProduct x ((2 • Matrix.vecMulVec z z).mulVec x) =
        2 * dotProduct x ((Matrix.vecMulVec z z).mulVec x) := by
      rw [Matrix.smul_mulVec, dotProduct_smul]
      simp
    change dotProduct x (((Matrix.vecMulVec (fun i => z i ^ 2) 1 + Matrix.vecMulVec 1 (fun i => z i ^ 2)) -
      2 • Matrix.vecMulVec z z).mulVec x) ≤ 0
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add, hA, hB, h2C, hC]
    simp [hsum1, hsum2, dotProduct_comm]
    nlinarith

/-- Pairing a centered matrix with a squared-distance probe recovers its quadratic form. -/
lemma trace_centered_squared_difference {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ}
    (hRrowsum : ∀ i, ∑ j, R i j = 0) (hRcolsum : ∀ j, ∑ i, R i j = 0) (z : Fin n → ℝ) :
    let D : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.vecMulVec (fun i => z i ^ 2) 1 + Matrix.vecMulVec 1 (fun i => z i ^ 2) -
        2 • Matrix.vecMulVec z z
    Matrix.trace (R * D) = -2 * dotProduct z (R.mulVec z) := by
  dsimp
  have htrace1 : Matrix.trace (R * Matrix.vecMulVec (fun i => z i ^ 2) 1) = 0 := by
    -- The first rank-one term vanishes because the columns of `R` sum to zero.
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm, Matrix.dotProduct_mulVec]
    have hzero : Matrix.vecMul 1 R = 0 := by
      ext j
      rw [Matrix.vecMul, one_dotProduct, hRcolsum j]
      simp
    rw [hzero]
    simp
  have htrace2 : Matrix.trace (R * Matrix.vecMulVec 1 (fun i => z i ^ 2)) = 0 := by
    -- The second rank-one term vanishes because the rows of `R` sum to zero.
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
    have hzero : R.mulVec 1 = 0 := by
      ext i
      rw [Matrix.mulVec, dotProduct_one, hRrowsum i]
      simp
    rw [hzero]
    simp
  have htrace3 : Matrix.trace (R * Matrix.vecMulVec z z) = dotProduct z (R.mulVec z) := by
    -- The remaining trace is exactly the quadratic form of `R` at `z`.
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm, Matrix.dotProduct_mulVec]
  rw [Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add, htrace1, htrace2,
    Matrix.mul_smul, Matrix.trace_smul, htrace3]
  ring

/-- Compressing a quadratic form through `Uᵀ` matches the quadratic form of `U * R * Uᵀ`. -/
lemma compressed_quadratic_eq {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ}
    (U : Matrix (Fin (n - 1)) (Fin n) ℝ) (x : Fin (n - 1) → ℝ) :
    let z : Fin n → ℝ := U.transpose.mulVec x
    let W : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := U * R * U.transpose
    dotProduct z (R.mulVec z) = dotProduct x (W.mulVec x) := by
  dsimp
  -- Rewrite the left quadratic form by moving the transpose off of `U`.
  have hstep := (Matrix.dotProduct_mulVec x U (R.mulVec (U.transpose.mulVec x))).symm
  have hstep' : dotProduct (U.transpose.mulVec x) (R.mulVec (U.transpose.mulVec x)) =
      dotProduct x (U.mulVec (R.mulVec (U.transpose.mulVec x))) := by
    simpa [← Matrix.vecMul_transpose U.transpose x] using hstep
  have hmul : U.mulVec (R.mulVec (U.transpose.mulVec x)) = ((U * R * U.transpose).mulVec x) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  calc
    dotProduct (U.transpose.mulVec x) (R.mulVec (U.transpose.mulVec x))
      = dotProduct x (U.mulVec (R.mulVec (U.transpose.mulVec x))) := hstep'
    _ = dotProduct x ((U * R * U.transpose).mulVec x) := by rw [hmul]

/-
Exercise 2.36 | 9 | thm

Let Sⁿ be the vector space of real symmetric n × n matrices, equipped with the trace inner product
⟨A, B⟩ = tr(AB), and let 1 ∈ ℝⁿ be the all - ones vector. Define

K = {D ∈ Sⁿ | D_{ii} = 0 for i = 1, …, n, and xᵀ D x ≤ 0 for all x ∈ ℝⁿ with 1ᵀ x = 0}.

Thus K is the cone of Euclidean distance matrices. Let V ∈ ℝ^{n×(n - 1)} be defined by

V_{ij} = {1 - 1/n if i = j, - 1/n if i ≠ j}

for i = 1, …, n and j = 1, …, n - 1. Prove that K is a convex cone and that its dual cone

K* = {Y ∈ Sⁿ | ⟨Y, D⟩ ≥ 0 for all D ∈ K}

is given by

K* = {V W Vᵀ + diag(u) | W ⪯ 0, u ∈ ℝⁿ}.
-/
theorem dualCone_of_euclideanDistanceMatrices_eq_vwvT_add_diag
    {n : ℕ} (hn : 1 < n) :
    let V : Matrix (Fin n) (Fin (n - 1)) ℝ :=
      fun i j => if (i : ℕ) = (j : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ))
    let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
      {D | D.IsSymm ∧ (∀ i, D i i = 0) ∧
        ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
          dotProduct x (D.mulVec x) ≤ 0}
    Convex ℝ K ∧
      (∀ a b, 0 ≤ a → 0 ≤ b → ∀ A ∈ K, ∀ B ∈ K, a • A + b • B ∈ K) ∧
      {Y : Matrix (Fin n) (Fin n) ℝ | Y.IsSymm ∧ ∀ D ∈ K, 0 ≤ Matrix.trace (Y * D)} =
      {Y : Matrix (Fin n) (Fin n) ℝ |
          Y.IsSymm ∧
          ∃ W : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ, ∃ u : Fin n → ℝ,
            Y = V * W * V.transpose + Matrix.diagonal u ∧
            W.IsSymm ∧
            ∀ x : Fin (n - 1) → ℝ, dotProduct x (W.mulVec x) ≤ 0} := by
  dsimp
  let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {D | D.IsSymm ∧ (∀ i, D i i = 0) ∧
      ∀ x : Fin n → ℝ, (∑ i, x i) = 0 → dotProduct x (D.mulVec x) ≤ 0}
  have hcombo :
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ∀ A ∈ K, ∀ B ∈ K, a • A + b • B ∈ K := by
    -- This packages the cone argument once so both the convexity and cone clauses can reuse it.
    intro a b ha hb A hA B hB
    simpa [K] using edm_mem_of_nonneg_combo ha hb hA hB
  refine ⟨?_, ?_, ?_⟩
  · -- Convexity follows from the same nonnegative-combination closure after imposing `a + b = 1`.
    rw [convex_iff_add_mem]
    intro A hA B hB a b ha hb hab
    exact hcombo a b ha hb A hA B hB
  · -- This is exactly the cone-closure statement requested in the theorem.
    intro a b ha hb A hA B hB
    have hreal :=
      hcombo (a : ℝ) (b : ℝ) (show 0 ≤ (a : ℝ) by exact_mod_cast ha)
        (show 0 ≤ (b : ℝ) by exact_mod_cast hb) A hA B hB
    rcases hreal with ⟨hsymm, _, hquad⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [Nat.cast_smul_eq_nsmul ℝ] using hsymm
    · intro i
      rcases hA with ⟨_, hA_diag, _⟩
      rcases hB with ⟨_, hB_diag, _⟩
      simp [hA_diag i, hB_diag i]
    · intro x hx
      simpa [Nat.cast_smul_eq_nsmul ℝ] using hquad x hx
  · -- Route correction: the earlier plan asked for full Gram-matrix EDM probes immediately.
    -- The forward inclusion is already accessible just from the centered-column identities of `V`,
    -- so we close that direction now and leave only the converse reconstruction as the blocker.
    let V : Matrix (Fin n) (Fin (n - 1)) ℝ :=
      fun i j => if (i : ℕ) = (j : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ))
    ext Y
    constructor
    · intro hY
      let u : Fin n → ℝ := fun i => ∑ j, Y i j
      let R : Matrix (Fin n) (Fin n) ℝ := Y - Matrix.diagonal u
      let U : Matrix (Fin (n - 1)) (Fin n) ℝ :=
        fun j i => if (i : ℕ) = (j : ℕ) then 1 else if (i : ℕ) = n - 1 then -1 else 0
      let W : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := U * R * U.transpose
      rcases hY with ⟨hYsymm, hdual⟩
      have hYsplit : R + Matrix.diagonal u = Y := by
        -- The row-sum diagonal removes exactly the diagonal correction from `Y`.
        simpa [R] using sub_add_cancel Y (Matrix.diagonal u)
      have hRrowsum : ∀ i, ∑ j, R i j = 0 := by
        -- The centered part has zero row sums by construction.
        intro i
        change ∑ j, (Y i j - Matrix.diagonal u i j) = 0
        rw [Finset.sum_sub_distrib]
        have hdiag : ∑ j, Matrix.diagonal u i j = ∑ j, Y i j := by
          rw [Finset.sum_eq_single i]
          · simp [u]
          · intro j _ hji
            have hij : i ≠ j := fun h => hji h.symm
            simp [Matrix.diagonal, hij]
          · simp
        rw [hdiag]
        ring
      have hRsymm : R.IsSymm := by
        -- Subtracting a diagonal matrix preserves symmetry of the centered part.
        simpa [R] using hYsymm.sub (Matrix.isSymm_diagonal u)
      have hRcolsum : ∀ j, ∑ i, R i j = 0 := by
        -- Symmetry converts the row-sum identity into the corresponding column-sum identity.
        intro j
        calc
          ∑ i, R i j = ∑ i, R j i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact (hRsymm.apply i j).symm
          _ = 0 := hRrowsum j
      have hproj_raw := v_mul_u_apply (n := n) hn
      have hproj : ∀ i k : Fin n, (V * U) i k =
          if (i : ℕ) = (k : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ)) := by
        simpa [V, U] using hproj_raw
      have hleft : (V * U) * R = R := by
        -- Left multiplication by the centering projector fixes a matrix with zero column sums.
        ext i j
        rw [Matrix.mul_apply]
        have hsum :
            (∑ k : Fin n, (V * U) i k * R k j) =
              ∑ k : Fin n,
                (if (i : ℕ) = (k : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ))) * R k j := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hproj i k]
        rw [hsum]
        have hsplit :
            (fun k : Fin n =>
                (if (i : ℕ) = (k : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ))) * R k j) =
              fun k : Fin n => (((if (i : ℕ) = (k : ℕ) then (1 : ℝ) else 0) - (1 / (n : ℝ))) * R k j) := by
          funext k
          by_cases hik : (i : ℕ) = (k : ℕ) <;> simp [hik]
        simp_rw [hsplit]
        simp_rw [sub_mul]
        simp_rw [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_eq_single i]
        · rw [hRcolsum]
          simp
        · intro x _ hxi
          by_cases hix : (i : ℕ) = (x : ℕ)
          · exfalso
            apply hxi
            ext
            simpa using hix.symm
          · simp [hix]
        · simp
      have hright : R * (V * U).transpose = R := by
        -- Right multiplication by the transpose projector fixes a matrix with zero row sums.
        ext i j
        rw [Matrix.mul_apply]
        have hsum :
            (∑ k : Fin n, R i k * (V * U).transpose k j) =
              ∑ k : Fin n,
                R i k * (if (j : ℕ) = (k : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [Matrix.transpose_apply, hproj j k]
        rw [hsum]
        have hsplit :
            (fun k : Fin n =>
                R i k * (if (j : ℕ) = (k : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ)))) =
              fun k : Fin n => (R i k * ((if (j : ℕ) = (k : ℕ) then (1 : ℝ) else 0) - (1 / (n : ℝ)))) := by
          funext k
          by_cases hjk : (j : ℕ) = (k : ℕ) <;> simp [hjk]
        simp_rw [hsplit]
        simp_rw [mul_sub]
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_eq_single j]
        · rw [hRrowsum]
          simp
        · intro x _ hxj
          by_cases hjx : (j : ℕ) = (x : ℕ)
          · exfalso
            apply hxj
            ext
            simpa using hjx.symm
          · simp [hjx]
        · simp
      have hWsymm : W.IsSymm := by
        -- Conjugating the symmetric centered matrix by `U` preserves symmetry.
        change (U * R * U.transpose).transpose = U * R * U.transpose
        calc
          (U * R * U.transpose).transpose = U.transpose.transpose * R.transpose * U.transpose := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
          _ = U * R * U.transpose := by simp [hRsymm.eq, Matrix.mul_assoc]
      have hVWV : V * W * V.transpose = R := by
        -- The projector identities recover the centered matrix from the compressed block `W`.
        calc
          V * W * V.transpose = (V * U) * R * (V * U).transpose := by
            simp [W, Matrix.mul_assoc]
          _ = R * (V * U).transpose := by rw [hleft]
          _ = R := by rw [hright]
      have hYdecomp : Y = V * W * V.transpose + Matrix.diagonal u := by
        -- Add back the diagonal correction to recover the original matrix `Y`.
        calc
          Y = R + Matrix.diagonal u := by simpa using hYsplit.symm
          _ = V * W * V.transpose + Matrix.diagonal u := by rw [← hVWV]
      have hWnonpos : ∀ x : Fin (n - 1) → ℝ, dotProduct x (W.mulVec x) ≤ 0 := by
        intro x
        let z : Fin n → ℝ := U.transpose.mulVec x
        let D : Matrix (Fin n) (Fin n) ℝ :=
          Matrix.vecMulVec (fun i => z i ^ 2) 1 + Matrix.vecMulVec 1 (fun i => z i ^ 2) -
            2 • Matrix.vecMulVec z z
        have hDraw := squared_difference_matrix_mem_edm_cone (n := n) z
        have hD : D ∈ K := by
          simpa [K, D] using hDraw
        have hDdiag : ∀ i, D i i = 0 := by
          simpa [D] using hDraw.2.1
        have htraceR : Matrix.trace (R * D) = -2 * dotProduct z (R.mulVec z) := by
          simpa [D] using trace_centered_squared_difference (R := R) hRrowsum hRcolsum z
        have htraceYD : 0 ≤ Matrix.trace (Y * D) := hdual D hD
        have hdiagTrace := (trace_diagonal_mul_eq_zero_of_zero_diag u hDdiag).1
        have htraceCentered : 0 ≤ Matrix.trace (R * D) := by
          -- The diagonal part pairs trivially with the zero-diagonal probe.
          have htraceYD' := htraceYD
          rw [← hYsplit, Matrix.add_mul, Matrix.trace_add, hdiagTrace, add_zero] at htraceYD'
          exact htraceYD'
        have hz_nonpos : dotProduct z (R.mulVec z) ≤ 0 := by
          rw [htraceR] at htraceCentered
          nlinarith
        have hcompress : dotProduct z (R.mulVec z) = dotProduct x (W.mulVec x) := by
          simpa [z, W] using compressed_quadratic_eq (R := R) U x
        rw [← hcompress]
        exact hz_nonpos
      exact ⟨hYsymm, W, u, hYdecomp, hWsymm, hWnonpos⟩
    · intro hY
      rcases hY with ⟨hYsymm, W, u, rfl, hWsymm, hWnonpos⟩
      refine ⟨hYsymm, ?_⟩
      intro D hD
      rcases hD with ⟨hDsymm, hDdiag, hDquad⟩
      -- The columns of `V` sum to zero, so the EDM inequality applies to every `V * z`.
      have hVcolsum : ∀ j : Fin (n - 1), ∑ i : Fin n, V i j = 0 := by
        intro j
        rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ => if i = (j : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ)))]
        simp_rw [show (fun i : ℕ => if i = (j : ℕ) then 1 - (1 / (n : ℝ)) else -(1 / (n : ℝ))) =
          fun i : ℕ => (if (j : ℕ) = i then (1 : ℝ) else 0) - (1 / (n : ℝ)) by
            funext i; by_cases h : i = (j : ℕ) <;> simp [h, eq_comm]]
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos]
        · simp [Finset.card_range, nsmul_eq_mul]
          have hnn : (0 : ℝ) < n := by
            exact_mod_cast (show 0 < n by omega)
          have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnn
          field_simp [hn0]
          ring
        · have hjn : (j : ℕ) < n := by omega
          simpa [Finset.mem_range] using hjn
      -- Compressing an EDM through `V` produces a negative semidefinite form.
      have hnegCompressed : (-(V.transpose * D * V)).PosSemidef := by
        refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
        · have hnegDherm : (-D).IsHermitian := by
            simpa [Matrix.IsHermitian, Matrix.IsSymm,
              Matrix.conjTranspose_eq_transpose_of_trivial] using hDsymm.neg
          simpa [V, Matrix.conjTranspose_eq_transpose_of_trivial, neg_mul, Matrix.mul_assoc] using
            (Matrix.isHermitian_conjTranspose_mul_mul V hnegDherm)
        · intro z
          have hsumV : (∑ i, (V.mulVec z) i) = 0 := by
            calc
              ∑ i, (V.mulVec z) i = ∑ i, ∑ j, V i j * z j := by
                simp [Matrix.mulVec, dotProduct]
              _ = ∑ j, ∑ i, V i j * z j := by
                rw [Finset.sum_comm]
              _ = ∑ j, (∑ i, V i j) * z j := by
                simp [Finset.sum_mul]
              _ = 0 := by
                refine Finset.sum_eq_zero ?_
                intro j hj
                rw [hVcolsum j, zero_mul]
          have hquad : dotProduct (V.mulVec z) (D.mulVec (V.mulVec z)) ≤ 0 := hDquad (V.mulVec z) hsumV
          have hrewrite :
              star z ⬝ᵥ (-(V.transpose * D * V)).mulVec z =
                - dotProduct (V.mulVec z) (D.mulVec (V.mulVec z)) := by
            rw [Matrix.neg_mulVec, dotProduct_neg]
            have hinner :
                dotProduct z ((V.transpose * (D * V)).mulVec z) =
                  dotProduct (V.mulVec z) ((D * V).mulVec z) := by
              calc
                dotProduct z ((V.transpose * (D * V)).mulVec z)
                  = (z ᵥ* (V.transpose * (D * V))) ⬝ᵥ z := by rw [Matrix.dotProduct_mulVec]
                _ = ((z ᵥ* V.transpose) ᵥ* (D * V)) ⬝ᵥ z := by rw [Matrix.vecMul_vecMul]
                _ = dotProduct (V.mulVec z) ((D * V).mulVec z) := by
                  rw [Matrix.vecMul_transpose, Matrix.dotProduct_mulVec]
            simpa [Matrix.mul_assoc, Matrix.mulVec_mulVec] using congrArg Neg.neg hinner
          rw [hrewrite]
          exact neg_nonneg.mpr hquad
      -- The representing matrix `W` is negative semidefinite, hence `-W` is PSD.
      have hnegW : (-W).PosSemidef := by
        refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
        · simpa [Matrix.IsHermitian, Matrix.IsSymm,
            Matrix.conjTranspose_eq_transpose_of_trivial] using hWsymm.neg
        · intro x
          have hrewrite : star x ⬝ᵥ (-W) *ᵥ x = - dotProduct x (W.mulVec x) := by
            simp [dotProduct, Matrix.neg_mulVec]
          rw [hrewrite]
          exact neg_nonneg.mpr (hWnonpos x)
      -- The diagonal term vanishes against every EDM, and the remaining trace is a PSD pairing.
      have hdiagTrace := (trace_diagonal_mul_eq_zero_of_zero_diag u hDdiag).1
      rw [Matrix.add_mul, Matrix.trace_add, hdiagTrace, add_zero]
      have htraceReassoc :
          Matrix.trace ((V * W * V.transpose) * D) = Matrix.trace (W * (V.transpose * D * V)) := by
        calc
          Matrix.trace ((V * W * V.transpose) * D)
              = Matrix.trace ((V * W) * (V.transpose * D)) := by simp [Matrix.mul_assoc]
          _ = Matrix.trace ((V.transpose * D) * (V * W)) := by rw [Matrix.trace_mul_comm]
          _ = Matrix.trace ((V.transpose * D * V) * W) := by simp [Matrix.mul_assoc]
          _ = Matrix.trace (W * (V.transpose * D * V)) := by rw [Matrix.trace_mul_comm]
      rw [htraceReassoc]
      have htracePair : 0 ≤ Matrix.trace (W * (V.transpose * D * V)) := by
        rw [show W * (V.transpose * D * V) = (-W) * (-(V.transpose * D * V)) by simp]
        rcases Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hnegCompressed with ⟨B, hB⟩
        rw [hB]
        have hpsd : (B * (-W) * Bᴴ).PosSemidef := hnegW.mul_mul_conjTranspose_same B
        have htraceNonneg : 0 ≤ Matrix.trace ((B * (-W)) * Bᴴ) := by
          simpa [Matrix.mul_assoc] using (Matrix.PosSemidef.trace_nonneg hpsd)
        have hcycle₁ : Matrix.trace ((B * (-W)) * Bᴴ) = Matrix.trace ((Bᴴ * B) * (-W)) := by
          simpa [Matrix.mul_assoc] using (Matrix.trace_mul_cycle B (-W) Bᴴ)
        have hcycle₂ : Matrix.trace ((Bᴴ * B) * (-W)) = Matrix.trace ((-W) * (Bᴴ * B)) := by
          rw [Matrix.trace_mul_comm]
        rw [hcycle₁, hcycle₂] at htraceNonneg
        exact htraceNonneg
      exact htracePair

end «problem-22»
