import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-75»


open Matrix

/-- The coordinate frame attached to an embedding picks distinct standard basis columns. -/
def coordinateFrame {α : Type*} [DecidableEq α] {k : ℕ} (e : Fin k ↪ α) :
    Matrix α (Fin k) ℝ :=
  fun i j => if e j = i then 1 else 0

/-- The columns of a coordinate frame are orthonormal. -/
lemma coordinateFrame_transpose_mul_self {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (e : Fin k ↪ α) :
    (coordinateFrame e).transpose * coordinateFrame e = 1 := by
  -- Each selected column is a standard basis vector, and distinct columns have disjoint support.
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [coordinateFrame, Matrix.mul_apply]
  · simp [coordinateFrame, Matrix.mul_apply, hij, e.injective.eq_iff]

/-- The complement of the projection onto an orthonormal frame is positive semidefinite. -/
lemma one_sub_mul_transpose_self_posSemidef
    {m : Type*} [Fintype m] [DecidableEq m] {k : ℕ}
    (U : Matrix m (Fin k) ℝ) (hU : U.transpose * U = 1) :
    Matrix.PosSemidef ((1 : Matrix m m ℝ) - U * U.transpose) := by
  let P : Matrix m m ℝ := U * U.transpose
  have hP_sq : P * P = P := by
    -- Orthonormal columns make `P` an idempotent projection.
    calc
      P * P = U * (U.transpose * U) * U.transpose := by
        simp only [P, Matrix.mul_assoc]
      _ = U * (1 : Matrix (Fin k) (Fin k) ℝ) * U.transpose := by rw [hU]
      _ = P := by simp [P]
  have hP_symm : P.IsSymm := by
    -- The matrix `U Uᵀ` is symmetric by construction.
    change P.transpose = P
    simpa [P] using (transpose_mul U U.transpose)
  have hcomp_eq :
      ((1 : Matrix m m ℝ) - P) * (((1 : Matrix m m ℝ) - P)ᴴ) =
        (1 : Matrix m m ℝ) - P := by
    -- The complement of a symmetric idempotent is itself a projection.
    change ((1 : Matrix m m ℝ) - P) * (((1 : Matrix m m ℝ) - P)ᵀ) =
      (1 : Matrix m m ℝ) - P
    calc
      ((1 : Matrix m m ℝ) - P) * (((1 : Matrix m m ℝ) - P)ᵀ)
          = ((1 : Matrix m m ℝ) - P) * ((1 : Matrix m m ℝ) - P) := by
              rw [Matrix.transpose_sub, Matrix.transpose_one, hP_symm]
      _ = ((1 : Matrix m m ℝ) - P) - (((1 : Matrix m m ℝ) - P) * P) := by
            rw [Matrix.mul_sub, Matrix.mul_one]
      _ = ((1 : Matrix m m ℝ) - P) - (P - P * P) := by
            rw [Matrix.sub_mul, Matrix.one_mul]
      _ = (1 : Matrix m m ℝ) - P := by simp [hP_sq]
  -- The complement of a symmetric idempotent is itself a projection, hence PSD.
  have hpsd := Matrix.posSemidef_self_mul_conjTranspose ((1 : Matrix m m ℝ) - P)
  exact hcomp_eq ▸ hpsd
/-
A candidate point for the semidefinite program above, packaging the fixed data A, k together with
decision variables X, U, V and the SDP constraints.
-/
structure KyFanNormSDP (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] where
  A : Matrix m n ℝ
  k : ℕ
  X : Matrix m n ℝ
  U : Matrix m m ℝ
  V : Matrix n n ℝ
  U_symm : U.IsSymm
  V_symm : V.IsSymm
  block_psd :
    PosSemidef
      (Matrix.fromBlocks U X X.transpose V)
  U_le_one :
    PosSemidef ((1 : Matrix m m ℝ) - U)
  V_le_one :
    PosSemidef ((1 : Matrix n n ℝ) - V)
  trace_eq :
    Matrix.trace U + Matrix.trace V = 2 * k

/-
The feasibility predicate encoding the four SDP constraints: block positive semidefiniteness, U ≼ I,
V ≼ I, and tr(U) + tr(V) = 2k.
-/
def KyFanNormSDP.isFeasible
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : KyFanNormSDP m n) : Prop :=
  PosSemidef (Matrix.fromBlocks P.U P.X P.X.transpose P.V) ∧
  PosSemidef ((1 : Matrix m m ℝ) - P.U) ∧
  PosSemidef ((1 : Matrix n n ℝ) - P.V) ∧
  Matrix.trace P.U + Matrix.trace P.V = 2 * P.k

/-
The SDP objective tr(Aᵀ X).
-/
def KyFanNormSDP.objective
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : KyFanNormSDP m n) : ℝ :=
  Matrix.trace (P.A.transpose * P.X)

/-- A block-diagonal matrix is PSD when each diagonal block is PSD. -/
lemma blockDiagonal_posSemidef
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℝ} {D : Matrix n n ℝ}
    (hA : PosSemidef A) (hD : PosSemidef D) :
    PosSemidef (Matrix.fromBlocks A 0 0 D) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · -- The block-diagonal matrix is Hermitian because both diagonal blocks are Hermitian.
    exact Matrix.IsHermitian.fromBlocks hA.isHermitian (by ext i j <;> simp) hD.isHermitian
  · intro x
    -- The quadratic form splits as a sum of the quadratic forms of the two diagonal blocks.
    calc
      0 ≤ star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
            star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) :=
        add_nonneg (hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl))
          (hD.dotProduct_mulVec_nonneg (x ∘ Sum.inr))
      _ = star x ⬝ᵥ ((Matrix.fromBlocks A 0 0 D) *ᵥ x) := by
        simp [dotProduct, Matrix.fromBlocks_mulVec]

/-- Feasibility upgrades the block constraint to the normalized block matrix `[I, X; Xᵀ, I]`. -/
lemma normalizedIdentityBlockPosSemidef
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : KyFanNormSDP m n) :
    PosSemidef (Matrix.fromBlocks (1 : Matrix m m ℝ) P.X P.X.transpose (1 : Matrix n n ℝ)) := by
  have hdiag :
      PosSemidef
        (Matrix.fromBlocks ((1 : Matrix m m ℝ) - P.U) 0 0 ((1 : Matrix n n ℝ) - P.V)) :=
    -- The slack matrices on the two diagonal blocks stay PSD after taking the direct sum.
    blockDiagonal_posSemidef P.U_le_one P.V_le_one
  have hadd := Matrix.PosSemidef.add P.block_psd hdiag
  -- Adding the slack matrix exactly replaces `U` and `V` by identities.
  convert hadd using 1
  ext i j <;> cases i <;> cases j <;> simp [sub_eq_add_neg, add_comm, add_left_comm]

/-- Every feasible `X` is a contraction on the right: `I - Xᵀ X` is PSD. -/
lemma feasibleRightContractionPosSemidef
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : KyFanNormSDP m n) :
    PosSemidef ((1 : Matrix n n ℝ) - P.X.transpose * P.X) := by
  -- Route correction: take the Schur complement of the normalized block matrix instead of
  -- diagonalizing `U` and `V` separately.
  letI : Invertible (1 : Matrix m m ℝ) := invertibleOne
  have hiff :=
    Matrix.PosDef.fromBlocks₁₁ P.X (1 : Matrix n n ℝ)
      (Matrix.PosDef.one : PosDef (1 : Matrix m m ℝ))
  -- With the identity in the top-left corner, the Schur complement is exactly `I - Xᵀ X`.
  simpa using hiff.mp (normalizedIdentityBlockPosSemidef P)

/-- Every diagonal entry of `Xᵀ X` coming from a feasible point is bounded by `1`. -/
lemma feasibleRightGram_diag_le_one
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : KyFanNormSDP m n) (i : n) :
    (P.X.transpose * P.X) i i ≤ 1 := by
  have hnonneg :
      0 ≤ (P.X.transpose * P.X) i i := by
    -- The Gram matrix `Xᵀ X` is always PSD, so its diagonal entries are nonnegative.
    simpa using (Matrix.posSemidef_conjTranspose_mul_self P.X).diag_nonneg (i := i)
  have hcontractive :
      0 ≤ 1 - (P.X.transpose * P.X) i i := by
    -- The Schur-complement contraction bound controls the same diagonal entries from above.
    simpa using (feasibleRightContractionPosSemidef P).diag_nonneg (i := i)
  -- Over `ℝ`, these two scalar inequalities collapse to the desired bound.
  linarith

/-- An orthonormal pair of `k`-frames yields a feasible SDP point with the matching objective. -/
lemma orthonormalFrameFeasiblePoint
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ)
    (U : Matrix m (Fin k) ℝ) (V : Matrix n (Fin k) ℝ)
    (hU : U.transpose * U = 1) (hV : V.transpose * V = 1) :
    ∃ P : KyFanNormSDP m n, P.A = A ∧ P.k = k ∧
      P.objective = Matrix.trace (U.transpose * A * V) := by
  let X : Matrix m n ℝ := U * V.transpose
  let U₀ : Matrix m m ℝ := U * U.transpose
  let V₀ : Matrix n n ℝ := V * V.transpose
  have hU₀_symm : U₀.IsSymm := by
    -- The Gram matrix of a frame is symmetric.
    change U₀.transpose = U₀
    simpa [U₀] using (transpose_mul U U.transpose)
  have hV₀_symm : V₀.IsSymm := by
    -- The same symmetry argument works for the `V`-block.
    change V₀.transpose = V₀
    simpa [V₀] using (transpose_mul V V.transpose)
  have hU_conj : Uᴴ = U.transpose := by
    -- Over `ℝ`, conjugate transpose is just transpose.
    ext i j
    simp [Matrix.conjTranspose]
  have hV_conj : Vᴴ = V.transpose := by
    -- The same real-valued simplification applies to `V`.
    ext i j
    simp [Matrix.conjTranspose]
  have hgram :
      Matrix.fromRows U V * (Matrix.fromRows U V)ᴴ =
        Matrix.fromBlocks U₀ X X.transpose V₀ := by
    -- The whole block matrix is the Gram matrix of the stacked frame `[U; V]`.
    calc
      Matrix.fromRows U V * (Matrix.fromRows U V)ᴴ
          = Matrix.fromRows U V * Matrix.fromCols Uᴴ Vᴴ := by
              rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose]
      _ = Matrix.fromBlocks (U * Uᴴ) (U * Vᴴ) (V * Uᴴ) (V * Vᴴ) := by
            simpa using (Matrix.fromRows_mul_fromCols U V Uᴴ Vᴴ)
      _ = Matrix.fromBlocks (U * U.transpose) (U * V.transpose)
            (V * U.transpose) (V * V.transpose) := by
            rw [hU_conj, hV_conj]
      _ = Matrix.fromBlocks U₀ X X.transpose V₀ := by
              simp [U₀, V₀, X, Matrix.transpose_mul]
  have hblock_psd :
      PosSemidef (Matrix.fromBlocks U₀ X X.transpose V₀) := by
    -- A Gram matrix is automatically positive semidefinite.
    exact hgram ▸ Matrix.posSemidef_self_mul_conjTranspose (Matrix.fromRows U V)
  have hU₀_le_one : PosSemidef ((1 : Matrix m m ℝ) - U₀) := by
    -- The orthogonal complement of the `U`-projection is again PSD.
    simpa [U₀] using one_sub_mul_transpose_self_posSemidef U hU
  have hV₀_le_one : PosSemidef ((1 : Matrix n n ℝ) - V₀) := by
    -- The same projection-complement argument applies to `V`.
    simpa [V₀] using one_sub_mul_transpose_self_posSemidef V hV
  have htrace_U₀ : Matrix.trace U₀ = k := by
    -- Cycling the trace moves the rectangular factors into the orthonormal relation `UᵀU = I`.
    calc
      Matrix.trace U₀ = Matrix.trace (U.transpose * U) := by
        simpa [U₀] using Matrix.trace_mul_comm U U.transpose
      _ = Matrix.trace (1 : Matrix (Fin k) (Fin k) ℝ) := by rw [hU]
      _ = k := by simp
  have htrace_V₀ : Matrix.trace V₀ = k := by
    -- The `V`-trace is identical for the same reason.
    calc
      Matrix.trace V₀ = Matrix.trace (V.transpose * V) := by
        simpa [V₀] using Matrix.trace_mul_comm V V.transpose
      _ = Matrix.trace (1 : Matrix (Fin k) (Fin k) ℝ) := by rw [hV]
      _ = k := by simp
  have htrace_eq : Matrix.trace U₀ + Matrix.trace V₀ = 2 * k := by
    -- Both projection traces equal the frame dimension.
    linarith
  have hobjective :
      Matrix.trace (A.transpose * X) = Matrix.trace (U.transpose * A * V) := by
    -- Route correction: normalize the rectangular trace by transposing once, then cycling.
    calc
      Matrix.trace (A.transpose * X) = Matrix.trace (A * X.transpose) := by
        simpa using Matrix.trace_transpose_mul A X.transpose
      _ = Matrix.trace (A * V * U.transpose) := by
        simp [X, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Matrix.trace (U.transpose * A * V) := by
        simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle A V U.transpose
  let P : KyFanNormSDP m n :=
    { A := A
      k := k
      X := X
      U := U₀
      V := V₀
      U_symm := hU₀_symm
      V_symm := hV₀_symm
      block_psd := hblock_psd
      U_le_one := hU₀_le_one
      V_le_one := hV₀_le_one
      trace_eq := htrace_eq }
  refine ⟨P, rfl, rfl, ?_⟩
  -- The objective matches the variational witness by the trace computation above.
  simpa [KyFanNormSDP.objective, P, X] using hobjective

/-- The trace of a square block matrix is the sum of the traces of its diagonal blocks. -/
lemma trace_fromBlocks
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ) :
    Matrix.trace (Matrix.fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  -- The diagonal of a block matrix splits over the left and right summands.
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- Flipping the sign on the right block preserves positivity of the normalized identity block. -/
lemma signedNormalizedIdentityBlockPosSemidef
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : KyFanNormSDP m n) :
    PosSemidef
      (Matrix.fromBlocks (1 : Matrix m m ℝ) (-P.X) (-P.X.transpose) (1 : Matrix n n ℝ)) := by
  let D : Matrix (Sum m n) (Sum m n) ℝ :=
    Matrix.fromBlocks (1 : Matrix m m ℝ) 0 0 (- (1 : Matrix n n ℝ))
  have hD_transpose : Dᵀ = D := by
    -- The sign matrix is diagonal, hence symmetric.
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · by_cases hij : i = j <;> simp [D, hij, eq_comm]
    · simp [D]
    · simp [D]
    · by_cases hij : i = j <;> simp [D, hij, eq_comm]
  have hcongr := (normalizedIdentityBlockPosSemidef P).mul_mul_conjTranspose_same D
  -- Conjugation by the block-diagonal sign matrix only flips the off-diagonal blocks.
  simpa [D, hD_transpose, Matrix.fromBlocks_multiply, sub_eq_add_neg] using hcongr

/-- The half-scaled feasible block matrix is a positive contraction with trace `k`. -/
lemma feasibleHalfBlock_isTraceKContraction
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : KyFanNormSDP m n) :
    let W : Matrix (Sum m n) (Sum m n) ℝ := Matrix.fromBlocks P.U P.X P.X.transpose P.V
    let Y : Matrix (Sum m n) (Sum m n) ℝ := (1 / 2 : ℝ) • W
    PosSemidef Y ∧
      PosSemidef ((1 : Matrix (Sum m n) (Sum m n) ℝ) - Y) ∧
      Matrix.trace Y = P.k := by
  let W : Matrix (Sum m n) (Sum m n) ℝ := Matrix.fromBlocks P.U P.X P.X.transpose P.V
  let Y : Matrix (Sum m n) (Sum m n) ℝ := (1 / 2 : ℝ) • W
  have hY_psd : PosSemidef Y := by
    -- The original block constraint stays PSD after scaling by `1/2`.
    simpa [W, Y] using P.block_psd.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hslack :
      PosSemidef
        (Matrix.fromBlocks ((1 : Matrix m m ℝ) - P.U) 0 0 ((1 : Matrix n n ℝ) - P.V)) :=
    -- The diagonal slack blocks remain PSD after taking their direct sum.
    blockDiagonal_posSemidef P.U_le_one P.V_le_one
  have hminus_core :
      PosSemidef
        (Matrix.fromBlocks (1 : Matrix m m ℝ) (-P.X) (-P.X.transpose) (1 : Matrix n n ℝ) +
          Matrix.fromBlocks ((1 : Matrix m m ℝ) - P.U) 0 0 ((1 : Matrix n n ℝ) - P.V)) := by
    -- The sign-flipped normalized block and the diagonal slack add to the complement numerator.
    exact Matrix.PosSemidef.add (signedNormalizedIdentityBlockPosSemidef P) hslack
  have hone_sub_Y :
      PosSemidef ((1 : Matrix (Sum m n) (Sum m n) ℝ) - Y) := by
    have hscaled : PosSemidef
        ((1 / 2 : ℝ) •
          (Matrix.fromBlocks (1 : Matrix m m ℝ) (-P.X) (-P.X.transpose) (1 : Matrix n n ℝ) +
            Matrix.fromBlocks ((1 : Matrix m m ℝ) - P.U) 0 0 ((1 : Matrix n n ℝ) - P.V))) := by
      -- Scaling the complement numerator by `1/2` preserves positivity.
      exact hminus_core.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    -- The complement `1 - Y` is exactly this scaled numerator.
    refine (show
      ((1 / 2 : ℝ) •
          (Matrix.fromBlocks (1 : Matrix m m ℝ) (-P.X) (-P.X.transpose) (1 : Matrix n n ℝ) +
            Matrix.fromBlocks ((1 : Matrix m m ℝ) - P.U) 0 0 ((1 : Matrix n n ℝ) - P.V)))
        = ((1 : Matrix (Sum m n) (Sum m n) ℝ) - Y) from ?_).symm ▸ hscaled
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [W, Y, Matrix.one_apply] <;> ring
  have htrace_Y : Matrix.trace Y = P.k := by
    -- The block trace is the average of `trace U + trace V`, which equals `2k`.
    have htrace :
        Matrix.trace Y = (1 / 2 : ℝ) * (Matrix.trace P.U + Matrix.trace P.V) := by
      simp [W, Y, trace_fromBlocks]
    linarith [P.trace_eq, htrace]
  exact ⟨hY_psd, hone_sub_Y, htrace_Y⟩

/-- The SDP objective is the block-dilation trace against the half-scaled feasible block matrix. -/
lemma objective_eq_blockDilationTrace
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (P : KyFanNormSDP m n) (hPA : P.A = A) :
    let W : Matrix (Sum m n) (Sum m n) ℝ := Matrix.fromBlocks P.U P.X P.X.transpose P.V
    let Y : Matrix (Sum m n) (Sum m n) ℝ := (1 / 2 : ℝ) • W
    let B : Matrix (Sum m n) (Sum m n) ℝ :=
      Matrix.fromBlocks (0 : Matrix m m ℝ) A A.transpose (0 : Matrix n n ℝ)
    P.objective = Matrix.trace (B * Y) := by
  let W : Matrix (Sum m n) (Sum m n) ℝ := Matrix.fromBlocks P.U P.X P.X.transpose P.V
  let Y : Matrix (Sum m n) (Sum m n) ℝ := (1 / 2 : ℝ) • W
  let B : Matrix (Sum m n) (Sum m n) ℝ :=
    Matrix.fromBlocks (0 : Matrix m m ℝ) A A.transpose (0 : Matrix n n ℝ)
  have htrace :
      Matrix.trace (B * Y) = Matrix.trace (A.transpose * P.X) := by
    -- Expanding the block product leaves only the two off-diagonal trace contributions.
    calc
      Matrix.trace (B * Y) = (1 / 2 : ℝ) * Matrix.trace (B * W) := by
        simp [Y, Matrix.trace_smul]
      _ = (1 / 2 : ℝ) *
          (Matrix.trace (A * P.X.transpose) + Matrix.trace (A.transpose * P.X)) := by
        simp [B, W, Matrix.fromBlocks_multiply, trace_fromBlocks]
      _ = (1 / 2 : ℝ) *
          (Matrix.trace (A.transpose * P.X) + Matrix.trace (A.transpose * P.X)) := by
        simpa using congrArg
          (fun t : ℝ => (1 / 2 : ℝ) * (t + Matrix.trace (A.transpose * P.X)))
          (Matrix.trace_transpose_mul A P.X.transpose).symm
      _ = Matrix.trace (A.transpose * P.X) := by ring
  -- This is exactly the original objective after rewriting `P.A` to `A`.
  calc
    P.objective = Matrix.trace (A.transpose * P.X) := by simp [KyFanNormSDP.objective, hPA]
    _ = Matrix.trace (B * Y) := htrace.symm

/-- Every entry of an orthonormal `k`-frame has absolute value at most `1`. -/
lemma orthonormalFrame_entry_abs_le_one
    {m : Type*} [Fintype m] [DecidableEq m] {k : ℕ}
    (U : Matrix m (Fin k) ℝ) (hU : U.transpose * U = 1) (i : m) (t : Fin k) :
    |U i t| ≤ 1 := by
  -- The diagonal entry `(Uᵀ U) t t` is the squared norm of the `t`-th column.
  have hdiag : ∑ j, U j t * U j t = 1 := by
    have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M t t) hU
    simpa [Matrix.mul_apply] using h
  have hsq_le : U i t * U i t ≤ 1 := by
    have hnonneg : ∀ j : m, 0 ≤ U j t * U j t := by
      intro j
      nlinarith [sq_nonneg (U j t)]
    calc
      U i t * U i t ≤ ∑ j, U j t * U j t := by
        simpa using
          (Finset.single_le_sum
            (fun j _ => hnonneg j)
            (by simp : i ∈ (Finset.univ : Finset m)))
      _ = 1 := hdiag
  have hsquare : (U i t) ^ 2 ≤ 1 := by
    simpa [pow_two] using hsq_le
  have hupper : U i t ≤ 1 := by
    nlinarith [sq_nonneg (1 - U i t), hsquare]
  have hlower : -1 ≤ U i t := by
    nlinarith [sq_nonneg (U i t + 1), hsquare]
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The Ky Fan witness set is bounded above by a crude entrywise `ℓ¹` bound on `A`. -/
lemma bddAbove_kyFanWitnessSet
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) :
    BddAbove {r : ℝ | ∃ U : Matrix m (Fin k) ℝ, ∃ V : Matrix n (Fin k) ℝ,
      U.transpose * U = 1 ∧ V.transpose * V = 1 ∧
      r = Matrix.trace (U.transpose * A * V)} := by
  let C : ℝ := ∑ j, ∑ i, |A j i|
  refine ⟨k * C, ?_⟩
  intro r hr
  rcases hr with ⟨U, V, hU, hV, rfl⟩
  have htrace_abs :
      |Matrix.trace (U.transpose * A * V)| ≤
        ∑ t, ∑ i, ∑ j, |U j t| * |A j i| * |V i t| := by
    -- Expand the trace, then apply the triangle inequality twice.
    calc
      |Matrix.trace (U.transpose * A * V)|
          = |∑ t, (U.transpose * A * V) t t| := by
              simp [Matrix.trace]
      _ ≤ ∑ t, |(U.transpose * A * V) t t| := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (s := (Finset.univ : Finset (Fin k)))
                (f := fun t => (U.transpose * A * V) t t))
      _ = ∑ t, |∑ i, (U.transpose * A) t i * V i t| := by
            simp [Matrix.mul_apply]
      _ ≤ ∑ t, ∑ i, |(U.transpose * A) t i * V i t| := by
            refine Finset.sum_le_sum ?_
            intro t _
            simpa using
              (Finset.abs_sum_le_sum_abs
                (s := (Finset.univ : Finset n))
                (f := fun i => (U.transpose * A) t i * V i t))
      _ = ∑ t, ∑ i, |(U.transpose * A) t i| * |V i t| := by
            simp [abs_mul]
      _ = ∑ t, ∑ i, |∑ j, U j t * A j i| * |V i t| := by
            simp [Matrix.mul_apply]
      _ ≤ ∑ t, ∑ i, (∑ j, |U j t * A j i|) * |V i t| := by
            refine Finset.sum_le_sum ?_
            intro t _
            refine Finset.sum_le_sum ?_
            intro i _
            exact mul_le_mul_of_nonneg_right
              (by
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (s := (Finset.univ : Finset m))
                    (f := fun j => U j t * A j i)))
              (abs_nonneg _)
      _ = ∑ t, ∑ i, (∑ j, |U j t| * |A j i|) * |V i t| := by
            simp [abs_mul]
      _ = ∑ t, ∑ i, ∑ j, |U j t| * |A j i| * |V i t| := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  have hentrywise :
      ∑ t, ∑ i, ∑ j, |U j t| * |A j i| * |V i t| ≤ k * C := by
    -- Each frame entry has absolute value at most `1`, so each summand is bounded by `|A j i|`.
    calc
      ∑ t, ∑ i, ∑ j, |U j t| * |A j i| * |V i t|
          ≤ ∑ t, C := by
              refine Finset.sum_le_sum ?_
              intro t _
              have hCt : ∑ i, ∑ j, |U j t| * |A j i| * |V i t| ≤ C := by
                calc
                  ∑ i, ∑ j, |U j t| * |A j i| * |V i t|
                      ≤ ∑ i, ∑ j, |A j i| := by
                          refine Finset.sum_le_sum ?_
                          intro i _
                          refine Finset.sum_le_sum ?_
                          intro j _
                          have hUabs := orthonormalFrame_entry_abs_le_one U hU j t
                          have hVabs := orthonormalFrame_entry_abs_le_one V hV i t
                          have huv_le_one : |U j t| * |V i t| ≤ 1 := by
                            exact mul_le_one₀ hUabs (abs_nonneg _) hVabs
                          calc
                            |U j t| * |A j i| * |V i t|
                                = |A j i| * (|U j t| * |V i t|) := by ring
                            _ ≤ |A j i| * 1 := by
                                  exact mul_le_mul_of_nonneg_left huv_le_one (abs_nonneg _)
                            _ = |A j i| := by ring
                  _ = C := by
                        show ∑ i, ∑ j, |A j i| = ∑ j, ∑ i, |A j i|
                        exact Finset.sum_comm
              simpa [C] using hCt
      _ = k * C := by
            simp [C]
  -- The crude absolute-value estimate is enough to produce an upper bound for `sSup`.
  exact (le_abs_self _).trans (htrace_abs.trans hentrywise)

/-- An antitone weight sequence dominates every mass vector in `[0,1]` with total mass `k` by its
first `k` entries. -/
lemma weighted_sum_le_head_sum_of_unit_interval_mass
    {N k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ N)
    (lam z : Fin N → ℝ)
    (hlam : Antitone lam)
    (hz_nonneg : ∀ i, 0 ≤ z i)
    (hz_le_one : ∀ i, z i ≤ 1)
    (hz_sum : ∑ i, z i = k) :
    ∑ i, lam i * z i ≤ ∑ j : Fin k, lam (Fin.castLE hkn j) := by
  let j0 : Fin k := ⟨k - 1, Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_one) hk1) Nat.zero_lt_one⟩
  let t : ℝ := lam (Fin.castLE hkn j0)
  have ht_head : ∀ j : Fin k, 0 ≤ lam (Fin.castLE hkn j) - t := by
    intro j
    -- Every selected head entry lies above the threshold `t`.
    refine sub_nonneg.mpr ?_
    exact hlam (by
      change (Fin.castLE hkn j).1 ≤ (Fin.castLE hkn j0).1
      exact Nat.le_pred_of_lt j.2)
  have ht_tail : ∀ i : Fin N, k ≤ i.1 → lam i - t ≤ 0 := by
    intro i hi
    -- Every tail entry lies below the same threshold.
    have hcast_le : (Fin.castLE hkn j0 : Fin N) ≤ i := by
      change (Fin.castLE hkn j0).1 ≤ i.1
      exact le_trans (Nat.sub_le _ _) hi
    exact sub_nonpos.mpr (hlam hcast_le)
  have hpointwise :
      ∀ i : Fin N,
        (lam i - t) * z i ≤ if hi : i.1 < k then lam i - t else 0 := by
    intro i
    by_cases hi : i.1 < k
    · -- On the head, the coefficient `z i` is at most `1`.
      have hnonneg : 0 ≤ lam i - t := by
        refine sub_nonneg.mpr ?_
        have hcast_le : i ≤ Fin.castLE hkn j0 := by
          change i.1 ≤ (Fin.castLE hkn j0).1
          exact Nat.le_pred_of_lt hi
        exact hlam hcast_le
      have hmul :=
        mul_le_mul_of_nonneg_left (hz_le_one i) hnonneg
      simpa [hi] using hmul
    · -- On the tail, the coefficient `λ i - t` is nonpositive and `z i` is nonnegative.
      have hnonpos : lam i - t ≤ 0 := ht_tail i (Nat.le_of_not_gt hi)
      have hmul : (lam i - t) * z i ≤ 0 := by
        nlinarith [hz_nonneg i, hnonpos]
      simpa [hi] using hmul
  have hsum_pointwise :
      ∑ i, (lam i - t) * z i ≤ ∑ i, if hi : i.1 < k then lam i - t else 0 := by
    exact Finset.sum_le_sum (fun i _ => hpointwise i)
  have hhead_sum :
      (∑ i, if hi : i.1 < k then lam i - t else 0) =
        ∑ j : Fin k, (lam (Fin.castLE hkn j) - t) := by
    -- Rewrite the head-only sum on `Fin N` as the direct sum over `Fin k`.
    have hcast :
        (∑ i : Fin N, if hi : i.1 < k then lam i - t else 0) =
          ∑ i : Fin (k + (N - k)),
            if hi : (finCongr (Nat.add_sub_of_le hkn) i).1 < k then
              lam (finCongr (Nat.add_sub_of_le hkn) i) - t
            else 0 := by
      symm
      simpa using
        (Equiv.sum_comp (finCongr (Nat.add_sub_of_le hkn))
          (fun i : Fin N => if hi : i.1 < k then lam i - t else 0))
    rw [hcast, Fin.sum_univ_add]
    have hhead_cast :
        ∀ j : Fin k,
          finCongr (Nat.add_sub_of_le hkn) (Fin.castAdd (N - k) j) = Fin.castLE hkn j := by
      intro j
      ext
      simp [finCongr, Fin.castLE]
    have htail_zero :
        ∀ j : Fin (N - k),
          (if hi : (finCongr (Nat.add_sub_of_le hkn) (Fin.natAdd k j)).1 < k then
              lam (finCongr (Nat.add_sub_of_le hkn) (Fin.natAdd k j)) - t
            else 0) = 0 := by
      intro j
      have hnot : ¬ (finCongr (Nat.add_sub_of_le hkn) (Fin.natAdd k j)).1 < k := by
        change ¬ k + j.1 < k
        omega
      simp [hnot]
    have hfirst :
        (∑ j : Fin k,
          if hi : (finCongr (Nat.add_sub_of_le hkn) (Fin.castAdd (N - k) j)).1 < k then
            lam (finCongr (Nat.add_sub_of_le hkn) (Fin.castAdd (N - k) j)) - t
          else 0) =
          ∑ j : Fin k, (lam (Fin.castLE hkn j) - t) := by
      rw [show (∑ j : Fin k,
        if hi : (finCongr (Nat.add_sub_of_le hkn) (Fin.castAdd (N - k) j)).1 < k then
          lam (finCongr (Nat.add_sub_of_le hkn) (Fin.castAdd (N - k) j)) - t
        else 0) =
      ∑ j : Fin k, (lam (Fin.castLE hkn j) - t) by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hlt : (finCongr (Nat.add_sub_of_le hkn) (Fin.castAdd (N - k) j)).1 < k := by
          rw [hhead_cast j]
          exact j.2
        simp [hhead_cast j, hlt]]
    have hsecond :
        (∑ j : Fin (N - k),
          if hi : (finCongr (Nat.add_sub_of_le hkn) (Fin.natAdd k j)).1 < k then
            lam (finCongr (Nat.add_sub_of_le hkn) (Fin.natAdd k j)) - t
          else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      exact htail_zero j
    rw [hfirst, hsecond, add_zero]
  have hsum_z :
      t * (∑ i, z i) = t * k := by
    rw [hz_sum]
  -- Subtract the threshold `t`, bound the head by `z i ≤ 1`, and discard the nonpositive tail.
  calc
    ∑ i, lam i * z i = ∑ i, ((lam i - t) * z i + t * z i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    _ = ∑ i, (lam i - t) * z i + t * (∑ i, z i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ ∑ j : Fin k, (lam (Fin.castLE hkn j) - t) + t * k := by
      exact add_le_add (hsum_pointwise.trans_eq hhead_sum) (le_of_eq hsum_z)
    _ = ∑ j : Fin k, lam (Fin.castLE hkn j) := by
      calc
        ∑ j : Fin k, (lam (Fin.castLE hkn j) - t) + t * k
            = (∑ j : Fin k, lam (Fin.castLE hkn j)) - ∑ _ : Fin k, t + t * k := by
                rw [Finset.sum_sub_distrib]
        _ = (∑ j : Fin k, lam (Fin.castLE hkn j)) - k * t + t * k := by simp
        _ = ∑ j : Fin k, lam (Fin.castLE hkn j) := by ring

/-- Left multiplication by a diagonal matrix keeps only the diagonal entries of the second factor
inside the trace. -/
lemma trace_diagonal_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (Y : Matrix ι ι ℝ) :
    Matrix.trace (Matrix.diagonal d * Y) = ∑ i, d i * Y i i := by
  -- Expand the trace and the diagonal multiplication entrywise.
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]

/-- A Hermitian trace-`k` positive contraction is dominated by the ordered sum of the first `k`
eigenvalues. -/
lemma trace_hermitian_mul_traceContraction_le_head_eigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B Y : Matrix ι ι ℝ} (hB : B.IsHermitian)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι)
    (hY_psd : PosSemidef Y)
    (hY_le_one : PosSemidef ((1 : Matrix ι ι ℝ) - Y))
    (htraceY : Matrix.trace Y = k) :
    Matrix.trace (B * Y) ≤ ∑ j : Fin k, hB.eigenvalues₀ (Fin.castLE hkn j) := by
  let N : ℕ := Fintype.card ι
  let U : Matrix.unitaryGroup ι ℝ := hB.eigenvectorUnitary
  let Uc : Matrix ι ι ℝ := U
  let Z : Matrix ι ι ℝ := star Uc * Y * Uc
  let e : Fin N ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin N)
  let z : Fin N → ℝ := fun i => Z (e i) (e i)
  have hdiagB : Uc * Matrix.diagonal hB.eigenvalues * star Uc = B := by
    -- Diagonalize `B` in its orthonormal eigenbasis.
    simpa [U, Uc, Unitary.conjStarAlgAut_apply] using hB.spectral_theorem.symm
  have htrace_diag :
      Matrix.trace (B * Y) = ∑ i, hB.eigenvalues i * Z i i := by
    -- Cycle the trace until the diagonal factor sits on the left.
    calc
      Matrix.trace (B * Y)
          = Matrix.trace (((Uc * Matrix.diagonal hB.eigenvalues * star Uc) * Y)) := by
              rw [hdiagB]
      _ = Matrix.trace (Uc * Matrix.diagonal hB.eigenvalues * (star Uc * Y)) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace ((star Uc * Y) * Uc * Matrix.diagonal hB.eigenvalues) := by
            rw [Matrix.trace_mul_cycle Uc (Matrix.diagonal hB.eigenvalues) (star Uc * Y)]
      _ = Matrix.trace ((star Uc * Y * Uc) * Matrix.diagonal hB.eigenvalues) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace (Matrix.diagonal hB.eigenvalues * Z) := by
            simpa [Z, Matrix.mul_assoc] using
              (Matrix.trace_mul_comm (star Uc * Y * Uc) (Matrix.diagonal hB.eigenvalues))
      _ = ∑ i, hB.eigenvalues i * Z i i := by
            simpa [Z] using trace_diagonal_mul hB.eigenvalues Z
  have hZ_psd : PosSemidef Z := by
    -- Unitary conjugation preserves positive semidefiniteness.
    simpa [Z, U, Uc] using hY_psd.conjTranspose_mul_mul_same Uc
  have hone_sub_Z : PosSemidef ((1 : Matrix ι ι ℝ) - Z) := by
    -- The same conjugation preserves the contraction slack `1 - Y`.
    have hconj : PosSemidef (star Uc * ((1 : Matrix ι ι ℝ) - Y) * Uc) := by
      simpa [U, Uc] using hY_le_one.conjTranspose_mul_mul_same Uc
    have hrewrite :
        star Uc * ((1 : Matrix ι ι ℝ) - Y) * Uc = (1 : Matrix ι ι ℝ) - Z := by
      calc
        star Uc * ((1 : Matrix ι ι ℝ) - Y) * Uc
            = ((star Uc * (1 : Matrix ι ι ℝ)) - star Uc * Y) * Uc := by
                rw [Matrix.mul_sub]
        _ = (star Uc * Uc) - star Uc * Y * Uc := by
              rw [Matrix.sub_mul]
              simp [Matrix.mul_assoc]
        _ = (1 : Matrix ι ι ℝ) - Z := by
              simp [Z, U, Uc, Matrix.mul_assoc]
    exact hrewrite ▸ hconj
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    simpa [z] using hZ_psd.diag_nonneg (i := e i)
  have hz_le_one : ∀ i, z i ≤ 1 := by
    intro i
    have hdiag := hone_sub_Z.diag_nonneg (i := e i)
    simpa [z, Z] using hdiag
  have htraceZ : Matrix.trace Z = k := by
    -- Conjugating by the unitary eigenbasis does not change the trace.
    calc
      Matrix.trace Z = Matrix.trace (Uc * star Uc * Y) := by
        simpa [Z, Matrix.mul_assoc] using Matrix.trace_mul_cycle (star Uc) Y Uc
      _ = Matrix.trace Y := by
            simp [U, Uc, Matrix.mul_assoc]
      _ = k := htraceY
  have hz_sum : ∑ i, z i = k := by
    -- Reindex the diagonal sum back to `Fin N`.
    calc
      ∑ i : Fin N, z i = ∑ j : ι, Z j j := by
        simpa [z] using (Equiv.sum_comp e (fun j : ι => Z j j))
      _ = Matrix.trace Z := by simp [Matrix.trace]
      _ = k := htraceZ
  have htrace_reindex :
      Matrix.trace (B * Y) = ∑ i : Fin N, hB.eigenvalues₀ i * z i := by
    -- Reindex the spectral trace identity onto the ordered `eigenvalues₀` indexing set.
    calc
      Matrix.trace (B * Y) = ∑ j : ι, hB.eigenvalues j * Z j j := htrace_diag
      _ = ∑ i : Fin N, hB.eigenvalues (e i) * Z (e i) (e i) := by
            symm
            simpa using (Equiv.sum_comp e (fun j : ι => hB.eigenvalues j * Z j j))
      _ = ∑ i : Fin N, hB.eigenvalues₀ i * z i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            change hB.eigenvalues₀ (e.symm (e i)) * Z (e i) (e i) = hB.eigenvalues₀ i * z i
            rw [e.symm_apply_apply]
  -- Apply the scalar threshold lemma to the diagonal entries of the conjugated contraction.
  calc
    Matrix.trace (B * Y) = ∑ i : Fin N, hB.eigenvalues₀ i * z i := htrace_reindex
    _ ≤ ∑ j : Fin k, hB.eigenvalues₀ (Fin.castLE hkn j) := by
          exact weighted_sum_le_head_sum_of_unit_interval_mass hk1 hkn
            hB.eigenvalues₀ z hB.eigenvalues₀_antitone hz_nonneg hz_le_one hz_sum

/-- Splitting a block-dilation eigenvector along the left and right summands yields the usual
singular-vector equations. -/
lemma blockDilation_eigenvector_split
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ)
    (hB : (Matrix.fromBlocks (0 : Matrix m m ℝ) A A.transpose (0 : Matrix n n ℝ)).IsHermitian)
    (i : Sum m n) :
    let w : Sum m n → ℝ := hB.eigenvectorBasis i
    let u : m → ℝ := fun a => w (Sum.inl a)
    let v : n → ℝ := fun b => w (Sum.inr b)
    A *ᵥ v = hB.eigenvalues i • u ∧
      A.transpose *ᵥ u = hB.eigenvalues i • v := by
  -- Route correction: read the block-dilation eigenvector equation componentwise on the two
  -- summands instead of trying to diagonalize `A` directly.
  dsimp
  have hmul := hB.mulVec_eigenvectorBasis i
  constructor
  · ext a
    have hcoord := congrArg (fun z : Sum m n → ℝ => z (Sum.inl a)) hmul
    simpa [Matrix.fromBlocks_mulVec] using hcoord
  · ext b
    have hcoord := congrArg (fun z : Sum m n → ℝ => z (Sum.inr b)) hmul
    simpa [Matrix.fromBlocks_mulVec] using hcoord

/-- For nonzero block-dilation eigenvalue sums, the left and right split pieces of orthonormal
eigenvectors each carry exactly half of the total mass. -/
lemma blockDilation_split_dot_half
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ)
    (hB : (Matrix.fromBlocks (0 : Matrix m m ℝ) A A.transpose (0 : Matrix n n ℝ)).IsHermitian)
    {i j : Sum m n}
    (hsum : hB.eigenvalues i + hB.eigenvalues j ≠ 0) :
    let wi : Sum m n → ℝ := hB.eigenvectorBasis i
    let wj : Sum m n → ℝ := hB.eigenvectorBasis j
    let ui : m → ℝ := fun a => wi (Sum.inl a)
    let vi : n → ℝ := fun b => wi (Sum.inr b)
    let uj : m → ℝ := fun a => wj (Sum.inl a)
    let vj : n → ℝ := fun b => wj (Sum.inr b)
    (dotProduct ui uj = if i = j then (1 / 2 : ℝ) else 0) ∧
      (dotProduct vi vj = if i = j then (1 / 2 : ℝ) else 0) := by
  classical
  dsimp
  obtain ⟨hAvi, hAtui⟩ := blockDilation_eigenvector_split A hB i
  obtain ⟨hAvj, hAtuj⟩ := blockDilation_eigenvector_split A hB j
  let ui : m → ℝ := fun a => hB.eigenvectorBasis i (Sum.inl a)
  let vi : n → ℝ := fun b => hB.eigenvectorBasis i (Sum.inr b)
  let uj : m → ℝ := fun a => hB.eigenvectorBasis j (Sum.inl a)
  let vj : n → ℝ := fun b => hB.eigenvectorBasis j (Sum.inr b)
  have horth :
      dotProduct ui uj + dotProduct vi vj =
        if i = j then 1 else 0 := by
    -- Split the orthonormal eigenvector inner product across the left and right summands.
    calc
      dotProduct ui uj + dotProduct vi vj =
          dotProduct (hB.eigenvectorBasis i) (hB.eigenvectorBasis j) := by
            simp [ui, uj, vi, vj, dotProduct, Fintype.sum_sum_type]
      _ = dotProduct (hB.eigenvectorBasis j) (hB.eigenvectorBasis i) := by
            rw [dotProduct_comm]
      _ = if i = j then 1 else 0 := by
            simpa [EuclideanSpace.inner_eq_star_dotProduct] using
              (orthonormal_iff_ite.mp hB.eigenvectorBasis.orthonormal i j)
  have hleft_eq :
      hB.eigenvalues j * dotProduct ui uj =
        hB.eigenvalues i * dotProduct vi vj := by
    -- Route correction: compare the two split pieces through the block equations instead of trying
    -- to read off their norms directly from the zero-eigenvalue sector.
    calc
      hB.eigenvalues j * dotProduct ui uj = dotProduct ui (A *ᵥ vj) := by
        rw [hAvj]
        simpa [ui, uj, dotProduct, smul_eq_mul] using (dotProduct_smul (hB.eigenvalues j) ui uj).symm
      _ =
        dotProduct (A.transpose *ᵥ ui) vj := by
            rw [dotProduct_mulVec, mulVec_transpose]
      _ =
        hB.eigenvalues i * dotProduct vi vj := by
            rw [hAtui]
            simpa [vi, vj, dotProduct, smul_eq_mul] using (smul_dotProduct (hB.eigenvalues i) vi vj)
  have hright_eq :
      hB.eigenvalues i * dotProduct ui uj =
        hB.eigenvalues j * dotProduct vi vj := by
    -- The symmetric transpose identity gives the complementary scalar relation.
    calc
      hB.eigenvalues i * dotProduct ui uj = dotProduct (A *ᵥ vi) uj := by
            rw [hAvi]
            simpa [ui, uj, dotProduct, smul_eq_mul] using
              (smul_dotProduct (hB.eigenvalues i) ui uj).symm
      _ =
        dotProduct vi (A.transpose *ᵥ uj) := by
            rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
      _ =
        hB.eigenvalues j * dotProduct vi vj := by
            rw [hAtuj]
            simpa [vi, vj, dotProduct, smul_eq_mul] using (dotProduct_smul (hB.eigenvalues j) vi vj)
  have hsplit_eq :
      dotProduct ui uj = dotProduct vi vj := by
    have hmulzero :
        (hB.eigenvalues i + hB.eigenvalues j) *
            (dotProduct ui uj - dotProduct vi vj) = 0 := by
      nlinarith [hleft_eq, hright_eq]
    have hdiff_zero := (mul_eq_zero.mp hmulzero).resolve_left hsum
    exact sub_eq_zero.mp hdiff_zero
  have hhalf_left :
      dotProduct ui uj =
        (if i = j then (1 / 2 : ℝ) else 0) := by
    -- Once the split pieces are equal, the orthonormality sum forces each to be half.
    have hdouble : 2 * dotProduct ui uj = if i = j then 1 else 0 := by
      calc
        2 * dotProduct ui uj = dotProduct ui uj + dotProduct ui uj := by ring
        _ = dotProduct ui uj + dotProduct vi vj := by rw [hsplit_eq]
        _ = if i = j then 1 else 0 := horth
    by_cases hij : i = j
    · simp [hij] at hdouble ⊢
      nlinarith
    · simp [hij] at hdouble ⊢
      nlinarith
  have hhalf_right :
      dotProduct vi vj =
        (if i = j then (1 / 2 : ℝ) else 0) := by
    simpa [hsplit_eq] using hhalf_left
  exact ⟨hhalf_left, hhalf_right⟩

/-- The negative eigenspaces of the block dilation contribute an orthonormal family on the right
block, so there are at most `card n` negative eigenvalues. -/
lemma blockDilation_negative_eigenvalue_count_le_card_right
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ)
    (hB : (Matrix.fromBlocks (0 : Matrix m m ℝ) A A.transpose (0 : Matrix n n ℝ)).IsHermitian) :
    Fintype.card {i : Sum m n // hB.eigenvalues i < 0} ≤ Fintype.card n := by
  classical
  let negRight : {i : Sum m n // hB.eigenvalues i < 0} → EuclideanSpace ℝ n :=
    fun i => WithLp.toLp 2 (fun b => Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr b))
  have hnegRight_pairwise :
      Pairwise (fun i j : {i : Sum m n // hB.eigenvalues i < 0} =>
        inner (𝕜 := ℝ) (negRight i) (negRight j) = 0) := by
    -- Route correction: package the negative spectral family on the right block and use
    -- `blockDilation_split_dot_half` to get orthonormality directly, avoiding coefficient
    -- bookkeeping in the whole block basis.
    intro i j hij
    have hsum : hB.eigenvalues i.1 + hB.eigenvalues j.1 ≠ 0 := by
      linarith [i.2, j.2]
    obtain ⟨_, hright⟩ := blockDilation_split_dot_half A hB hsum
    have hright' :
        dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
            (fun b => hB.eigenvectorBasis j.1 (Sum.inr b)) =
          (if i = j then (1 / 2 : ℝ) else 0) := by
      simpa [Subtype.ext_iff] using hright
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hinner_expand :
        inner (𝕜 := ℝ) (negRight i) (negRight j) =
          2 * dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
                (fun b => hB.eigenvectorBasis j.1 (Sum.inr b)) := by
      calc
        inner (𝕜 := ℝ) (negRight i) (negRight j)
            = dotProduct (fun b => Real.sqrt 2 * hB.eigenvectorBasis j.1 (Sum.inr b))
                (fun b => Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr b)) := by
                  simp [negRight, EuclideanSpace.inner_toLp_toLp]
        _ = ∑ x, (Real.sqrt 2 * hB.eigenvectorBasis j.1 (Sum.inr x)) *
              (Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr x)) := by
                simp [dotProduct]
        _ = ∑ x, 2 * (hB.eigenvectorBasis i.1 (Sum.inr x) *
              hB.eigenvectorBasis j.1 (Sum.inr x)) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                calc
                  (Real.sqrt 2 * hB.eigenvectorBasis j.1 (Sum.inr x)) *
                      (Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr x))
                      = (Real.sqrt 2 * Real.sqrt 2) *
                          (hB.eigenvectorBasis i.1 (Sum.inr x) *
                            hB.eigenvectorBasis j.1 (Sum.inr x)) := by ring
                  _ = 2 * (hB.eigenvectorBasis i.1 (Sum.inr x) *
                        hB.eigenvectorBasis j.1 (Sum.inr x)) := by rw [hsqrt]
        _ = 2 * dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
              (fun b => hB.eigenvectorBasis j.1 (Sum.inr b)) := by
                simp [dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    rw [hinner_expand, hright', if_neg hij]
    norm_num
  have hnegRight_ne_zero :
      ∀ i : {i : Sum m n // hB.eigenvalues i < 0}, negRight i ≠ 0 := by
    intro i
    have hsum : hB.eigenvalues i.1 + hB.eigenvalues i.1 ≠ 0 := by
      linarith [i.2]
    obtain ⟨_, hright⟩ := blockDilation_split_dot_half A hB hsum
    have hright' :
        dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
            (fun b => hB.eigenvectorBasis i.1 (Sum.inr b)) = (1 / 2 : ℝ) := by
      simpa using hright
    exact fun hzero => by
      have hfunzero :
          (fun b => Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr b)) = 0 := by
        exact (WithLp.toLp_eq_zero (p := (2 : ENNReal))).mp hzero
      have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
      have hraw_zero :
          (fun b => hB.eigenvectorBasis i.1 (Sum.inr b)) = 0 := by
        funext b
        have hb := congrArg (fun f : n → ℝ => f b) hfunzero
        exact (mul_eq_zero.mp hb).resolve_left hsqrt_ne
      have : (1 / 2 : ℝ) = 0 := by simpa [hraw_zero] using hright'
      norm_num at this
  have hnegRight_li : LinearIndependent ℝ negRight :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hnegRight_ne_zero hnegRight_pairwise
  -- The orthonormal family lives in `n → ℝ`, whose dimension is `card n`.
  exact (LinearIndependent.fintype_card_le_finrank hnegRight_li).trans_eq
    (finrank_euclideanSpace (𝕜 := ℝ) (ι := n))

/-- The previous cardinal bound reindexed onto the ordered eigenvalue indexing. -/
lemma blockDilation_negative_eigenvalue_count_le_card_right_ordered
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ)
    (hB : (Matrix.fromBlocks (0 : Matrix m m ℝ) A A.transpose (0 : Matrix n n ℝ)).IsHermitian) :
    Fintype.card {i : Fin (Fintype.card (Sum m n)) // hB.eigenvalues₀ i < 0} ≤ Fintype.card n := by
  classical
  let e : Fin (Fintype.card (Sum m n)) ≃ Sum m n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let eNeg :
      {i : Fin (Fintype.card (Sum m n)) // hB.eigenvalues₀ i < 0} ≃
        {i : Sum m n // hB.eigenvalues i < 0} :=
    { toFun := fun i => ⟨e i.1, by simpa [Matrix.IsHermitian.eigenvalues, e] using i.2⟩
      invFun := fun i => ⟨e.symm i.1, by simpa [Matrix.IsHermitian.eigenvalues, e] using i.2⟩
      left_inv := by
        intro i
        ext
        simp [e]
      right_inv := by
        intro i
        ext
        simp [e] }
  have hcard :
      Fintype.card {i : Fin (Fintype.card (Sum m n)) // hB.eigenvalues₀ i < 0} =
        Fintype.card {i : Sum m n // hB.eigenvalues i < 0} :=
    Fintype.card_congr eNeg
  rw [hcard]
  exact blockDilation_negative_eigenvalue_count_le_card_right A hB

/-- If `r ≤ k ≤ n`, then the eventual kernel padding width `k - r` fits inside the right nullity
bound `n - r`. -/
lemma kernel_padding_le_right_nullity {r k n : ℕ}
    (hrk : r ≤ k) (hkn : k ≤ n) :
    k - r ≤ n - r := by
  -- This is the arithmetic bound needed when the positive block uses `r` columns.
  omega

/-- If `r ≤ k ≤ n ≤ m`, then the same padding width also fits inside the left nullity bound
`m - r`. -/
lemma kernel_padding_le_left_nullity {r k n m : ℕ}
    (hrk : r ≤ k) (hkn : k ≤ n) (hnm : n ≤ m) :
    k - r ≤ m - r := by
  -- The left kernel has at least as much room because `m` dominates `n`.
  omega

/-- Appending an orthonormal contribution block and an orthonormal zero-contributing padding block
produces a witness in the Ky Fan frame set. -/
lemma splitFrameWitness_mem_kyFanWitnessSet
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) {k p : ℕ} (hp : p ≤ k) {headSum : ℝ}
    (Upos : Matrix m (Fin p) ℝ) (Vpos : Matrix n (Fin p) ℝ)
    (Uker : Matrix m (Fin (k - p)) ℝ) (Vker : Matrix n (Fin (k - p)) ℝ)
    (hUpos : Upos.transpose * Upos = 1)
    (hVpos : Vpos.transpose * Vpos = 1)
    (hUker : Uker.transpose * Uker = 1)
    (hVker : Vker.transpose * Vker = 1)
    (hcrossU : Upos.transpose * Uker = 0)
    (hcrossV : Vpos.transpose * Vker = 0)
    (htracePos : Matrix.trace (Upos.transpose * A * Vpos) = headSum)
    (htraceKer : Matrix.trace (Uker.transpose * A * Vker) = 0) :
    headSum ∈ {r : ℝ | ∃ U : Matrix m (Fin k) ℝ, ∃ V : Matrix n (Fin k) ℝ,
      U.transpose * U = 1 ∧ V.transpose * V = 1 ∧
      r = Matrix.trace (U.transpose * A * V)} := by
  classical
  let U0 : Matrix m (Fin p ⊕ Fin (k - p)) ℝ := Upos.fromCols Uker
  let V0 : Matrix n (Fin p ⊕ Fin (k - p)) ℝ := Vpos.fromCols Vker
  let e : Fin p ⊕ Fin (k - p) ≃ Fin k :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hp))
  let U : Matrix m (Fin k) ℝ := fun i j => U0 i (e.symm j)
  let V : Matrix n (Fin k) ℝ := fun i j => V0 i (e.symm j)
  have hcrossU' : Uker.transpose * Upos = 0 := by
    -- The lower-left Gram block is the transpose of the assumed upper-right zero block.
    simpa using congrArg Matrix.transpose hcrossU
  have hcrossV' : Vker.transpose * Vpos = 0 := by
    -- The same transpose symmetry gives the vanishing cross term on the `V` side.
    simpa using congrArg Matrix.transpose hcrossV
  have hU0 : U0.transpose * U0 = 1 := by
    -- The concatenated `U`-family has block-diagonal Gram matrix because the cross terms vanish.
    calc
      U0.transpose * U0 =
          Matrix.fromBlocks (Upos.transpose * Upos) (Upos.transpose * Uker)
            (Uker.transpose * Upos) (Uker.transpose * Uker) := by
            simp [U0, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols]
      _ = Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℝ) 0 0
            (1 : Matrix (Fin (k - p)) (Fin (k - p)) ℝ) := by
            rw [hUpos, hUker, hcrossU, hcrossU']
      _ = (1 : Matrix (Fin p ⊕ Fin (k - p)) (Fin p ⊕ Fin (k - p)) ℝ) := by
            ext a b <;> cases a <;> cases b <;> simp [Matrix.one_apply]
  have hV0 : V0.transpose * V0 = 1 := by
    -- The same block-Gram computation works for the `V`-family.
    calc
      V0.transpose * V0 =
          Matrix.fromBlocks (Vpos.transpose * Vpos) (Vpos.transpose * Vker)
            (Vker.transpose * Vpos) (Vker.transpose * Vker) := by
            simp [V0, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols]
      _ = Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℝ) 0 0
            (1 : Matrix (Fin (k - p)) (Fin (k - p)) ℝ) := by
            rw [hVpos, hVker, hcrossV, hcrossV']
      _ = (1 : Matrix (Fin p ⊕ Fin (k - p)) (Fin p ⊕ Fin (k - p)) ℝ) := by
            ext a b <;> cases a <;> cases b <;> simp [Matrix.one_apply]
  have hU : U.transpose * U = 1 := by
    -- Reindexing the columns from `Fin p ⊕ Fin (k-p)` to `Fin k` preserves the Gram matrix.
    ext a b
    have h :=
      congrArg
        (fun M : Matrix (Fin p ⊕ Fin (k - p)) (Fin p ⊕ Fin (k - p)) ℝ =>
          M (e.symm a) (e.symm b)) hU0
    simpa [U, Matrix.mul_apply, Matrix.one_apply] using h
  have hV : V.transpose * V = 1 := by
    -- The same column reindexing argument preserves the `V` Gram matrix.
    ext a b
    have h :=
      congrArg
        (fun M : Matrix (Fin p ⊕ Fin (k - p)) (Fin p ⊕ Fin (k - p)) ℝ =>
          M (e.symm a) (e.symm b)) hV0
    simpa [V, Matrix.mul_apply, Matrix.one_apply] using h
  have hAV0 :
      A * V0 = (A * Vpos).fromCols (A * Vker) := by
    -- Multiplication by `A` distributes over the concatenated column blocks.
    ext i j
    cases j with
    | inl j =>
        simp [V0, Matrix.fromCols_apply_inl]
    | inr j =>
        simp [V0, Matrix.fromCols_apply_inr]
  have htrace0 : Matrix.trace (U0.transpose * A * V0) = headSum := by
    -- The trace of the concatenated witness splits across the two diagonal blocks.
    have hblock :
        U0.transpose * A * V0 =
          Matrix.fromBlocks (Upos.transpose * A * Vpos) (Upos.transpose * A * Vker)
            (Uker.transpose * A * Vpos) (Uker.transpose * A * Vker) := by
      calc
        U0.transpose * A * V0 = U0.transpose * (A * V0) := by
          rw [Matrix.mul_assoc]
        _ = U0.transpose * ((A * Vpos).fromCols (A * Vker)) := by
          rw [hAV0]
        _ =
            Matrix.fromBlocks (Upos.transpose * (A * Vpos)) (Upos.transpose * (A * Vker))
              (Uker.transpose * (A * Vpos)) (Uker.transpose * (A * Vker)) := by
              simp [U0, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols]
        _ =
            Matrix.fromBlocks (Upos.transpose * A * Vpos) (Upos.transpose * A * Vker)
              (Uker.transpose * A * Vpos) (Uker.transpose * A * Vker) := by
              simp [Matrix.mul_assoc]
    rw [hblock, trace_fromBlocks, htracePos, htraceKer, add_zero]
  have htrace :
      Matrix.trace (U.transpose * A * V) = headSum := by
    -- Reindexing the columns only permutes the trace sum over the diagonal.
    calc
      Matrix.trace (U.transpose * A * V)
          = ∑ j : Fin k, (U.transpose * A * V) j j := by
              simp [Matrix.trace]
      _ = ∑ c : Fin p ⊕ Fin (k - p), (U0.transpose * A * V0) c c := by
            symm
            simpa [U, V, Matrix.mul_apply] using
              (Equiv.sum_comp e
                fun j : Fin k => (U0.transpose * A * V0) (e.symm j) (e.symm j))
      _ = Matrix.trace (U0.transpose * A * V0) := by
            simp [Matrix.trace]
      _ = headSum := htrace0
  refine ⟨U, V, hU, hV, htrace.symm⟩

/-- The matrix whose columns are an orthonormal Euclidean family has identity Gram matrix. -/
lemma matrix_of_orthonormal_transpose_mul_self
    {m : Type*} [Fintype m] [DecidableEq m] {q : ℕ}
    (u : Fin q → EuclideanSpace ℝ m) (hu : Orthonormal ℝ u) :
    let U : Matrix m (Fin q) ℝ := fun i j => (u j).ofLp i
    U.transpose * U = 1 := by
  -- Route correction: encode orthonormal columns through Euclidean vectors first, then read the
  -- matrix Gram entries as dot products instead of expanding matrix products by hand each time.
  dsimp
  ext i j
  calc
    (∑ x, (u i).ofLp x * (u j).ofLp x) = dotProduct (u i).ofLp (u j).ofLp := by
      simp [dotProduct]
    _ = dotProduct (u j).ofLp (u i).ofLp := by
      rw [dotProduct_comm]
    _ = if i = j then 1 else 0 := by
      simpa [EuclideanSpace.inner_eq_star_dotProduct] using
        (orthonormal_iff_ite.mp hu i j)
    _ = (1 : Matrix (Fin q) (Fin q) ℝ) i j := by
      simp [Matrix.one_apply]

/-- The Euclidean range of `A` has dimension `A.rank`. -/
lemma toEuclideanLin_range_finrank_eq_rank
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) :
    Module.finrank ℝ ↥(LinearMap.range (Matrix.toEuclideanLin A)) = A.rank := by
  let em := WithLp.linearEquiv 2 ℝ (m → ℝ)
  let en := WithLp.linearEquiv 2 ℝ (n → ℝ)
  have hcomp :
      Matrix.toEuclideanLin A =
        em.symm.toLinearMap.comp (A.mulVecLin.comp en.toLinearMap) := by
    -- `toEuclideanLin` is just `mulVecLin` transported across the `WithLp` linear equivalences.
    ext v i
    rfl
  -- After identifying the range as a linear-equivalence image of `A.mulVecLin.range`, finrank is
  -- preserved exactly.
  rw [hcomp, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  rw [LinearEquiv.finrank_map_eq]
  simp [Matrix.rank]

/-- The Euclidean kernel of `A` has dimension `card n - A.rank`. -/
lemma toEuclideanLin_ker_finrank_eq_card_sub_rank
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) :
    Module.finrank ℝ ↥(LinearMap.ker (Matrix.toEuclideanLin A)) = Fintype.card n - A.rank := by
  have hrange : Module.finrank ℝ ↥(LinearMap.range (Matrix.toEuclideanLin A)) = A.rank :=
    toEuclideanLin_range_finrank_eq_rank A
  have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.toEuclideanLin A)
  -- This is just rank-nullity on `EuclideanSpace ℝ n`.
  rw [hrange, finrank_euclideanSpace] at hsum
  have : Module.finrank ℝ ↥(LinearMap.ker (Matrix.toEuclideanLin A)) =
      Fintype.card n - A.rank := by
    omega
  exact this

/-- The orthogonal complement of an orthonormal `p`-family in `ℝ^m` has dimension `card m - p`. -/
lemma orthogonal_complement_finrank_of_orthonormal
    {m : Type*} [Fintype m] [DecidableEq m] {p : ℕ}
    (u : Fin p → EuclideanSpace ℝ m) (hu : Orthonormal ℝ u) :
    Module.finrank ℝ ↥(Submodule.span ℝ (Set.range u))ᗮ = Fintype.card m - p := by
  let K : Submodule ℝ (EuclideanSpace ℝ m) := Submodule.span ℝ (Set.range u)
  have hK : Module.finrank ℝ ↥K = p := by
    -- The span of an orthonormal family has the expected dimension.
    simpa [K] using (finrank_span_eq_card hu.linearIndependent)
  have hp : p ≤ Fintype.card m := by
    have hle : Module.finrank ℝ ↥K ≤ Module.finrank ℝ (EuclideanSpace ℝ m) :=
      Submodule.finrank_le K
    rw [hK, finrank_euclideanSpace] at hle
    exact hle
  have hsum : p + Module.finrank ℝ ↥Kᗮ = Fintype.card m := by
    -- Finite-dimensional orthogonal decomposition gives the complementary dimension formula.
    simpa [hK, finrank_euclideanSpace] using (Submodule.finrank_add_finrank_orthogonal K)
  have : Module.finrank ℝ ↥Kᗮ = Fintype.card m - p := by
    omega
  simpa [K] using this

/-- Positive block-dilation eigenvalues contribute an orthonormal family inside
`range (Matrix.toEuclideanLin A.transpose)`, so there are at most `A.rank` of them. -/
lemma blockDilation_positive_eigenvalue_count_le_rank
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ)
    (hB : (Matrix.fromBlocks (0 : Matrix m m ℝ) A A.transpose (0 : Matrix n n ℝ)).IsHermitian) :
    Fintype.card {i : Sum m n // 0 < hB.eigenvalues i} ≤ A.rank := by
  classical
  let posRightRaw : {i : Sum m n // 0 < hB.eigenvalues i} → EuclideanSpace ℝ n :=
    fun i => WithLp.toLp 2 (fun b => Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr b))
  have hpos_mem :
      ∀ i : {i : Sum m n // 0 < hB.eigenvalues i},
        posRightRaw i ∈ LinearMap.range (Matrix.toEuclideanLin A.transpose) := by
    intro i
    obtain ⟨_, hAtu⟩ := blockDilation_eigenvector_split A hB i.1
    rw [LinearMap.mem_range]
    refine ⟨WithLp.toLp 2 (fun a =>
      (Real.sqrt 2 / hB.eigenvalues i.1) * hB.eigenvectorBasis i.1 (Sum.inl a)), ?_⟩
    ext b
    have hi0 : hB.eigenvalues i.1 ≠ 0 := by linarith [i.2]
    calc
      (A.transpose *ᵥ
          fun a => (Real.sqrt 2 / hB.eigenvalues i.1) * hB.eigenvectorBasis i.1 (Sum.inl a)) b
          = (Real.sqrt 2 / hB.eigenvalues i.1) *
              (A.transpose *ᵥ fun a => hB.eigenvectorBasis i.1 (Sum.inl a)) b := by
                simpa [dotProduct, smul_eq_mul] using
                  (dotProduct_smul (Real.sqrt 2 / hB.eigenvalues i.1)
                    (fun j => A j b) (fun a => hB.eigenvectorBasis i.1 (Sum.inl a)))
      _ = Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr b) := by
            rw [hAtu]
            simp [smul_eq_mul, div_eq_mul_inv, hi0, mul_assoc, mul_left_comm, mul_comm]
  let posRight :
      {i : Sum m n // 0 < hB.eigenvalues i} →
        ↥(LinearMap.range (Matrix.toEuclideanLin A.transpose)) :=
    fun i => ⟨posRightRaw i, hpos_mem i⟩
  have hpair_raw :
      Pairwise (fun i j : {i : Sum m n // 0 < hB.eigenvalues i} =>
        inner (𝕜 := ℝ) (posRightRaw i) (posRightRaw j) = 0) := by
    -- On the positive sector, `blockDilation_split_dot_half` again turns the right split pieces
    -- into an orthonormal family after the `√2` normalization.
    intro i j hij
    have hsum : hB.eigenvalues i.1 + hB.eigenvalues j.1 ≠ 0 := by
      linarith [i.2, j.2]
    obtain ⟨_, hright⟩ := blockDilation_split_dot_half A hB hsum
    have hright' :
        dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
            (fun b => hB.eigenvectorBasis j.1 (Sum.inr b)) =
          (if i = j then (1 / 2 : ℝ) else 0) := by
      simpa [Subtype.ext_iff] using hright
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hinner_expand :
        inner (𝕜 := ℝ) (posRightRaw i) (posRightRaw j) =
          2 * dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
                (fun b => hB.eigenvectorBasis j.1 (Sum.inr b)) := by
      calc
        inner (𝕜 := ℝ) (posRightRaw i) (posRightRaw j)
            = dotProduct (fun b => Real.sqrt 2 * hB.eigenvectorBasis j.1 (Sum.inr b))
                (fun b => Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr b)) := by
                  simp [posRightRaw, EuclideanSpace.inner_toLp_toLp]
        _ = ∑ x, (Real.sqrt 2 * hB.eigenvectorBasis j.1 (Sum.inr x)) *
              (Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr x)) := by
                simp [dotProduct]
        _ = ∑ x, 2 * (hB.eigenvectorBasis i.1 (Sum.inr x) *
              hB.eigenvectorBasis j.1 (Sum.inr x)) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                calc
                  (Real.sqrt 2 * hB.eigenvectorBasis j.1 (Sum.inr x)) *
                      (Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr x))
                      = (Real.sqrt 2 * Real.sqrt 2) *
                          (hB.eigenvectorBasis i.1 (Sum.inr x) *
                            hB.eigenvectorBasis j.1 (Sum.inr x)) := by ring
                  _ = 2 * (hB.eigenvectorBasis i.1 (Sum.inr x) *
                        hB.eigenvectorBasis j.1 (Sum.inr x)) := by rw [hsqrt]
        _ = 2 * dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
              (fun b => hB.eigenvectorBasis j.1 (Sum.inr b)) := by
                simp [dotProduct, Finset.mul_sum]
    rw [hinner_expand, hright', if_neg hij]
    norm_num
  have hne_raw :
      ∀ i : {i : Sum m n // 0 < hB.eigenvalues i}, posRightRaw i ≠ 0 := by
    intro i
    have hsum : hB.eigenvalues i.1 + hB.eigenvalues i.1 ≠ 0 := by
      linarith [i.2]
    obtain ⟨_, hright⟩ := blockDilation_split_dot_half A hB hsum
    have hright' :
        dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
            (fun b => hB.eigenvectorBasis i.1 (Sum.inr b)) = (1 / 2 : ℝ) := by
      simpa using hright
    exact fun hzero => by
      have hfunzero :
          (fun b => Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr b)) = 0 := by
        exact (WithLp.toLp_eq_zero (p := (2 : ENNReal))).mp hzero
      have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
      have hraw_zero :
          (fun b => hB.eigenvectorBasis i.1 (Sum.inr b)) = 0 := by
        funext b
        have hb := congrArg (fun f : n → ℝ => f b) hfunzero
        exact (mul_eq_zero.mp hb).resolve_left hsqrt_ne
      have : (1 / 2 : ℝ) = 0 := by simpa [hraw_zero] using hright'
      norm_num at this
  have hpair :
      Pairwise (fun i j : {i : Sum m n // 0 < hB.eigenvalues i} =>
        inner (𝕜 := ℝ) (posRight i) (posRight j) = 0) := by
    intro i j hij
    simpa [posRight] using hpair_raw hij
  have hne :
      ∀ i : {i : Sum m n // 0 < hB.eigenvalues i}, posRight i ≠ 0 := by
    intro i
    intro hzero
    have hval : posRightRaw i = 0 := by
      simpa [posRight] using congrArg Subtype.val hzero
    exact hne_raw i hval
  have hli : LinearIndependent ℝ posRight :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hne hpair
  have hrange :
      Module.finrank ℝ ↥(LinearMap.range (Matrix.toEuclideanLin A.transpose)) = A.rank := by
    simpa using toEuclideanLin_range_finrank_eq_rank A.transpose
  exact (LinearIndependent.fintype_card_le_finrank hli).trans_eq hrange

/-- Negative block-dilation eigenvalues satisfy the same rank-sized count bound on the right
split sector. -/
lemma blockDilation_negative_eigenvalue_count_le_rank
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ)
    (hB : (Matrix.fromBlocks (0 : Matrix m m ℝ) A A.transpose (0 : Matrix n n ℝ)).IsHermitian) :
    Fintype.card {i : Sum m n // hB.eigenvalues i < 0} ≤ A.rank := by
  classical
  let negRightRaw : {i : Sum m n // hB.eigenvalues i < 0} → EuclideanSpace ℝ n :=
    fun i => WithLp.toLp 2 (fun b => Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr b))
  have hneg_mem :
      ∀ i : {i : Sum m n // hB.eigenvalues i < 0},
        negRightRaw i ∈ LinearMap.range (Matrix.toEuclideanLin A.transpose) := by
    intro i
    obtain ⟨_, hAtu⟩ := blockDilation_eigenvector_split A hB i.1
    rw [LinearMap.mem_range]
    refine ⟨WithLp.toLp 2 (fun a =>
      (Real.sqrt 2 / hB.eigenvalues i.1) * hB.eigenvectorBasis i.1 (Sum.inl a)), ?_⟩
    ext b
    have hi0 : hB.eigenvalues i.1 ≠ 0 := by linarith [i.2]
    calc
      (A.transpose *ᵥ
          fun a => (Real.sqrt 2 / hB.eigenvalues i.1) * hB.eigenvectorBasis i.1 (Sum.inl a)) b
          = (Real.sqrt 2 / hB.eigenvalues i.1) *
              (A.transpose *ᵥ fun a => hB.eigenvectorBasis i.1 (Sum.inl a)) b := by
                simpa [dotProduct, smul_eq_mul] using
                  (dotProduct_smul (Real.sqrt 2 / hB.eigenvalues i.1)
                    (fun j => A j b) (fun a => hB.eigenvectorBasis i.1 (Sum.inl a)))
      _ = Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr b) := by
            rw [hAtu]
            simp [smul_eq_mul, div_eq_mul_inv, hi0, mul_assoc, mul_left_comm, mul_comm]
  let negRight :
      {i : Sum m n // hB.eigenvalues i < 0} →
        ↥(LinearMap.range (Matrix.toEuclideanLin A.transpose)) :=
    fun i => ⟨negRightRaw i, hneg_mem i⟩
  have hpair_raw :
      Pairwise (fun i j : {i : Sum m n // hB.eigenvalues i < 0} =>
        inner (𝕜 := ℝ) (negRightRaw i) (negRightRaw j) = 0) := by
    -- Route correction: keep the same right-split orthonormal family as before, but now record
    -- that it lies in the smaller `range (Aᵀ)` subspace so the bound improves from `card n`
    -- to `A.rank`.
    intro i j hij
    have hsum : hB.eigenvalues i.1 + hB.eigenvalues j.1 ≠ 0 := by
      linarith [i.2, j.2]
    obtain ⟨_, hright⟩ := blockDilation_split_dot_half A hB hsum
    have hright' :
        dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
            (fun b => hB.eigenvectorBasis j.1 (Sum.inr b)) =
          (if i = j then (1 / 2 : ℝ) else 0) := by
      simpa [Subtype.ext_iff] using hright
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hinner_expand :
        inner (𝕜 := ℝ) (negRightRaw i) (negRightRaw j) =
          2 * dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
                (fun b => hB.eigenvectorBasis j.1 (Sum.inr b)) := by
      calc
        inner (𝕜 := ℝ) (negRightRaw i) (negRightRaw j)
            = dotProduct (fun b => Real.sqrt 2 * hB.eigenvectorBasis j.1 (Sum.inr b))
                (fun b => Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr b)) := by
                  simp [negRightRaw, EuclideanSpace.inner_toLp_toLp]
        _ = ∑ x, (Real.sqrt 2 * hB.eigenvectorBasis j.1 (Sum.inr x)) *
              (Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr x)) := by
                simp [dotProduct]
        _ = ∑ x, 2 * (hB.eigenvectorBasis i.1 (Sum.inr x) *
              hB.eigenvectorBasis j.1 (Sum.inr x)) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                calc
                  (Real.sqrt 2 * hB.eigenvectorBasis j.1 (Sum.inr x)) *
                      (Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr x))
                      = (Real.sqrt 2 * Real.sqrt 2) *
                          (hB.eigenvectorBasis i.1 (Sum.inr x) *
                            hB.eigenvectorBasis j.1 (Sum.inr x)) := by ring
                  _ = 2 * (hB.eigenvectorBasis i.1 (Sum.inr x) *
                        hB.eigenvectorBasis j.1 (Sum.inr x)) := by rw [hsqrt]
        _ = 2 * dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
              (fun b => hB.eigenvectorBasis j.1 (Sum.inr b)) := by
                simp [dotProduct, Finset.mul_sum]
    rw [hinner_expand, hright', if_neg hij]
    norm_num
  have hne_raw :
      ∀ i : {i : Sum m n // hB.eigenvalues i < 0}, negRightRaw i ≠ 0 := by
    intro i
    have hsum : hB.eigenvalues i.1 + hB.eigenvalues i.1 ≠ 0 := by
      linarith [i.2]
    obtain ⟨_, hright⟩ := blockDilation_split_dot_half A hB hsum
    have hright' :
        dotProduct (fun b => hB.eigenvectorBasis i.1 (Sum.inr b))
            (fun b => hB.eigenvectorBasis i.1 (Sum.inr b)) = (1 / 2 : ℝ) := by
      simpa using hright
    exact fun hzero => by
      have hfunzero :
          (fun b => Real.sqrt 2 * hB.eigenvectorBasis i.1 (Sum.inr b)) = 0 := by
        exact (WithLp.toLp_eq_zero (p := (2 : ENNReal))).mp hzero
      have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
      have hraw_zero :
          (fun b => hB.eigenvectorBasis i.1 (Sum.inr b)) = 0 := by
        funext b
        have hb := congrArg (fun f : n → ℝ => f b) hfunzero
        exact (mul_eq_zero.mp hb).resolve_left hsqrt_ne
      have : (1 / 2 : ℝ) = 0 := by simpa [hraw_zero] using hright'
      norm_num at this
  have hpair :
      Pairwise (fun i j : {i : Sum m n // hB.eigenvalues i < 0} =>
        inner (𝕜 := ℝ) (negRight i) (negRight j) = 0) := by
    intro i j hij
    simpa [negRight] using hpair_raw hij
  have hne :
      ∀ i : {i : Sum m n // hB.eigenvalues i < 0}, negRight i ≠ 0 := by
    intro i
    intro hzero
    have hval : negRightRaw i = 0 := by
      simpa [negRight] using congrArg Subtype.val hzero
    exact hne_raw i hval
  have hli : LinearIndependent ℝ negRight :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hne hpair
  have hrange :
      Module.finrank ℝ ↥(LinearMap.range (Matrix.toEuclideanLin A.transpose)) = A.rank := by
    simpa using toEuclideanLin_range_finrank_eq_rank A.transpose
  exact (LinearIndependent.fintype_card_le_finrank hli).trans_eq hrange

/-- Reindexing the positive sector onto the ordered eigenvalue indexing preserves its cardinality. -/
lemma blockDilation_positive_eigenvalue_count_le_rank_ordered
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ)
    (hB : (Matrix.fromBlocks (0 : Matrix m m ℝ) A A.transpose (0 : Matrix n n ℝ)).IsHermitian) :
    Fintype.card {i : Fin (Fintype.card (Sum m n)) // 0 < hB.eigenvalues₀ i} ≤ A.rank := by
  classical
  let e : Fin (Fintype.card (Sum m n)) ≃ Sum m n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let ePos :
      {i : Fin (Fintype.card (Sum m n)) // 0 < hB.eigenvalues₀ i} ≃
        {i : Sum m n // 0 < hB.eigenvalues i} :=
    { toFun := fun i => ⟨e i.1, by simpa [Matrix.IsHermitian.eigenvalues, e] using i.2⟩
      invFun := fun i => ⟨e.symm i.1, by simpa [Matrix.IsHermitian.eigenvalues, e] using i.2⟩
      left_inv := by
        intro i
        ext
        simp [e]
      right_inv := by
        intro i
        ext
        simp [e] }
  have hcard :
      Fintype.card {i : Fin (Fintype.card (Sum m n)) // 0 < hB.eigenvalues₀ i} =
        Fintype.card {i : Sum m n // 0 < hB.eigenvalues i} :=
    Fintype.card_congr ePos
  rw [hcard]
  exact blockDilation_positive_eigenvalue_count_le_rank A hB


/- [BLOCK Exercise 4.29-(a) | 33 | thm]
Let A ∈ ℝ^{m × n} with m ≥ n, and let k be an integer with 1 ≤ k ≤ n. Let σ_1(A) ≥ ·s ≥ σ_n(A) be
the singular values of A, and define f(A)=sum_{i=1}^k σ_i(A). Let S^m and S^n denote the sets of
real symmetric m × m and n × n matrices, respectively. For symmetric matrices P,Q, write P succeq 0
if P is positive semidefinite, and P preceq Q if Q-P succeq 0. Show that f(A) is the optimal value
of the semidefinite program for Ky Fan norm
aligned
maximize quad & tr(Aᵀ X) ; ;
subject to quad & [ U & X ; ; Xᵀ & V ] succeq 0, ; ;
& U preceq I, ; ;
& V preceq I, ; ;
& tr(U)+tr(V)=2k,
aligned
where the decision variables are X ∈ ℝ^{m × n}, U ∈ S^m, and V ∈ S^n, and I is the identity matrix
of the appropriate dimension.
-/
theorem kyFanNormSDP_optimal_value
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ)
    (hmn : Fintype.card n ≤ Fintype.card m)
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card n) :
    let fA : ℝ := sSup {r : ℝ | ∃ U : Matrix m (Fin k) ℝ, ∃ V : Matrix n (Fin k) ℝ,
        U.transpose * U = 1 ∧ V.transpose * V = 1 ∧
        r = Matrix.trace (U.transpose * A * V)}
    (∀ P : KyFanNormSDP m n, P.A = A → P.k = k → P.objective ≤ fA) ∧
    (∀ ε > 0, ∃ P : KyFanNormSDP m n, P.A = A ∧ P.k = k ∧ fA - ε < P.objective) := by
  classical
  dsimp
  set S : Set ℝ := {r : ℝ | ∃ U : Matrix m (Fin k) ℝ, ∃ V : Matrix n (Fin k) ℝ,
      U.transpose * U = 1 ∧ V.transpose * V = 1 ∧
      r = Matrix.trace (U.transpose * A * V)}
  constructor
  · intro P hPA hPk
    let W : Matrix (Sum m n) (Sum m n) ℝ := Matrix.fromBlocks P.U P.X P.X.transpose P.V
    let Y : Matrix (Sum m n) (Sum m n) ℝ := (1 / 2 : ℝ) • W
    let B : Matrix (Sum m n) (Sum m n) ℝ :=
      Matrix.fromBlocks (0 : Matrix m m ℝ) A A.transpose (0 : Matrix n n ℝ)
    have hY :=
      feasibleHalfBlock_isTraceKContraction P
    have hobjective :=
      objective_eq_blockDilationTrace A P hPA
    have hS_bdd : BddAbove S := by
      -- The witness set already has a coarse entrywise upper bound, so `sSup S` is meaningful.
      simpa [S] using bddAbove_kyFanWitnessSet A k
    have hB : B.IsHermitian := by
      -- The block dilation is Hermitian because the off-diagonal blocks are transposes.
      simpa [B] using
        Matrix.IsHermitian.fromBlocks
          (Matrix.isHermitian_zero : (0 : Matrix m m ℝ).IsHermitian)
          (by
            ext i j
            simp [Matrix.conjTranspose])
          (Matrix.isHermitian_zero : (0 : Matrix n n ℝ).IsHermitian)
    dsimp [W, Y, B] at hY hobjective
    -- Route correction: stop working with the rectangular variable `X` directly.
    -- The proof is now reduced to a square Hermitian dilation `B` and a trace-`k` positive
    -- contraction `Y`, which is the right input for a Ky-Fan variational argument.
    have htrace_le_sup : Matrix.trace (B * Y) ≤ sSup S := by
      have htrace_le_head :
          Matrix.trace (B * Y) ≤
            ∑ j : Fin k,
              hB.eigenvalues₀
                (Fin.castLE
                  (show k ≤ Fintype.card (Sum m n) by
                    simpa [Fintype.card_sum] using
                      Nat.le_trans hkn (Nat.le_add_left (Fintype.card n) (Fintype.card m))) j) := by
        -- The completed spectral helper reduces the feasible SDP point to the ordered head sum.
        exact trace_hermitian_mul_traceContraction_le_head_eigenvalues hB hk1
          (show k ≤ Fintype.card (Sum m n) by
            simpa [Fintype.card_sum] using
              Nat.le_trans hkn (Nat.le_add_left (Fintype.card n) (Fintype.card m)))
          hY.1 hY.2.1 (by simpa [Y, hPk] using hY.2.2)
      have hhead_le_sup :
          (∑ j : Fin k,
              hB.eigenvalues₀
                (Fin.castLE
                  (show k ≤ Fintype.card (Sum m n) by
                    simpa [Fintype.card_sum] using
                      Nat.le_trans hkn (Nat.le_add_left (Fintype.card n) (Fintype.card m))) j)) ≤
            sSup S := by
        let hksum : k ≤ Fintype.card (Sum m n) := by
          simpa [Fintype.card_sum] using
            Nat.le_trans hkn (Nat.le_add_left (Fintype.card n) (Fintype.card m))
        let headSum : ℝ :=
          ∑ j : Fin k, hB.eigenvalues₀ (Fin.castLE hksum j)
        have hhead_nonneg : ∀ j : Fin k, 0 ≤ hB.eigenvalues₀ (Fin.castLE hksum j) := by
          -- The negative block-dilation spectrum fits inside the last `card n` slots, so every
          -- one of the first `k ≤ card n ≤ card m` ordered eigenvalues is nonnegative.
          intro j
          let N : ℕ := Fintype.card (Sum m n)
          let vlast : Fin k :=
            ⟨k - 1, Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hk1) Nat.zero_lt_one⟩
          have hlast_nonneg :
              0 ≤ hB.eigenvalues₀ (Fin.castLE hksum vlast) := by
            by_contra hneg
            have hneg_last : hB.eigenvalues₀ (Fin.castLE hksum vlast) < 0 := lt_of_not_ge hneg
            let tailIdx : Fin (N - (k - 1)) → Fin N :=
              fun s => ⟨k - 1 + s.1, by
                dsimp [N]
                omega⟩
            have htail_neg :
                ∀ s : Fin (N - (k - 1)),
                  hB.eigenvalues₀ (tailIdx s) < 0 := by
              intro s
              have hle :
                  (Fin.castLE hksum vlast : Fin N) ≤ tailIdx s := by
                change k - 1 ≤ (tailIdx s).1
                exact Nat.le_add_right _ _
              exact lt_of_le_of_lt (hB.eigenvalues₀_antitone hle) hneg_last
            let tailNeg :
                Fin (N - (k - 1)) ↪ {i : Fin N // hB.eigenvalues₀ i < 0} :=
              ⟨fun s => ⟨tailIdx s, htail_neg s⟩, by
                intro s t hst
                apply Fin.ext
                exact Nat.add_left_cancel (congrArg Fin.val (Subtype.ext_iff.mp hst))⟩
            have htail_card :
                N - (k - 1) ≤ Fintype.card {i : Fin N // hB.eigenvalues₀ i < 0} := by
              simpa using Fintype.card_le_of_injective tailNeg tailNeg.injective
            have hneg_card :=
              blockDilation_negative_eigenvalue_count_le_card_right_ordered A hB
            have hbig : Fintype.card n < N - (k - 1) := by
              change Fintype.card n <
                Fintype.card (Sum m n) - (k - 1)
              simp [Fintype.card_sum]
              omega
            exact (not_le_of_gt hbig) (htail_card.trans hneg_card)
          have hle :
              (Fin.castLE hksum j : Fin (Fintype.card (Sum m n))) ≤ Fin.castLE hksum vlast := by
            change j.1 ≤ vlast.1
            exact Nat.le_pred_of_lt j.2
          exact hlast_nonneg.trans (hB.eigenvalues₀_antitone hle)
        have hhead_mem : headSum ∈ S := by
          -- Route correction: the proof is now isolated to a pure witness-construction goal.
          -- Once the ordered head sum is shown to belong to the frame witness set `S`,
          -- `le_csSup` closes the inequality immediately. The spectral-ordering part is now done:
          -- `hhead_nonneg` shows the relevant head entries are all nonnegative.
          have hframePackage :
              ∃ (p : ℕ) (hp : p ≤ k)
                (Upos : Matrix m (Fin p) ℝ) (Vpos : Matrix n (Fin p) ℝ)
                (Uker : Matrix m (Fin (k - p)) ℝ) (Vker : Matrix n (Fin (k - p)) ℝ),
                  Upos.transpose * Upos = 1 ∧
                  Vpos.transpose * Vpos = 1 ∧
                  Uker.transpose * Uker = 1 ∧
                  Vker.transpose * Vker = 1 ∧
                  Upos.transpose * Uker = 0 ∧
                  Vpos.transpose * Vker = 0 ∧
                  Matrix.trace (Upos.transpose * A * Vpos) = headSum ∧
                  Matrix.trace (Uker.transpose * A * Vker) = 0 := by
            -- TODO: prove the corrected `p = min k A.rank` positive-prefix count, realize the
            -- positive head entries with split block-dilation eigenvectors, and pad the remaining
            -- `k - p` columns by orthonormal kernel vectors of `Aᵀ` and `A`.
            sorry
          rcases hframePackage with
            ⟨p, hp, Upos, Vpos, Uker, Vker,
              hUpos, hVpos, hUker, hVker, hcrossU, hcrossV, htracePos, htraceKer⟩
          simpa [S] using
            splitFrameWitness_mem_kyFanWitnessSet A hp Upos Vpos Uker Vker
              hUpos hVpos hUker hVker hcrossU hcrossV htracePos htraceKer
        -- Membership in the witness set is exactly the input required for the supremum bound.
        exact le_csSup hS_bdd hhead_mem
      exact htrace_le_head.trans hhead_le_sup
    exact hobjective.symm ▸ htrace_le_sup
  · intro ε hε
    have hS_nonempty : S.Nonempty := by
      let eₙ : Fin k ↪ n :=
        Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hkn))
      let eₘ : Fin k ↪ m :=
        Classical.choice
          (Function.Embedding.nonempty_of_card_le (by simpa using Nat.le_trans hkn hmn))
      -- The first `k` coordinate vectors in `m` and `n` give a concrete nonempty witness set.
      refine ⟨Matrix.trace ((coordinateFrame eₘ).transpose * A * coordinateFrame eₙ), ?_⟩
      refine ⟨coordinateFrame eₘ, coordinateFrame eₙ, ?_, ?_, rfl⟩
      · simpa using coordinateFrame_transpose_mul_self eₘ
      · simpa using coordinateFrame_transpose_mul_self eₙ
    -- Once the candidate set is nonempty, `sSup S - ε < sSup S` gives a witness above `fA - ε`.
    obtain ⟨r, hrS, hlt⟩ :=
      exists_lt_of_lt_csSup hS_nonempty (sub_lt_self (sSup S) hε)
    rcases hrS with ⟨U, V, hU, hV, rfl⟩
    obtain ⟨P, hPA, hPk, hobj⟩ := orthonormalFrameFeasiblePoint A k U V hU hV
    refine ⟨P, hPA, hPk, ?_⟩
    -- The feasible point constructed from the frame realizes the selected candidate value.
    simpa [hobj] using hlt

end «problem-75»
