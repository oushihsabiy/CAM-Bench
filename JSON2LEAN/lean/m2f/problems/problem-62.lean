import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open scoped MatrixOrder
open Filter
open scoped BigOperators

namespace «problem-62»
/- [BLOCK Exercise 2.26-(b) | 31 | defn]
For symmetric matrices A, B ∈ S^n, A preceq B means that B - A succeq 0.
-/
def loewnerOrder {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm ∧ B.IsSymm ∧ Matrix.PosSemidef (B - A)

/- [BLOCK Exercise 2.26-(b) | 32 | defn]
If X = [ X_{11} & X_{12}; X_{12}ᵀ & X_{22} ] with X_{22} invertible, then the Schur complement of
X_{22} in X is X_{11} - X_{12}X_{22}^{-1}X_{12}ᵀ.
-/
def schurComplement {n m : ℕ} (X11 : Matrix (Fin n) (Fin n) ℝ)
    (X12 : Matrix (Fin n) (Fin m) ℝ)
    (X22 : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  X11 - X12 * X22⁻¹ * X12.transpose

/- [BLOCK Exercise 2.26-(b) | 33 | opt_prob]
aligned
minimize quad & log det Y^{-1} ;
subject to quad & [ Y & 0 ; 0 & 0 ] preceq [ X_{11} & X_{12} ; X_{12}ᵀ & X_{22} ],
aligned
with domain S_{++}^m for log det Y^{-1}.
-/
structure LogDetSemidefiniteProgram where
  n : ℕ
  m : ℕ
  X11 : Matrix (Fin m) (Fin m) ℝ
  X12 : Matrix (Fin m) (Fin n) ℝ
  X22 : Matrix (Fin n) (Fin n) ℝ
  Y : Matrix (Fin m) (Fin m) ℝ
  X11_symm : X11.IsSymm
  X22_symm : X22.IsSymm
  Y_symm : Y.IsSymm
  Y_posDef : Matrix.PosDef Y
  block_constraint :
    (Matrix.fromBlocks Y
      (0 : Matrix (Fin m) (Fin n) ℝ)
      (0 : Matrix (Fin n) (Fin m) ℝ)
      (0 : Matrix (Fin n) (Fin n) ℝ)).IsSymm ∧
    (Matrix.fromBlocks X11 X12 X12.transpose X22).IsSymm ∧
    Matrix.PosSemidef
      ((Matrix.fromBlocks X11 X12 X12.transpose X22) -
        Matrix.fromBlocks Y
          (0 : Matrix (Fin m) (Fin n) ℝ)
          (0 : Matrix (Fin n) (Fin m) ℝ)
          (0 : Matrix (Fin n) (Fin n) ℝ))

def LogDetSemidefiniteProgram.objective (p : LogDetSemidefiniteProgram) : ℝ :=
  Real.log (Matrix.det (p.Y⁻¹))

def LogDetSemidefiniteProgram.isFeasible (p : LogDetSemidefiniteProgram) : Prop :=
  (Matrix.fromBlocks p.Y
    (0 : Matrix (Fin p.m) (Fin p.n) ℝ)
    (0 : Matrix (Fin p.n) (Fin p.m) ℝ)
    (0 : Matrix (Fin p.n) (Fin p.n) ℝ)).IsSymm ∧
  (Matrix.fromBlocks p.X11 p.X12 p.X12.transpose p.X22).IsSymm ∧
  Matrix.PosSemidef
    ((Matrix.fromBlocks p.X11 p.X12 p.X12.transpose p.X22) -
      Matrix.fromBlocks p.Y
        (0 : Matrix (Fin p.m) (Fin p.n) ℝ)
        (0 : Matrix (Fin p.n) (Fin p.m) ℝ)
        (0 : Matrix (Fin p.n) (Fin p.n) ℝ))

def LogDetSemidefiniteProgram.schurComplementData (p : LogDetSemidefiniteProgram) :
    Matrix (Fin p.m) (Fin p.m) ℝ :=
  schurComplement p.X11 p.X12 p.X22

/-- The bottom-right principal block of a positive-definite block matrix is positive definite. -/
lemma bottomRightBlock_posDef_of_fromBlocks_posDef
    {n m : ℕ}
    (X11 : Matrix (Fin m) (Fin m) ℝ)
    (X12 : Matrix (Fin m) (Fin (n - m)) ℝ)
    (X22 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)
    (hX22symm : X22.IsSymm)
    (hXpos : Matrix.PosDef (Matrix.fromBlocks X11 X12 X12.transpose X22)) :
    Matrix.PosDef X22 := by
  -- Evaluate the block quadratic form on vectors supported in the lower block.
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa using hX22symm) ?_
  intro y hy
  have hvec : Sum.elim (0 : Fin m → ℝ) y ≠ 0 := by
    intro hzero
    apply hy
    funext i
    have := congrFun hzero (Sum.inr i)
    simpa using this
  have hmain := hXpos.dotProduct_mulVec_pos hvec
  simpa [Matrix.dotProduct_mulVec, Matrix.fromBlocks_mulVec, Function.comp_def] using hmain

/-- A positive-definite block matrix has a positive-definite Schur complement. -/
lemma schurComplement_posDef_of_fromBlocks_posDef
    {n m : ℕ}
    (X11 : Matrix (Fin m) (Fin m) ℝ)
    (X12 : Matrix (Fin m) (Fin (n - m)) ℝ)
    (X22 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)
    (hX22symm : X22.IsSymm)
    (hXpos : Matrix.PosDef (Matrix.fromBlocks X11 X12 X12.transpose X22)) :
    Matrix.PosDef (schurComplement X11 X12 X22) := by
  letI := (bottomRightBlock_posDef_of_fromBlocks_posDef X11 X12 X22 hX22symm hXpos).isUnit.invertible
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · -- The block-Hermitian condition descends to the Schur complement.
    simpa [schurComplement] using
      (Matrix.IsHermitian.fromBlocks₂₂ X11 X12 (by simpa using hX22symm)).mp hXpos.1
  · -- Route correction: using `x ⊕ 0` leaves an extra positive term, so we cancel it with the
    -- standard Schur-complement choice `y = -(X22⁻¹ X12ᵀ x)`.
    intro x hx
    let y : Fin (n - m) → ℝ := -((X22⁻¹ * X12.transpose) *ᵥ x)
    have hvec : Sum.elim x y ≠ 0 := by
      intro hzero
      apply hx
      funext i
      have := congrFun hzero (Sum.inl i)
      simpa [y] using this
    have hmain := hXpos.dotProduct_mulVec_pos hvec
    have hmain' :
        0 < (x ⊕ᵥ y) ᵥ* Matrix.fromBlocks X11 X12 X12.transpose X22 ⬝ᵥ (x ⊕ᵥ y) := by
      simpa [Matrix.dotProduct_mulVec, y] using hmain
    have hrewrite :
        (x ⊕ᵥ y) ᵥ* Matrix.fromBlocks X11 X12 X12.transpose X22 ⬝ᵥ (x ⊕ᵥ y) =
          ((X22⁻¹ * X12.transpose) *ᵥ x + y) ᵥ* X22 ⬝ᵥ ((X22⁻¹ * X12.transpose) *ᵥ x + y) +
          x ᵥ* (X11 - X12 * X22⁻¹ * X12.transpose) ⬝ᵥ x := by
      simpa [y] using Matrix.schur_complement_eq₂₂ X11 X12 x y (D := X22)
        (hD := by simpa using hX22symm)
    rw [hrewrite] at hmain'
    simpa [schurComplement, y, Matrix.dotProduct_mulVec, Function.comp_def] using hmain'

/-- Feasibility of `Y` implies `Y` is bounded above by the Schur complement in matrix order. -/
lemma feasible_implies_schurComplement_sub_nonneg
    {n m : ℕ}
    (X11 : Matrix (Fin m) (Fin m) ℝ)
    (X12 : Matrix (Fin m) (Fin (n - m)) ℝ)
    (X22 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)
    (Y : Matrix (Fin m) (Fin m) ℝ)
    (hX22pos : Matrix.PosDef X22)
    (hfeas : (Matrix.fromBlocks Y
        (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
        (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
        (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)).IsSymm ∧
      (Matrix.fromBlocks X11 X12 X12.transpose X22).IsSymm ∧
      Matrix.PosSemidef
        ((Matrix.fromBlocks X11 X12 X12.transpose X22) -
          Matrix.fromBlocks Y
            (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
            (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
            (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ))) :
    Matrix.PosSemidef (schurComplement X11 X12 X22 - Y) := by
  rcases hfeas with ⟨_, _, hpsd⟩
  -- Rewrite the block slack matrix in a form suited for the Schur-complement lemma.
  have hblock : Matrix.PosSemidef (Matrix.fromBlocks (X11 - Y) X12 X12.transpose X22) := by
    simpa [sub_eq_add_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_neg] using hpsd
  letI := hX22pos.isUnit.invertible
  have hschur := (Matrix.PosDef.fromBlocks₂₂ (A := X11 - Y) X12 hX22pos).mp hblock
  simpa [schurComplement, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hschur

/-- For a positive semidefinite matrix `C`, the determinant of `I + C` is at least `1`. -/
lemma det_one_add_posSemidef_ge_one
    {k : ℕ}
    {C : Matrix (Fin k) (Fin k) ℝ}
    (hC : Matrix.PosSemidef C) :
    1 ≤ Matrix.det (1 + C) := by
  -- Rewrite `I + C` as a functional calculus expression so the determinant becomes a product of
  -- the eigenvalue transforms `1 + λ_i`.
  have hEq1 : cfc (fun x : ℝ => 1 + x) C = (1 : Matrix (Fin k) (Fin k) ℝ) + C := by
    calc
      cfc (fun x : ℝ => 1 + x) C = (1 : Matrix (Fin k) (Fin k) ℝ) + cfc (fun x : ℝ => x) C := by
        simpa using (cfc_const_add (R := ℝ) (1 : ℝ) (fun x : ℝ => x) C (ha := hC.1))
      _ = (1 : Matrix (Fin k) (Fin k) ℝ) + C := by
        simpa using congrArg (fun M : Matrix (Fin k) (Fin k) ℝ =>
          (1 : Matrix (Fin k) (Fin k) ℝ) + M) (cfc_id' ℝ C (ha := hC.1))
  calc
    1 ≤ ∏ i, (1 + hC.1.eigenvalues i) := by
      refine Finset.one_le_prod Finset.univ ?_
      intro i
      have hi := hC.eigenvalues_nonneg i
      linarith
    _ = Matrix.det ((1 : Matrix (Fin k) (Fin k) ℝ) + C) := by
      symm
      calc
        Matrix.det ((1 : Matrix (Fin k) (Fin k) ℝ) + C)
          = Matrix.det (hC.1.cfc (fun x : ℝ => 1 + x)) := by
              rw [← hEq1, hC.1.cfc_eq]
        _ = ∏ i, (1 + hC.1.eigenvalues i) := by
              simp [Matrix.IsHermitian.cfc, -Unitary.conjStarAlgAut_apply]

/-- A positive semidefinite increment increases determinant on positive-definite matrices. -/
lemma det_mono_of_posDef_and_posSemidef_sub
    {k : ℕ}
    {A B : Matrix (Fin k) (Fin k) ℝ}
    (hA : Matrix.PosDef A)
    (hBA : Matrix.PosSemidef (B - A)) :
    Matrix.det A ≤ Matrix.det B := by
  let S : Matrix (Fin k) (Fin k) ℝ := CFC.sqrt A
  -- Conjugate the increment by the inverse square root to factor out `A`.
  have hSpos : Matrix.PosDef S := by
    simpa [S] using Matrix.IsStrictlyPositive.posDef hA.isStrictlyPositive.sqrt
  letI := hSpos.isUnit.invertible
  let Cmat : Matrix (Fin k) (Fin k) ℝ := S⁻¹ * (B - A) * S⁻¹
  have hSinv_herm : S⁻¹.IsHermitian := hSpos.1.inv
  have hSinv_symm : S⁻¹.IsSymm := by
    exact hSinv_herm
  have hC_psd : Matrix.PosSemidef Cmat := by
    have hconj : Matrix.PosSemidef ((S⁻¹).conjTranspose * (B - A) * S⁻¹) :=
      Matrix.PosSemidef.conjTranspose_mul_mul_same hBA S⁻¹
    simpa [Cmat, hSinv_symm.eq] using hconj
  have hdetC : 1 ≤ Matrix.det (1 + Cmat) := det_one_add_posSemidef_ge_one hC_psd
  have hAeq : A = S * S := by
    symm
    rw [← sq]
    simpa [S] using (CFC.sq_sqrt A)
  have hCSC : S * Cmat * S = B - A := by
    calc
      S * Cmat * S = S * (S⁻¹ * (B - A) * S⁻¹) * S := by simp [Cmat]
      _ = (S * S⁻¹) * (B - A) * (S⁻¹ * S) := by simp [Matrix.mul_assoc]
      _ = B - A := by simp
  have hCSC' : S * Cmat * S = B - S * S := by
    simpa [hAeq] using hCSC
  have hBeq : B = S * (1 + Cmat) * S := by
    calc
      B = S * S + (B - S * S) := by
        rw [sub_eq_add_neg]
        abel
      _ = S * S + S * Cmat * S := by rw [← hCSC']
      _ = S * (1 + Cmat) * S := by
        symm
        calc
          S * (1 + Cmat) * S = (S * (1 + Cmat)) * S := by rw [Matrix.mul_assoc]
          _ = (S * 1 + S * Cmat) * S := by rw [Matrix.mul_add]
          _ = S * S + S * Cmat * S := by simp [add_mul, Matrix.mul_assoc]
  have hdet_formula : Matrix.det B = Matrix.det A * Matrix.det (1 + Cmat) := by
    rw [hBeq, Matrix.det_mul, Matrix.det_mul, hAeq, Matrix.det_mul]
    ring
  have hApos : 0 < Matrix.det A := hA.det_pos
  calc
    Matrix.det A ≤ Matrix.det A * Matrix.det (1 + Cmat) := by
      simpa [one_mul] using mul_le_mul_of_nonneg_left hdetC (le_of_lt hApos)
    _ = Matrix.det B := by rw [hdet_formula]

/-- For a real positive-definite matrix, the trace of the matrix logarithm is the logarithm of the
determinant. -/
lemma trace_log_eq_log_det_of_posDef
    {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : Matrix.PosDef A) :
    Matrix.trace (CFC.log A) = Real.log (Matrix.det A) := by
  -- Diagonalize the Hermitian matrix and compute both sides on eigenvalues.
  rw [show CFC.log A = hA.1.cfc Real.log by
    simpa [CFC.log] using hA.1.cfc_eq Real.log]
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  rw [hA.1.det_eq_prod_eigenvalues, Real.log_prod]
  · simp
  · intro i _
    exact (ne_of_gt (hA.eigenvalues_pos i))

/- [BLOCK Exercise 2.26-(b) | 34 | thm]
Let n,m ∈ ℕ with m ≤ n. Let S^n be the set of real symmetric n × n matrices and S_{++}^n the set of
real symmetric positive definite n × n matrices. For A,B ∈ S^n, A preceq B means B-A succeq 0. Let P
∈ ℝ^{n × m} have rank m, and let f:S^n → ℝ have domain dom f=S_{++}^n, defined by f(X)=logdet(Pᵀ
X^{-1}P). Assume P=[ I ; 0 ], where I is the m × m identity matrix. Let X ∈ S_{++}^n be partitioned
as X=[ X_{11} & X_{12} ; X_{12}ᵀ & X_{22} ], where X_{11} ∈ S^m, X_{12} ∈ ℝ^{m × (n-m)}, and X_{22}
∈ S^{n-m}. Show that the optimization problem aligned minimize quad & log det Y^{-1} ; subject to
quad & [ Y & 0 ; 0 & 0 ] preceq [ X_{11} & X_{12} ; X_{12}ᵀ & X_{22} ], aligned Take S_{++}^m as the
domain of log det Y^{-1}. has the solution Y = X_{11} - X_{12} X_{22}^{-1} X_{12}ᵀ.
-/
theorem schur_complement_solves_logDetSemidefiniteProgram
    {n m : ℕ} (hmn : m ≤ n)
    (X11 : Matrix (Fin m) (Fin m) ℝ)
    (X12 : Matrix (Fin m) (Fin (n - m)) ℝ)
    (X22 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)
    (hX11symm : X11.IsSymm)
    (hX22symm : X22.IsSymm)
    (hXpos :
      Matrix.PosDef (Matrix.fromBlocks X11 X12 X12.transpose X22)) :
    let Yopt := schurComplement X11 X12 X22
    ((Matrix.fromBlocks Yopt
        (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
        (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
        (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)).IsSymm ∧
      (Matrix.fromBlocks X11 X12 X12.transpose X22).IsSymm ∧
      Matrix.PosSemidef
        ((Matrix.fromBlocks X11 X12 X12.transpose X22) -
          Matrix.fromBlocks Yopt
            (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
            (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
            (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ))) ∧
    Matrix.PosDef Yopt ∧
    ∀ Y : Matrix (Fin m) (Fin m) ℝ,
      Y.IsSymm →
      Matrix.PosDef Y →
      ((Matrix.fromBlocks Y
          (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
          (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
          (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)).IsSymm ∧
        (Matrix.fromBlocks X11 X12 X12.transpose X22).IsSymm ∧
        Matrix.PosSemidef
          ((Matrix.fromBlocks X11 X12 X12.transpose X22) -
            Matrix.fromBlocks Y
              (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
              (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
              (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ))) →
      Real.log (Matrix.det (Yopt⁻¹)) ≤ Real.log (Matrix.det (Y⁻¹)) := by
  let Yopt := schurComplement X11 X12 X22
  have hX22pos : Matrix.PosDef X22 :=
    bottomRightBlock_posDef_of_fromBlocks_posDef X11 X12 X22 hX22symm hXpos
  have hYopt_pos : Matrix.PosDef Yopt :=
    schurComplement_posDef_of_fromBlocks_posDef X11 X12 X22 hX22symm hXpos
  have hYopt_symm : Yopt.IsSymm := by
    -- The Hermitian Schur complement is symmetric over `ℝ`.
    simpa [Yopt, schurComplement] using
      (Matrix.IsHermitian.fromBlocks₂₂ X11 X12 (by simpa using hX22symm)).mp hXpos.1
  have hbig_symm : (Matrix.fromBlocks X11 X12 X12.transpose X22).IsSymm := by
    simpa using hXpos.1
  have hYopt_feas_psd : Matrix.PosSemidef
      ((Matrix.fromBlocks X11 X12 X12.transpose X22) -
        Matrix.fromBlocks Yopt
          (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
          (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
          (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)) := by
    letI := hX22pos.isUnit.invertible
    -- The Schur complement of the slack matrix is zero, so the slack is PSD.
    have hzero : Matrix.PosSemidef ((X11 - Yopt) - X12 * X22⁻¹ * X12.transpose) := by
      simpa [Yopt, schurComplement] using
        (Matrix.PosSemidef.zero : Matrix.PosSemidef (0 : Matrix (Fin m) (Fin m) ℝ))
    have hblock := (Matrix.PosDef.fromBlocks₂₂ (A := X11 - Yopt) X12 hX22pos).mpr hzero
    simpa [sub_eq_add_neg, Matrix.fromBlocks_add, Matrix.fromBlocks_neg] using hblock
  refine ⟨?_, hYopt_pos, ?_⟩
  · refine ⟨?_, hbig_symm, hYopt_feas_psd⟩
    exact Matrix.IsSymm.fromBlocks hYopt_symm rfl <| by
      simp
  · intro Y hYsymm hYpos hfeasY
    let _ := hmn
    let _ := hX11symm
    have hYopt_sub_Y : Matrix.PosSemidef (Yopt - Y) :=
      feasible_implies_schurComplement_sub_nonneg X11 X12 X22 Y hX22pos hfeasY
    have hdet_mono : Matrix.det Y ≤ Matrix.det Yopt :=
      det_mono_of_posDef_and_posSemidef_sub hYpos hYopt_sub_Y
    have hYdetpos : 0 < Matrix.det Y := hYpos.det_pos
    have hYoptdetpos : 0 < Matrix.det Yopt := hYopt_pos.det_pos
    have hlog_mono : Real.log (Matrix.det Y) ≤ Real.log (Matrix.det Yopt) :=
      Real.log_le_log hYdetpos hdet_mono
    -- Convert monotonicity of `log det` into monotonicity of the objective `log det Y⁻¹`.
    have hYopt_obj : Real.log (Matrix.det (Yopt⁻¹)) = -Real.log (Matrix.det Yopt) := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv]
    have hY_obj : Real.log (Matrix.det (Y⁻¹)) = -Real.log (Matrix.det Y) := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv]
    rw [hYopt_obj, hY_obj]
    exact neg_le_neg hlog_mono

end «problem-62»
