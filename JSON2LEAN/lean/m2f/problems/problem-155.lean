import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open scoped MatrixOrder
open scoped ComplexOrder
open Filter
open scoped BigOperators

namespace «problem-155»
/-
A semidefinite program is an optimization problem of the form langle C, Xrangle: langle Aᵢ, Xrangle
= bᵢ (i = 1, ..., m), X succeq 0, where the variable X is symmetric and langle U, Vrangle = tr(Uᵀ
V).
-/
open scoped Matrix

structure SemidefiniteProgram (n m : ℕ) where
  C : Matrix (Fin n) (Fin n) ℝ
  A : Fin m → Matrix (Fin n) (Fin n) ℝ
  b : Fin m → ℝ
  C_symm : C.IsSymm
  A_symm : ∀ i, (A i).IsSymm

/-
⟨U, V⟩ = tr(UᵀV).
-/
def SemidefiniteProgram.matrixInner {n : ℕ}
    (U V : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (U.transpose * V)

def SemidefiniteProgram.isFeasible {n m : ℕ} (P : SemidefiniteProgram n m)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsSymm ∧
    X.PosSemidef ∧
    (∀ i : Fin m, SemidefiniteProgram.matrixInner (P.A i) X = P.b i)

def SemidefiniteProgram.objective {n m : ℕ} (P : SemidefiniteProgram n m)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  SemidefiniteProgram.matrixInner P.C X

/-
Exercise 3.14

maximize tr(X)

subject to [A X X B] ⪰ 0,

where the variable is X ∈ Sⁿ.
-/
structure TraceMaximizationSemidefiniteProgram (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  B : Matrix (Fin n) (Fin n) ℝ
  A_symm : A.IsSymm
  B_symm : B.IsSymm

def TraceMaximizationSemidefiniteProgram.blockMatrix {n : ℕ}
    (P : TraceMaximizationSemidefiniteProgram n)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks P.A X X P.B

def TraceMaximizationSemidefiniteProgram.isFeasible {n : ℕ}
    (P : TraceMaximizationSemidefiniteProgram n)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsSymm ∧
    (TraceMaximizationSemidefiniteProgram.blockMatrix P X).PosSemidef

def TraceMaximizationSemidefiniteProgram.objective {n : ℕ}
    (_P : TraceMaximizationSemidefiniteProgram n)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace X

def TraceMaximizationSemidefiniteProgram.interp {n : ℕ}
    (t : ℝ)
    (P₁ P₂ : TraceMaximizationSemidefiniteProgram n) :
    TraceMaximizationSemidefiniteProgram n where
  A := t • P₁.A + (1 - t) • P₂.A
  B := t • P₁.B + (1 - t) • P₂.B
  A_symm := (P₁.A_symm.smul t).add (P₂.A_symm.smul (1 - t))
  B_symm := (P₁.B_symm.smul t).add (P₂.B_symm.smul (1 - t))

/-
Let S^n be the set of real symmetric n × n matrices, and let S_{+ +}^n be the set of real symmetric
positive definite n × n matrices. For U, V ∈ S^n, write U preceq V when V - U succeq 0. For M ∈
S_{+ +}^n, let M^{1/2} denote its unique symmetric positive definite square root, and let M^{- 1/2}
denote the inverse of M^{1/2}. Assume that if U, V ∈ S^n satisfy U succeq 0, V succeq 0, and U
preceq V, then U^{1/2} preceq V^{1/2}. For A, B ∈ S_{+ +}^n, define G(A, B) = A^{1/2}
(A^{- 1/2}BA^{- 1/2})^{1/2} A^{1/2}. Show that X = G(A, B) solves the semidefinite program trace
maximization semidefinite program.
-/
theorem geometricMean_solves_traceMaximizationSemidefiniteProgram
    {n : ℕ}
    (P : TraceMaximizationSemidefiniteProgram n)
    (sqrtA invSqrtA sqrtMid : Matrix (Fin n) (Fin n) ℝ)
    (hA_symm : P.A.IsSymm)
    (hB_symm : P.B.IsSymm)
    (hA_pos : P.A.PosDef)
    (hB_pos : P.B.PosDef)
    (h_sqrtA_symm : sqrtA.IsSymm)
    (h_sqrtA_pos : sqrtA.PosDef)
    (h_sqrtA : sqrtA * sqrtA = P.A)
    (h_sqrtA_unique :
      ∀ S : Matrix (Fin n) (Fin n) ℝ,
        S.IsSymm →
        S.PosDef →
        S * S = P.A →
        S = sqrtA)
    (h_invSqrtA_symm : invSqrtA.IsSymm)
    (h_invSqrtA_pos : invSqrtA.PosDef)
    (h_invSqrtA_left : invSqrtA * sqrtA = 1)
    (h_invSqrtA_right : sqrtA * invSqrtA = 1)
    (h_sqrtMid_symm : sqrtMid.IsSymm)
    (h_sqrtMid_pos : sqrtMid.PosDef)
    (h_sqrtMid : sqrtMid * sqrtMid = invSqrtA * P.B * invSqrtA)
    (h_sqrtMid_unique :
      ∀ S : Matrix (Fin n) (Fin n) ℝ,
        S.IsSymm →
        S.PosDef →
        S * S = invSqrtA * P.B * invSqrtA →
        S = sqrtMid)
    (h_sqrt_mono :
      ∀ U V sqrtU sqrtV : Matrix (Fin n) (Fin n) ℝ,
        U.IsSymm →
        V.IsSymm →
        U.PosSemidef →
        V.PosSemidef →
        (V - U).PosSemidef →
        sqrtU.IsSymm →
        sqrtV.IsSymm →
        sqrtU.PosDef →
        sqrtV.PosDef →
        sqrtU * sqrtU = U →
        sqrtV * sqrtV = V →
        (sqrtV - sqrtU).PosSemidef) :
    TraceMaximizationSemidefiniteProgram.isFeasible P (sqrtA * sqrtMid * sqrtA) ∧
      ∀ Y : Matrix (Fin n) (Fin n) ℝ,
        TraceMaximizationSemidefiniteProgram.isFeasible P Y →
          TraceMaximizationSemidefiniteProgram.objective P Y ≤
            TraceMaximizationSemidefiniteProgram.objective P (sqrtA * sqrtMid * sqrtA) := by
  classical
  let X : Matrix (Fin n) (Fin n) ℝ := sqrtA * sqrtMid * sqrtA
  let M : Matrix (Fin n) (Fin n) ℝ := invSqrtA * P.B * invSqrtA
  -- Route correction: rather than trying to force the custom monotonicity hypothesis `h_sqrt_mono`
  -- onto a semidefinite square root, use Schur complements and the matrix-order `CFC.sqrt`.
  have hA_inv : P.A⁻¹ = invSqrtA * invSqrtA := by
    -- The inverse is determined by the explicit right inverse built from `invSqrtA`.
    apply Matrix.inv_eq_right_inv
    calc
      P.A * (invSqrtA * invSqrtA)
          = (sqrtA * sqrtA) * (invSqrtA * invSqrtA) := by rw [h_sqrtA]
      _ = sqrtA * (sqrtA * invSqrtA) * invSqrtA := by simp [Matrix.mul_assoc]
      _ = sqrtA * 1 * invSqrtA := by rw [h_invSqrtA_right]
      _ = sqrtA * invSqrtA := by simp
      _ = 1 := h_invSqrtA_right
  have hX_symm : X.IsSymm := by
    -- The candidate is symmetric because it has the form `A * B * A` with symmetric factors.
    dsimp [X]
    simpa [Matrix.IsSymm, Matrix.transpose_mul, Matrix.mul_assoc, h_sqrtA_symm.eq,
      h_sqrtMid_symm.eq]
  have hX_herm : X.IsHermitian := by
    -- Over `ℝ`, symmetry and Hermitianity coincide.
    simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hX_symm
  have hM_pos : M.PosDef := by
    -- Conjugating the positive definite matrix `P.B` by `invSqrtA` preserves positivity.
    have hconj :=
      hB_pos.mul_mul_conjTranspose_same
        (B := invSqrtA)
        (Matrix.vecMul_injective_iff_isUnit.2 h_invSqrtA_pos.isUnit)
    dsimp [M] at *
    simpa [Matrix.conjTranspose, h_invSqrtA_symm.eq] using hconj
  have h_sqrtMid_cfc : CFC.sqrt M = sqrtMid := by
    -- The given `sqrtMid` is the positive square root of the normalized middle matrix.
    have hM_nonneg : 0 ≤ M := hM_pos.posSemidef.nonneg
    have hsqrtMid_nonneg : 0 ≤ sqrtMid := h_sqrtMid_pos.posSemidef.nonneg
    apply (CFC.sqrt_eq_iff M sqrtMid hM_nonneg hsqrtMid_nonneg).2
    dsimp [M]
    simpa [pow_two] using h_sqrtMid
  have hX_feasible : TraceMaximizationSemidefiniteProgram.isFeasible P X := by
    refine ⟨hX_symm, ?_⟩
    letI := hA_pos.isUnit.invertible
    -- The Schur complement of the candidate vanishes after the square-root identities.
    have hschur : (P.B - Xᴴ * P.A⁻¹ * X).PosSemidef := by
      have hzero : P.B - Xᴴ * P.A⁻¹ * X = 0 := by
        rw [hX_herm.eq, hA_inv]
        dsimp [X]
        have hprod :
            sqrtA * sqrtMid * sqrtA * (invSqrtA * invSqrtA) * (sqrtA * sqrtMid * sqrtA) =
              P.B := by
          calc
            sqrtA * sqrtMid * sqrtA * (invSqrtA * invSqrtA) * (sqrtA * sqrtMid * sqrtA)
                = sqrtA * sqrtMid * ((sqrtA * invSqrtA) * invSqrtA) * (sqrtA * sqrtMid * sqrtA) := by
                    simp [Matrix.mul_assoc]
            _ = sqrtA * sqrtMid * (1 * invSqrtA) * (sqrtA * sqrtMid * sqrtA) := by
                  rw [h_invSqrtA_right]
            _ = sqrtA * sqrtMid * invSqrtA * (sqrtA * sqrtMid * sqrtA) := by simp
            _ = sqrtA * sqrtMid * ((invSqrtA * sqrtA) * sqrtMid) * sqrtA := by
                  simp [Matrix.mul_assoc]
            _ = sqrtA * sqrtMid * (1 * sqrtMid) * sqrtA := by rw [h_invSqrtA_left]
            _ = sqrtA * (sqrtMid * sqrtMid) * sqrtA := by simp [Matrix.mul_assoc]
            _ = sqrtA * (invSqrtA * P.B * invSqrtA) * sqrtA := by rw [h_sqrtMid]
            _ = (sqrtA * invSqrtA) * P.B * (invSqrtA * sqrtA) := by simp [Matrix.mul_assoc]
            _ = 1 * P.B * 1 := by rw [h_invSqrtA_right, h_invSqrtA_left]
            _ = P.B := by simp
        rw [hprod, sub_self]
      rw [hzero]
      exact Matrix.PosSemidef.zero
    -- The block PSD condition is exactly the Schur-complement criterion.
    have hblock : (Matrix.fromBlocks P.A X Xᴴ P.B).PosSemidef :=
      (Matrix.PosDef.fromBlocks₁₁ (A := P.A) (B := X) (D := P.B) hA_pos).2 hschur
    simpa [TraceMaximizationSemidefiniteProgram.blockMatrix, Matrix.conjTranspose, hX_symm.eq]
      using hblock
  refine ⟨hX_feasible, ?_⟩
  intro Y hY
  letI := hA_pos.isUnit.invertible
  have hY_schur : (P.B - Yᵀ * P.A⁻¹ * Y).PosSemidef := by
    -- Feasibility of `Y` gives the Schur-complement inequality against the positive definite block `P.A`.
    have hblock : (Matrix.fromBlocks P.A Y Yᴴ P.B).PosSemidef := by
      simpa [TraceMaximizationSemidefiniteProgram.blockMatrix, Matrix.conjTranspose, hY.1.eq] using hY.2
    exact (Matrix.PosDef.fromBlocks₁₁ (A := P.A) (B := Y) (D := P.B) hA_pos).1 hblock
  let Z : Matrix (Fin n) (Fin n) ℝ := invSqrtA * Y * invSqrtA
  have hZ_symm : Z.IsSymm := by
    -- The normalized matrix stays symmetric because both `invSqrtA` and `Y` are symmetric.
    dsimp [Z]
    simpa [Matrix.IsSymm, Matrix.transpose_mul, Matrix.mul_assoc, h_invSqrtA_symm.eq, hY.1.eq]
  have hZ_herm : Z.IsHermitian := by
    -- Over `ℝ`, Hermitianity is the same as symmetry.
    simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hZ_symm
  have hZ_sq_le_M : Z ^ 2 ≤ M := by
    -- Route correction: use the matrix-order `CFC.sqrt` directly on `Matrix`; this snapshot already
    -- provides the Schur-complement side of the argument directly; only the monotone square-root
    -- step below needs the `CStarMatrix` detour.
    rw [Matrix.le_iff]
    have hnormalized := hY_schur.mul_mul_conjTranspose_same (B := invSqrtA)
    simpa [M, Z, hA_inv, hY.1.eq, pow_two, Matrix.mul_assoc, Matrix.conjTranspose,
      h_invSqrtA_symm.eq, mul_sub, sub_mul] using hnormalized
  have hsqrtMid_sub_Z : (sqrtMid - Z).PosSemidef := by
    -- Route correction: move to complex matrices, where the operator-monotone square-root theorem
    -- is available once we register the standard `L2`-operator C⋆-norm as a local instance.
    letI : NonUnitalCStarAlgebra (Matrix (Fin n) (Fin n) ℂ) :=
      { norm_mul_self_le := fun x =>
          le_of_eq <| Eq.symm <| Matrix.l2_opNorm_conjTranspose_mul_self x }
    have hcomplexifyPosSemidef :
        ∀ {D : Matrix (Fin n) (Fin n) ℝ},
          D.PosSemidef → ((algebraMap ℝ ℂ).mapMatrix D).PosSemidef := by
      intro D hD
      rw [Matrix.posSemidef_iff_eq_conjTranspose_mul_self] at hD ⊢
      rcases hD with ⟨B, rfl⟩
      refine ⟨(algebraMap ℝ ℂ).mapMatrix B, ?_⟩
      ext i j
      simp [Matrix.mul_apply]
    have hrealPosSemidef_of_complexify :
        ∀ {D : Matrix (Fin n) (Fin n) ℝ},
          D.IsSymm →
          ((algebraMap ℝ ℂ).mapMatrix D).PosSemidef →
          D.PosSemidef := by
      intro D hD_symm hDc
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
      · -- A real symmetric matrix is Hermitian.
        simpa [Matrix.IsHermitian, Matrix.conjTranspose] using hD_symm
      · intro x
        -- Testing the complexified matrix on real vectors recovers the original quadratic form.
        have hx := hDc.dotProduct_mulVec_nonneg fun i => (x i : ℂ)
        have hx' :
            (0 : ℂ) ≤
              ((star x ⬝ᵥ (D *ᵥ x) : ℝ) : ℂ) := by
          simpa [dotProduct, Matrix.mulVec] using hx
        exact Complex.zero_le_real.mp hx'
    let Zc : Matrix (Fin n) (Fin n) ℂ := (algebraMap ℝ ℂ).mapMatrix Z
    let Mc : Matrix (Fin n) (Fin n) ℂ := (algebraMap ℝ ℂ).mapMatrix M
    let sqrtMidc : Matrix (Fin n) (Fin n) ℂ := (algebraMap ℝ ℂ).mapMatrix sqrtMid
    have hZc_herm : Zc.IsHermitian := by
      -- Complexifying a real symmetric matrix produces a Hermitian matrix.
      dsimp [Zc]
      ext i j
      simp [Matrix.conjTranspose, hZ_symm.apply i j]
    have hMc_nonneg : 0 ≤ Mc := by
      -- The normalized middle matrix remains positive semidefinite after complexification.
      dsimp [Mc]
      exact (hcomplexifyPosSemidef hM_pos.posSemidef).nonneg
    have hsqrtMidc_nonneg : 0 ≤ sqrtMidc := by
      -- The given square root stays positive semidefinite after complexification.
      dsimp [sqrtMidc]
      exact (hcomplexifyPosSemidef h_sqrtMid_pos.posSemidef).nonneg
    have hZc_sq_le_Mc : Zc ^ 2 ≤ Mc := by
      -- The quadratic bound `Z ^ 2 ≤ M` is preserved entrywise by `ℝ → ℂ`.
      rw [Matrix.le_iff] at hZ_sq_le_M ⊢
      have htmp :
          (((algebraMap ℝ ℂ).mapMatrix M - (algebraMap ℝ ℂ).mapMatrix (Z * Z))).PosSemidef := by
        simpa [Matrix.map_sub, pow_two] using hcomplexifyPosSemidef hZ_sq_le_M
      dsimp [Zc, Mc]
      simpa [pow_two, ((algebraMap ℝ ℂ).mapMatrix.map_mul Z Z)] using htmp
    have hsqrtMidc_cfc : CFC.sqrt Mc = sqrtMidc := by
      -- The complexified candidate is the nonnegative square root of the complexified middle term.
      apply (CFC.sqrt_eq_iff Mc sqrtMidc (ha := hMc_nonneg) (hb := hsqrtMidc_nonneg)).2
      dsimp [Mc, sqrtMidc]
      calc
        ((algebraMap ℝ ℂ).mapMatrix sqrtMid) * ((algebraMap ℝ ℂ).mapMatrix sqrtMid)
            = (algebraMap ℝ ℂ).mapMatrix (sqrtMid * sqrtMid) := by
                simpa using ((algebraMap ℝ ℂ).mapMatrix.map_mul sqrtMid sqrtMid).symm
        _ = (algebraMap ℝ ℂ).mapMatrix (invSqrtA * P.B * invSqrtA) := by rw [h_sqrtMid]
    have hZc_le_abs : Zc ≤ CFC.abs Zc := by
      -- The difference `|Zc| - Zc` is twice the negative part, hence nonnegative.
      rw [Matrix.le_iff, CFC.abs_sub_self Zc hZc_herm]
      simpa [Matrix.nonneg_iff_posSemidef, two_smul] using
        (smul_nonneg (by positivity) (CFC.negPart_nonneg Zc) : 0 ≤ (2 : ℝ) • Zc⁻)
    have habs_eq_sqrt : CFC.abs Zc = CFC.sqrt (Zc ^ 2) := by
      -- For Hermitian `Zc`, the absolute value is the nonnegative square root of `Zc ^ 2`.
      symm
      apply (CFC.sqrt_eq_iff (Zc ^ 2) (CFC.abs Zc)
        (ha := by
          simpa [Matrix.star_eq_conjTranspose, hZc_herm.eq, pow_two] using star_mul_self_nonneg Zc)
        (hb := CFC.abs_nonneg Zc)).2
      simpa [Matrix.star_eq_conjTranspose, hZc_herm.eq, pow_two] using CFC.abs_mul_abs Zc
    have habs_le_sqrtMidc : CFC.abs Zc ≤ sqrtMidc := by
      -- Monotonicity of the complex matrix square root upgrades the quadratic comparison.
      calc
        CFC.abs Zc = CFC.sqrt (Zc ^ 2) := habs_eq_sqrt
        _ ≤ CFC.sqrt Mc := CFC.sqrt_le_sqrt (Zc ^ 2) Mc hZc_sq_le_Mc
        _ = sqrtMidc := hsqrtMidc_cfc
    have hDc_nonneg : ((algebraMap ℝ ℂ).mapMatrix (sqrtMid - Z)).PosSemidef := by
      -- Translating `Zc ≤ sqrtMidc` back to a positive semidefinite difference is immediate.
      have hZc_le_sqrtMidc : Zc ≤ sqrtMidc := hZc_le_abs.trans habs_le_sqrtMidc
      simpa [Zc, sqrtMidc, Matrix.le_iff, Matrix.map_sub] using hZc_le_sqrtMidc
    -- The difference is real symmetric, so complex positivity descends to real positivity.
    refine hrealPosSemidef_of_complexify (D := sqrtMid - Z) ?_ hDc_nonneg
    exact h_sqrtMid_symm.sub hZ_symm
  have hsqrtA_Z_sqrtA : sqrtA * Z * sqrtA = Y := by
    -- Undo the normalization using the explicit inverse relations between `sqrtA` and `invSqrtA`.
    dsimp [Z]
    calc
      sqrtA * (invSqrtA * Y * invSqrtA) * sqrtA
          = (sqrtA * invSqrtA) * Y * (invSqrtA * sqrtA) := by
              simp [Matrix.mul_assoc]
      _ = 1 * Y * 1 := by rw [h_invSqrtA_right, h_invSqrtA_left]
      _ = Y := by simp
  have hX_sub_Y_pos : (X - Y).PosSemidef := by
    -- Conjugating the normalized order bound by `sqrtA` recovers the desired comparison `Y ≤ X`.
    have hconj := hsqrtMid_sub_Z.mul_mul_conjTranspose_same (B := sqrtA)
    have hconj' : (sqrtA * (sqrtMid - Z) * sqrtA).PosSemidef := by
      simpa [Matrix.conjTranspose, h_sqrtA_symm.eq] using hconj
    have hrewrite : sqrtA * (sqrtMid - Z) * sqrtA = X - Y := by
      calc
        sqrtA * (sqrtMid - Z) * sqrtA
            = sqrtA * sqrtMid * sqrtA - sqrtA * Z * sqrtA := by
                simp [sub_eq_add_neg, Matrix.mul_assoc, mul_add, add_mul]
        _ = X - Y := by simp [X, hsqrtA_Z_sqrtA]
    simpa [hrewrite] using hconj'
  have htrace_nonneg : 0 ≤ Matrix.trace (X - Y) := Matrix.PosSemidef.trace_nonneg hX_sub_Y_pos
  -- The positive semidefinite difference `X - Y` has nonnegative trace, which is the objective gap.
  dsimp [TraceMaximizationSemidefiniteProgram.objective]
  have hgap : 0 ≤ Matrix.trace X - Matrix.trace Y := by
    simpa [Matrix.trace_sub] using htrace_nonneg
  linarith

/-
Let S^n be the set of real symmetric n × n matrices. For positive definite A and B, the matrix
geometric mean G(A, B) is the optimizer of the trace-maximization SDP above. The concavity of
tr G(A, B) follows from this SDP representation: if G₁ and G₂ solve the endpoint SDPs and Gt solves
the SDP for the averaged pair, then tG₁ + (1 - t)G₂ is feasible for the averaged SDP, hence its
trace is at most the optimal trace at the averaged pair. This formulation avoids the false boundary
case in which arbitrary non-principal square roots are used to define G.
-/
theorem trace_geometricMean_concave
    {n : ℕ}
    (t : ℝ)
    (P₁ P₂ : TraceMaximizationSemidefiniteProgram n)
    (G₁ G₂ Gt : Matrix (Fin n) (Fin n) ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1)
    (hG₁_opt :
      TraceMaximizationSemidefiniteProgram.isFeasible P₁ G₁ ∧
        ∀ Y : Matrix (Fin n) (Fin n) ℝ,
          TraceMaximizationSemidefiniteProgram.isFeasible P₁ Y →
            TraceMaximizationSemidefiniteProgram.objective P₁ Y ≤
              TraceMaximizationSemidefiniteProgram.objective P₁ G₁)
    (hG₂_opt :
      TraceMaximizationSemidefiniteProgram.isFeasible P₂ G₂ ∧
        ∀ Y : Matrix (Fin n) (Fin n) ℝ,
          TraceMaximizationSemidefiniteProgram.isFeasible P₂ Y →
            TraceMaximizationSemidefiniteProgram.objective P₂ Y ≤
              TraceMaximizationSemidefiniteProgram.objective P₂ G₂)
    (hGt_opt :
      TraceMaximizationSemidefiniteProgram.isFeasible
        (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂) Gt ∧
        ∀ Y : Matrix (Fin n) (Fin n) ℝ,
          TraceMaximizationSemidefiniteProgram.isFeasible
            (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂) Y →
            TraceMaximizationSemidefiniteProgram.objective
              (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂) Y ≤
              TraceMaximizationSemidefiniteProgram.objective
                (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂) Gt) :
    TraceMaximizationSemidefiniteProgram.isFeasible
        (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂)
        (t • G₁ + (1 - t) • G₂) ∧
      t * TraceMaximizationSemidefiniteProgram.objective P₁ G₁ +
          (1 - t) * TraceMaximizationSemidefiniteProgram.objective P₂ G₂ ≤
        TraceMaximizationSemidefiniteProgram.objective
          (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂) Gt := by
  rcases hG₁_opt with ⟨hG₁_feas, hG₁_optimal⟩
  rcases hG₂_opt with ⟨hG₂_feas, hG₂_optimal⟩
  rcases hGt_opt with ⟨hGt_feas, hGt_optimal⟩
  refine ⟨?_, ?_⟩
  · refine ⟨(hG₁_feas.1.smul t).add (hG₂_feas.1.smul (1 - t)), ?_⟩
    -- The block feasibility region is convex because positive semidefinite matrices are.
    have hblock₁ := hG₁_feas.2
    have hblock₂ := hG₂_feas.2
    have hblock :
        (t • TraceMaximizationSemidefiniteProgram.blockMatrix P₁ G₁ +
          (1 - t) • TraceMaximizationSemidefiniteProgram.blockMatrix P₂ G₂).PosSemidef :=
      Matrix.PosSemidef.add
        (Matrix.PosSemidef.smul hblock₁ ht₀)
        (Matrix.PosSemidef.smul hblock₂ (sub_nonneg.mpr ht₁))
    simpa [TraceMaximizationSemidefiniteProgram.blockMatrix,
      TraceMaximizationSemidefiniteProgram.interp, Matrix.fromBlocks_add, Matrix.fromBlocks_smul,
      Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hblock
  · -- The objective is linear, so optimality of `Gt` bounds the convex combination.
    have hfeas_combo :
        TraceMaximizationSemidefiniteProgram.isFeasible
          (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂)
          (t • G₁ + (1 - t) • G₂) := by
      exact (show TraceMaximizationSemidefiniteProgram.isFeasible
        (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂)
        (t • G₁ + (1 - t) • G₂) from by
          refine ⟨(hG₁_feas.1.smul t).add (hG₂_feas.1.smul (1 - t)), ?_⟩
          have hblock :
              (t • TraceMaximizationSemidefiniteProgram.blockMatrix P₁ G₁ +
                (1 - t) • TraceMaximizationSemidefiniteProgram.blockMatrix P₂ G₂).PosSemidef :=
            Matrix.PosSemidef.add
              (Matrix.PosSemidef.smul hG₁_feas.2 ht₀)
              (Matrix.PosSemidef.smul hG₂_feas.2 (sub_nonneg.mpr ht₁))
          simpa [TraceMaximizationSemidefiniteProgram.blockMatrix,
            TraceMaximizationSemidefiniteProgram.interp, Matrix.fromBlocks_add,
            Matrix.fromBlocks_smul, Matrix.add_mul, Matrix.mul_add, sub_eq_add_neg,
            add_comm, add_left_comm, add_assoc] using hblock)
    have hopt := hGt_optimal _ hfeas_combo
    simpa [TraceMaximizationSemidefiniteProgram.objective, Matrix.trace_add, Matrix.trace_smul,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using hopt

end «problem-155»
