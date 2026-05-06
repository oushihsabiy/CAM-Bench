import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-151»
/-
A semidefinite program is an optimization problem in which the decision variables are subject to
affine matrix inequalities of the form A₀ + \sum_{i = 1}^p zᵢ Aᵢ succeq 0, and the objective
function
is affine in the variables.
-/
structure SemidefiniteProgram (n p : ℕ) where
  A : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ
  c : Fin p → ℝ
  d : ℝ

def SemidefiniteProgram.lmi {n p : ℕ} (S : SemidefiniteProgram n p) (z : Fin p → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  S.A 0 + ∑ i : Fin p, z i • S.A i.succ

def SemidefiniteProgram.objective {n p : ℕ} (S : SemidefiniteProgram n p) (z : Fin p → ℝ) : ℝ :=
  ∑ i : Fin p, S.c i * z i + S.d

structure SchurComplementSemidefiniteProgram (m n : ℕ) where
  F : (Fin n → ℝ) → Matrix (Fin m) (Fin m) ℝ

def SchurComplementSemidefiniteProgram.blockMatrix {m n : ℕ}
    (P : SchurComplementSemidefiniteProgram m n) (x : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.fromBlocks (P.F x) 1 1 (t • (1 : Matrix (Fin m) (Fin m) ℝ))

def SchurComplementSemidefiniteProgram.isFeasible {m n : ℕ}
    (P : SchurComplementSemidefiniteProgram m n) (x : Fin n → ℝ) (t : ℝ) : Prop :=
  Matrix.PosDef (P.F x) ∧ Matrix.PosSemidef (P.blockMatrix x t)

def SchurComplementSemidefiniteProgram.objective {m n : ℕ}
    (_P : SchurComplementSemidefiniteProgram m n) (_x : Fin n → ℝ) (t : ℝ) : ℝ :=
  t

def unitBallQuadraticValues {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) : Set ℝ :=
  {q : ℝ | ∃ c : Fin m → ℝ, c ⬝ᵥ c ≤ 1 ∧ c ⬝ᵥ M.mulVec c = q}

def unitBallQuadraticSup {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  sSup (unitBallQuadraticValues M)

/-- The quadratic values attained on the unit ball are bounded above. -/
lemma unitBallQuadraticValues_bddAbove {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    BddAbove (unitBallQuadraticValues M) := by
  refine ⟨∑ i, ∑ j, |M i j|, ?_⟩
  intro q hq
  rcases hq with ⟨c, hc, rfl⟩
  -- Each coordinate of a vector in the unit ball has absolute value at most `1`.
  have hcoord_sq : ∀ i : Fin m, (c i) ^ 2 ≤ 1 := by
    intro i
    have hterm : c i * c i ≤ c ⬝ᵥ c := by
      simpa [dotProduct] using
        (Finset.single_le_sum (fun j _ => mul_self_nonneg (c j))
          (by simp : i ∈ (Finset.univ : Finset (Fin m))))
    simpa [sq] using hterm.trans hc
  have hcoord : ∀ i : Fin m, |c i| ≤ 1 := by
    intro i
    have hsq : (c i) ^ 2 ≤ 1 := hcoord_sq i
    have hleft : -(1 : ℝ) ≤ c i := by
      nlinarith
    have hright : c i ≤ 1 := by
      nlinarith
    exact abs_le.mpr ⟨hleft, hright⟩
  -- Expand the quadratic form into a double sum and bound each summand entrywise.
  have hexpand : c ⬝ᵥ M.mulVec c = ∑ i, ∑ j, c i * (M i j * c j) := by
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
  have habs :
      |c ⬝ᵥ M.mulVec c| ≤ ∑ i, ∑ j, |c i * (M i j * c j)| := by
    rw [hexpand]
    calc
      |∑ i, ∑ j, c i * (M i j * c j)| ≤ ∑ i, |∑ j, c i * (M i j * c j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |c i * (M i j * c j)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
  have hentry : ∀ i j : Fin m, |c i * (M i j * c j)| ≤ |M i j| := by
    intro i j
    calc
      |c i * (M i j * c j)| = |c i| * (|M i j| * |c j|) := by
        rw [abs_mul, abs_mul]
      _ ≤ 1 * (|M i j| * 1) := by
        gcongr <;> exact hcoord _
      _ = |M i j| := by
        ring
  exact (le_abs_self _).trans <| habs.trans <| by
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => hentry i j

/-- For a positive definite matrix, a bound on the unit-ball quadratic supremum is exactly the
matrix inequality `M ≤ t • 1`. -/
lemma unitBallQuadraticSup_le_iff_posSemidef_sub {m : ℕ}
    (hm : 0 < m) {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.PosDef) {t : ℝ} :
    unitBallQuadraticSup M ≤ t ↔ (t • (1 : Matrix (Fin m) (Fin m) ℝ) - M).PosSemidef := by
  constructor
  · intro hs
    -- Turn the supremum bound into nonnegativity of every quadratic form of `t • 1 - M`.
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · have hscalar : (t • (1 : Matrix (Fin m) (Fin m) ℝ)).IsHermitian := by
        simp [Matrix.IsHermitian]
      simpa using hscalar.sub hM.1
    · intro c
      by_cases hc0 : c = 0
      · simp [hc0]
      · let s : ℝ := Real.sqrt (c ⬝ᵥ c)
        let u : Fin m → ℝ := s⁻¹ • c
        have hcc_nonneg : 0 ≤ c ⬝ᵥ c := by
          simpa using dotProduct_star_self_nonneg c
        have hcc_pos : 0 < c ⬝ᵥ c := by
          have hcc_ne : c ⬝ᵥ c ≠ 0 := by
            intro hzero
            exact hc0 (dotProduct_self_eq_zero.mp hzero)
          exact lt_of_le_of_ne hcc_nonneg (Ne.symm hcc_ne)
        have hs_ne : s ≠ 0 := by
          exact Real.sqrt_ne_zero'.2 hcc_pos
        have hs_sq : s ^ 2 = c ⬝ᵥ c := by
          simp [s, Real.sq_sqrt hcc_nonneg]
        have hu_self : u ⬝ᵥ u = 1 := by
          -- Normalize `c` onto the unit sphere.
          calc
            u ⬝ᵥ u = s⁻¹ * (s⁻¹ * (c ⬝ᵥ c)) := by
              simp [u, smul_dotProduct, dotProduct_smul, mul_left_comm, mul_comm]
            _ = s⁻¹ * (s⁻¹ * s ^ 2) := by
              rw [hs_sq]
            _ = 1 := by
              field_simp [hs_ne]
        have hu_mem : u ⬝ᵥ M.mulVec u ∈ unitBallQuadraticValues M := by
          exact ⟨u, hu_self.le, rfl⟩
        have hu_le : u ⬝ᵥ M.mulVec u ≤ t := by
          exact (le_csSup (unitBallQuadraticValues_bddAbove M) hu_mem).trans hs
        have hc_repr : c = s • u := by
          simp [u, hs_ne, smul_smul]
        have hquad_scale : c ⬝ᵥ M.mulVec c = s ^ 2 * (u ⬝ᵥ M.mulVec u) := by
          -- Rescale the quadratic form along the normalized vector.
          rw [hc_repr]
          rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
          simp [sq, smul_eq_mul, mul_assoc]
        have htarget :
            c ⬝ᵥ ((t • (1 : Matrix (Fin m) (Fin m) ℝ) - M).mulVec c) =
              s ^ 2 * (t - u ⬝ᵥ M.mulVec u) := by
          calc
            c ⬝ᵥ ((t • (1 : Matrix (Fin m) (Fin m) ℝ) - M).mulVec c) =
                t * (c ⬝ᵥ c) - c ⬝ᵥ M.mulVec c := by
              rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
                dotProduct_smul, smul_eq_mul]
            _ = s ^ 2 * t - s ^ 2 * (u ⬝ᵥ M.mulVec u) := by
              rw [hquad_scale, ← hs_sq]
              ring
            _ = s ^ 2 * (t - u ⬝ᵥ M.mulVec u) := by
              ring
        have hmain : 0 ≤ s ^ 2 * (t - u ⬝ᵥ M.mulVec u) := by
          exact mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hu_le)
        exact htarget.symm ▸ hmain
  · intro hpsd
    -- Positivity of `t • 1 - M` bounds every admissible quadratic value by `t`.
    have i0 : Fin m := ⟨0, hm⟩
    have ht_nonneg : 0 ≤ t := by
      have hdiag_nonneg : 0 ≤ (t • (1 : Matrix (Fin m) (Fin m) ℝ) - M) i0 i0 := hpsd.diag_nonneg
      have hdiag_pos : 0 < M i0 i0 := hM.diag_pos
      have : 0 ≤ t - M i0 i0 := by
        simpa [Matrix.one_apply] using hdiag_nonneg
      linarith
    have hnonempty : (unitBallQuadraticValues M).Nonempty := by
      refine ⟨0, ?_⟩
      exact ⟨0, by simp, by simp⟩
    refine csSup_le hnonempty ?_
    intro q hq
    rcases hq with ⟨c, hc, rfl⟩
    have hcc_nonneg : 0 ≤ c ⬝ᵥ c := by
      simpa using dotProduct_star_self_nonneg c
    have hquad_nonneg :
        0 ≤ c ⬝ᵥ ((t • (1 : Matrix (Fin m) (Fin m) ℝ) - M).mulVec c) :=
      hpsd.dotProduct_mulVec_nonneg c
    have hle_tmul : c ⬝ᵥ M.mulVec c ≤ t * (c ⬝ᵥ c) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul] at hquad_nonneg
      linarith
    have hmul_le : t * (c ⬝ᵥ c) ≤ t := by
      nlinarith
    exact hle_tmul.trans hmul_le

/-- The block LMI is equivalent to the Schur-complement inequality with `B = 1`. -/
lemma blockMatrix_posSemidef_iff_schurComplement {m n : ℕ}
    (P : SchurComplementSemidefiniteProgram m n) (x : Fin n → ℝ) (t : ℝ)
    (hpd : Matrix.PosDef (P.F x)) :
    (P.blockMatrix x t).PosSemidef ↔
      (t • (1 : Matrix (Fin m) (Fin m) ℝ) - (P.F x)⁻¹).PosSemidef := by
  letI : Invertible (P.F x) := hpd.isUnit.invertible
  -- Specialize the standard Schur-complement criterion to the identity off-diagonal blocks.
  simpa [SchurComplementSemidefiniteProgram.blockMatrix, Matrix.mul_one, Matrix.one_mul] using
    (Matrix.PosDef.fromBlocks₁₁ (A := P.F x)
      (B := (1 : Matrix (Fin m) (Fin m) ℝ))
      (D := t • (1 : Matrix (Fin m) (Fin m) ℝ)) hpd)

/-
Let m, n ∈ ℕ. For each i = 0, 1, ..., n, let Fᵢ ∈ S^m, where S^m is the set of m × m real symmetric
matrices. For x = (x₁, ..., xₙ) ∈ ℝ^n, define F(x) = F₀ + \sum_{i = 1}^n xᵢ Fᵢ. Let dom f = {x ∈ ℝ^n
|
F(x)succ 0}, where F(x)succ 0 means that F(x) is positive definite. Assume m > 0, so the unit ball is
not the degenerate zero-dimensional case in which the LMI no longer constrains t. Prove the stronger
epigraph-level Schur-complement equivalence: for every x and t, the inequality
sup_{‖c‖_2 ≤ 1} cᵀ F(x)^{-1} c ≤ t is equivalent to the block LMI
[F(x) I; I tI] ⪰ 0. Consequently, the exact objective-value formulation, the epigraph formulation,
and the semidefinite program have the same infimum.
-/
theorem schurComplement_equivalent_to_unit_ball_quadratic_form_minimization
    (m n : ℕ)
    (F : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ)
    (hm : 0 < m)
    (hFsymm : ∀ i : Fin (n + 1), (F i).IsSymm) :
    let P : SchurComplementSemidefiniteProgram m n :=
      { F := fun x => F 0 + ∑ i : Fin n, x i • F i.succ }
    (∀ x : Fin n → ℝ, ∀ t : ℝ,
      Matrix.PosDef (P.F x) →
        (unitBallQuadraticSup ((P.F x)⁻¹) ≤ t ↔ P.isFeasible x t)) ∧
    ({t : ℝ | ∃ x : Fin n → ℝ,
      Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) ≤ t} =
      {t : ℝ | ∃ x : Fin n → ℝ, P.isFeasible x t}) ∧
    sInf
        {r : ℝ | ∃ x : Fin n → ℝ,
          Matrix.PosDef (P.F x) ∧
          unitBallQuadraticSup ((P.F x)⁻¹) = r} =
      sInf
        {t : ℝ | ∃ x : Fin n → ℝ,
          Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) ≤ t} ∧
    sInf
        {r : ℝ | ∃ x : Fin n → ℝ,
          Matrix.PosDef (P.F x) ∧
          unitBallQuadraticSup ((P.F x)⁻¹) = r} =
      sInf
        {t : ℝ | ∃ x : Fin n → ℝ,
          P.isFeasible x t} := by
  let _ := hFsymm
  let P : SchurComplementSemidefiniteProgram m n :=
    { F := fun x => F 0 + ∑ i : Fin n, x i • F i.succ }
  change
    (∀ x : Fin n → ℝ, ∀ t : ℝ,
      Matrix.PosDef (P.F x) →
        (unitBallQuadraticSup ((P.F x)⁻¹) ≤ t ↔ P.isFeasible x t)) ∧
    ({t : ℝ | ∃ x : Fin n → ℝ,
      Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) ≤ t} =
      {t : ℝ | ∃ x : Fin n → ℝ, P.isFeasible x t}) ∧
    sInf
        {r : ℝ | ∃ x : Fin n → ℝ,
          Matrix.PosDef (P.F x) ∧
          unitBallQuadraticSup ((P.F x)⁻¹) = r} =
      sInf
        {t : ℝ | ∃ x : Fin n → ℝ,
          Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) ≤ t} ∧
    sInf
        {r : ℝ | ∃ x : Fin n → ℝ,
          Matrix.PosDef (P.F x) ∧
          unitBallQuadraticSup ((P.F x)⁻¹) = r} =
      sInf
        {t : ℝ | ∃ x : Fin n → ℝ,
          P.isFeasible x t}
  -- First prove the pointwise equivalence between the quadratic epigraph and the block LMI.
  have hpointwise :
      ∀ x : Fin n → ℝ, ∀ t : ℝ,
        Matrix.PosDef (P.F x) →
          (unitBallQuadraticSup ((P.F x)⁻¹) ≤ t ↔ P.isFeasible x t) := by
    intro x t hpd
    constructor
    · intro hs
      refine ⟨hpd, ?_⟩
      exact (blockMatrix_posSemidef_iff_schurComplement (P := P) x t hpd).2
        ((unitBallQuadraticSup_le_iff_posSemidef_sub hm hpd.inv).1 hs)
    · rintro ⟨_, hblock⟩
      exact (unitBallQuadraticSup_le_iff_posSemidef_sub hm hpd.inv).2
        ((blockMatrix_posSemidef_iff_schurComplement (P := P) x t hpd).1 hblock)
  -- Then package the pointwise equivalence into equality of the two epigraph sets.
  have hepigraph :
      {t : ℝ | ∃ x : Fin n → ℝ,
        Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) ≤ t} =
        {t : ℝ | ∃ x : Fin n → ℝ, P.isFeasible x t} := by
    ext t
    constructor
    · rintro ⟨x, hpd, hs⟩
      exact ⟨x, (hpointwise x t hpd).1 hs⟩
    · rintro ⟨x, hfeas⟩
      rcases hfeas with ⟨hpd, hblock⟩
      exact ⟨x, hpd, (hpointwise x t hpd).2 ⟨hpd, hblock⟩⟩
  -- Compare exact objective values with their epigraph witnesses via the order-theoretic infimum lemma.
  have hcsInf_exact_epi :
      sInf
          {r : ℝ | ∃ x : Fin n → ℝ,
            Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) = r} =
        sInf
          {t : ℝ | ∃ x : Fin n → ℝ,
            Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) ≤ t} := by
    refine csInf_eq_csInf_of_forall_exists_le ?_ ?_
    · intro r hr
      rcases hr with ⟨x, hpd, rfl⟩
      exact ⟨unitBallQuadraticSup ((P.F x)⁻¹), ⟨x, hpd, le_rfl⟩, le_rfl⟩
    · intro t ht
      rcases ht with ⟨x, hpd, hle⟩
      exact ⟨unitBallQuadraticSup ((P.F x)⁻¹), ⟨x, hpd, rfl⟩, hle⟩
  -- Finally rewrite the feasible-value infimum with the already proved epigraph equality.
  have hcsInf_exact_feasible :
      sInf
          {r : ℝ | ∃ x : Fin n → ℝ,
            Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) = r} =
        sInf
          {t : ℝ | ∃ x : Fin n → ℝ,
            P.isFeasible x t} := by
    calc
      sInf
          {r : ℝ | ∃ x : Fin n → ℝ,
            Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) = r} =
          sInf
            {t : ℝ | ∃ x : Fin n → ℝ,
              Matrix.PosDef (P.F x) ∧ unitBallQuadraticSup ((P.F x)⁻¹) ≤ t} :=
        hcsInf_exact_epi
      _ =
          sInf
            {t : ℝ | ∃ x : Fin n → ℝ,
              P.isFeasible x t} := by
        rw [hepigraph]
  exact ⟨hpointwise, hepigraph, hcsInf_exact_epi, hcsInf_exact_feasible⟩


end «problem-151»
