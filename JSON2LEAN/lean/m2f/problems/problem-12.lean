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

namespace «problem-12»
/-
For X ∈ S_{+ +}^n, the log - determinant is logdet X = log(det X), where det X > 0.
-/
def logDet {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) : ℝ :=
  Real.log (Matrix.det X)

/-
[BLOCK Exercise 8.8 - (a) | 4 | opt_prob] Let Sⁿ denote the vector space of real symmetric n × n
matrices, let S₊₊ⁿ = {X ∈ Sⁿ ∣ X ≻ 0}, let diag(X) ∈ ℝⁿ denote the diagonal of X, let 1 ∈ ℝⁿ be the
all - ones vector, and let C ∈ Sⁿ. Consider the optimization problem

minimize tr(CX) − log det X

subject to diag(X) = 1,

with variable X ∈ Sⁿ, where the objective is defined only for X ∈ S₊₊ⁿ.
-/
structure LogDetSemidefiniteProgram (n : Type*) [Fintype n] [DecidableEq n] where
  C : Matrix n n ℝ
  C_symm : C.IsSymm

def LogDetSemidefiniteProgram.isFeasible {n : Type*} [Fintype n] [DecidableEq n]
    (_ : LogDetSemidefiniteProgram n) (X : Matrix n n ℝ) : Prop :=
  X.IsSymm ∧
  X.PosDef ∧
  X.diag = fun _ => (1 : ℝ)

def LogDetSemidefiniteProgram.objective {n : Type*} [Fintype n] [DecidableEq n]
    (P : LogDetSemidefiniteProgram n) (X : Matrix n n ℝ) : ℝ :=
  Matrix.trace (P.C * X) - logDet X

/-- Left multiplication by a diagonal matrix only keeps the diagonal part of the second factor
inside the trace. -/
lemma trace_diagonal_mul {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (Y : Matrix n n ℝ) :
    Matrix.trace (Matrix.diagonal d * Y) = ∑ i, d i * Y i i := by
  -- Expand the trace and the diagonal multiplication entrywise.
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]

/-- On the feasible affine slice `diag Y = 1`, a diagonal multiplier contributes the sum of its
diagonal entries. -/
lemma trace_diagonal_mul_of_diag_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) {Y : Matrix n n ℝ} (hY : Y.diag = fun _ => (1 : ℝ)) :
    Matrix.trace (Matrix.diagonal d * Y) = ∑ i, d i := by
  -- Replace each diagonal entry of `Y` by `1`.
  rw [trace_diagonal_mul]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hYii : Y i i = 1 := by
    simpa [Matrix.diag] using congrFun hY i
  simp [hYii]

/-- The barrier inequality `tr A - n - log det A ≥ 0` for a positive definite real matrix. -/
lemma trace_sub_log_det_nonneg_of_posDef {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosDef) :
    0 ≤ Matrix.trace A - Fintype.card n - Real.log (Matrix.det A) := by
  -- Diagonalize `A` and reduce to the scalar inequality `log u ≤ u - 1`.
  have htrace : Matrix.trace A = ∑ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.trace_eq_sum_eigenvalues
  have hdet : Matrix.det A = ∏ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.det_eq_prod_eigenvalues
  have hlog : Real.log (Matrix.det A) = ∑ i, Real.log (hA.isHermitian.eigenvalues i) := by
    rw [hdet, Real.log_prod]
    intro i hi
    exact (hA.eigenvalues_pos i).ne'
  rw [htrace, hlog]
  have hsum :
      0 ≤ ∑ i, (hA.isHermitian.eigenvalues i - 1 - Real.log (hA.isHermitian.eigenvalues i)) := by
    -- Each eigenvalue contributes a nonnegative scalar term.
    refine Finset.sum_nonneg ?_
    intro i hi
    have hi : 0 < hA.isHermitian.eigenvalues i := hA.eigenvalues_pos i
    linarith [Real.log_le_sub_one_of_pos hi]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  norm_num at hsum ⊢
  linarith

/-- Under the diagonal stationarity condition `X⁻¹ - C = diagonal d`, every feasible objective gap
is exactly the standard barrier gap of the conjugated matrix `sqrt(X⁻¹) * Y * sqrt(X⁻¹)`. -/
lemma objective_gap_eq_barrier_gap {n : Type*} [Fintype n] [DecidableEq n]
    (P : LogDetSemidefiniteProgram n) (X Y : Matrix n n ℝ)
    (hXpos : X.PosDef) (hYpos : Y.PosDef)
    (hXd : X.diag = fun _ => (1 : ℝ)) (hYd : Y.diag = fun _ => (1 : ℝ))
    {d : n → ℝ} (hd : X⁻¹ - P.C = Matrix.diagonal d) :
    P.objective Y - P.objective X =
      Matrix.trace (CFC.sqrt (X⁻¹) * Y * CFC.sqrt (X⁻¹)) - Fintype.card n -
        Real.log (Matrix.det (CFC.sqrt (X⁻¹) * Y * CFC.sqrt (X⁻¹))) := by
  let S := CFC.sqrt (X⁻¹)
  have hSpos : S.PosDef := by
    -- The square root of a positive definite inverse stays positive definite.
    exact Matrix.isStrictlyPositive_iff_posDef.mp (hXpos.inv.isStrictlyPositive.sqrt)
  have hSdetpos : 0 < Matrix.det S := hSpos.det_pos
  have hSdet_ne : Matrix.det S ≠ 0 := ne_of_gt hSdetpos
  have hSsq : S * S = X⁻¹ := by
    -- `S` is the positive square root of `X⁻¹`.
    simp [S, CFC.sqrt_mul_sqrt_self (X⁻¹) (show 0 ≤ X⁻¹ from hXpos.inv.posSemidef.nonneg)]
  have htraceS : Matrix.trace (S * Y * S) = Matrix.trace (X⁻¹ * Y) := by
    -- Trace is invariant under cyclic permutation.
    calc
      Matrix.trace (S * Y * S) = Matrix.trace (S * S * Y) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (X⁻¹ * Y) := by
        rw [hSsq]
  have hdetS : Matrix.det S * Matrix.det S = Matrix.det (X⁻¹) := by
    -- Determinants also see that `S^2 = X⁻¹`.
    have hdet := congrArg Matrix.det hSsq
    simpa [Matrix.det_mul] using hdet
  have hC : P.C = X⁻¹ - Matrix.diagonal d := by
    -- Solve the stationarity equation for `C`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      congrArg (fun Z => X⁻¹ - Z) hd
  have hlogS :
      Real.log (Matrix.det (S * Y * S)) = Real.log (Matrix.det Y) - Real.log (Matrix.det X) := by
    have hYdetpos : 0 < Matrix.det Y := hYpos.det_pos
    have hYdet_ne : Matrix.det Y ≠ 0 := ne_of_gt hYdetpos
    -- The determinant factorizes into the conjugation determinant and the determinant of `Y`.
    calc
      Real.log (Matrix.det (S * Y * S)) = Real.log (Matrix.det S * Matrix.det Y * Matrix.det S) := by
        rw [Matrix.det_mul, Matrix.det_mul]
      _ = Real.log (Matrix.det S) + Real.log (Matrix.det Y) + Real.log (Matrix.det S) := by
        rw [show Matrix.det S * Matrix.det Y * Matrix.det S =
            (Matrix.det S * Matrix.det Y) * Matrix.det S by ring,
          Real.log_mul (mul_ne_zero hSdet_ne hYdet_ne) hSdet_ne,
          Real.log_mul hSdet_ne hYdet_ne]
      _ = Real.log (Matrix.det S * Matrix.det S) + Real.log (Matrix.det Y) := by
        rw [Real.log_mul hSdet_ne hSdet_ne]
        ring
      _ = Real.log (Matrix.det (X⁻¹)) + Real.log (Matrix.det Y) := by
        rw [hdetS]
      _ = -Real.log (Matrix.det X) + Real.log (Matrix.det Y) := by
        rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv]
      _ = Real.log (Matrix.det Y) - Real.log (Matrix.det X) := by
        ring
  -- Rewrite both objective values using the diagonal stationarity relation.
  rw [LogDetSemidefiniteProgram.objective, LogDetSemidefiniteProgram.objective, logDet, logDet]
  simp only [sub_eq_add_neg]
  rw [hC, Matrix.sub_mul, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub]
  rw [trace_diagonal_mul_of_diag_eq_one d hYd, trace_diagonal_mul_of_diag_eq_one d hXd]
  have htraceXX : Matrix.trace (X⁻¹ * X) = Fintype.card n := by
    -- The inverse contribution at `X` is exactly the trace of the identity matrix.
    have hunit : IsUnit (Matrix.det X) := (Matrix.isUnit_iff_isUnit_det X).mp hXpos.isUnit
    rw [Matrix.nonsing_inv_mul _ hunit, Matrix.trace_one]
  rw [htraceS, htraceXX, hlogS]
  ring

/-- A symmetric perturbation of the identity stays positive definite when the scalar is small
compared to the perturbation norm. -/
lemma isStrictlyPositive_one_add_smul_of_isSymm_norm_mul_lt_one
    {n : Type*} [Fintype n] [DecidableEq n] (K : Matrix n n ℝ) (hK : K.IsSymm) {t : ℝ}
    (ht : |t| * ‖K‖ < 1) :
    IsStrictlyPositive (1 + t • K) := by
  -- Route correction: rather than using C⋆-order bounds, prove positivity directly from the
  -- quadratic form and the `l2` operator-norm estimate on `mulVec`.
  refine Matrix.isStrictlyPositive_iff_posDef.mpr ?_
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · -- The perturbed matrix stays symmetric.
    change (1 + t • K)ᵀ = 1 + t • K
    simpa using (Matrix.isSymm_one.add (hK.smul t)).eq
  · intro x hx
    have hinner :
        inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 (K *ᵥ x)) = star x ⬝ᵥ (K *ᵥ x) := by
      rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    have hself :
        x ⬝ᵥ x = ‖WithLp.toLp 2 x‖ ^ 2 := by
      calc
        x ⬝ᵥ x = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 x) := by
          simpa using (EuclideanSpace.inner_toLp_toLp x x).symm
        _ = ‖WithLp.toLp 2 x‖ ^ 2 := real_inner_self_eq_norm_sq _
    have hmulVec :
        ‖WithLp.toLp 2 (K *ᵥ x)‖ ≤ ‖K‖ * ‖WithLp.toLp 2 x‖ := by
      simpa using Matrix.l2_opNorm_mulVec K (WithLp.toLp 2 x)
    have hquad :
        |star x ⬝ᵥ (K *ᵥ x)| ≤ ‖K‖ * ‖WithLp.toLp 2 x‖ ^ 2 := by
      calc
        |star x ⬝ᵥ (K *ᵥ x)| =
            |inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 (K *ᵥ x))| := by
          rw [hinner]
        _ ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 (K *ᵥ x)‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖WithLp.toLp 2 x‖ * (‖K‖ * ‖WithLp.toLp 2 x‖) := by
          exact mul_le_mul_of_nonneg_left hmulVec (norm_nonneg (WithLp.toLp 2 x))
        _ = ‖K‖ * ‖WithLp.toLp 2 x‖ ^ 2 := by ring
    have hprod_lower :
        -(|t| * (‖K‖ * ‖WithLp.toLp 2 x‖ ^ 2)) ≤ t * (star x ⬝ᵥ (K *ᵥ x)) := by
      have habs :
          |t * (star x ⬝ᵥ (K *ᵥ x))| ≤ |t| * (‖K‖ * ‖WithLp.toLp 2 x‖ ^ 2) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hquad (abs_nonneg t)
      exact neg_le_of_abs_le habs
    have hrewrite :
        star x ⬝ᵥ ((1 + t • K) *ᵥ x) =
          ‖WithLp.toLp 2 x‖ ^ 2 + t * (star x ⬝ᵥ (K *ᵥ x)) := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul]
      simp [smul_eq_mul, hself]
    have hnorm_sq_pos : 0 < ‖WithLp.toLp 2 x‖ ^ 2 := by
      have hxLp : WithLp.toLp 2 x ≠ 0 := by
        exact fun h => hx (WithLp.toLp_injective 2 h)
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hxLp)
    have hcoeff_pos : 0 < 1 - |t| * ‖K‖ := by
      linarith
    have hlower :
        (1 - |t| * ‖K‖) * ‖WithLp.toLp 2 x‖ ^ 2 ≤ star x ⬝ᵥ ((1 + t • K) *ᵥ x) := by
      rw [hrewrite]
      nlinarith
    exact lt_of_lt_of_le (mul_pos hcoeff_pos hnorm_sq_pos) hlower


/-
Let S^n be the vector space of real n × n symmetric matrices, let S_{+ +}^n = {X∈ S^n| Xsucc 0}, let
diag(X)∈ ℝ^n denote the diagonal of X, let 1∈ ℝ^n be the all - ones vector, and let C∈ S^n. Consider
the log - det semidefinite program minimize & tr(CX) - logdet X; subject to & diag(X) = 1, array
with
variable X∈ S^n and objective domain restricted to X∈ S_{+ +}^n. Show that X is optimal if and only
if Xsucc 0, X^{- 1} - C is diagonal, diag(X) = 1. 8. 26
-/
theorem logDetSemidefiniteProgram_optimality_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : LogDetSemidefiniteProgram n) (X : Matrix n n ℝ) :
    P.isFeasible X ∧
      IsMinOn (fun Y : Matrix n n ℝ => P.objective Y)
        {Y | P.isFeasible Y} X ↔
      X.IsSymm ∧
      X.PosDef ∧
      (∃ d : n → ℝ, X⁻¹ - P.C = Matrix.diagonal d) ∧
      X.diag = fun _ => (1 : ℝ) := by
  constructor
  · rintro ⟨hFeasible, hMin⟩
    rcases hFeasible with ⟨hXsymm, hXpos, hXd⟩
    refine ⟨hXsymm, hXpos, ?_, hXd⟩
    -- Route correction: instead of searching for a global matrix derivative, restrict the
    -- objective to feasible off-diagonal lines `t ↦ X + t • Hᵢⱼ`, use the already-proved
    -- positivity lemma to keep the line feasible near `0`, and then apply Fermat along that
    -- one-variable slice.
    have hOffDiag :
        ∀ i j : n, i ≠ j → (X⁻¹ - P.C) i j = 0 := by
      intro i j hij
      let H : Matrix n n ℝ := Matrix.single i j 1 + Matrix.single j i 1
      have hHsymm : H.IsSymm := by
        -- The chosen basis direction is symmetric by construction.
        simp [H, Matrix.IsSymm, Matrix.transpose_add, add_comm]
      have hHdiag : H.diag = 0 := by
        -- The perturbation only changes off-diagonal entries, so its diagonal vanishes.
        ext a
        have hdiag1 : Matrix.single i j (1 : ℝ) a a = 0 := by
          by_cases hia : i = a
          · have hja : ¬ j = a := by
              intro hja
              exact hij (hia.trans hja.symm)
            simp [Matrix.single, hia, hja]
          · simp [Matrix.single, hia]
        have hdiag2 : Matrix.single j i (1 : ℝ) a a = 0 := by
          by_cases hja : j = a
          · have hia : ¬ i = a := by
              intro hia
              exact hij (hia.trans hja.symm)
            simp [Matrix.single, hja, hia]
          · simp [Matrix.single, hja]
        simp [H, Matrix.diag, hdiag1, hdiag2]
      -- Keep the affine feasibility constraints along the line and only prove openness of
      -- positive definiteness.
      have hLineFeasible : ∀ᶠ t : ℝ in 𝓝 0, P.isFeasible (X + t • H) := by
        let T : Matrix n n ℝ := CFC.sqrt X
        let K : Matrix n n ℝ := T⁻¹ * H * T⁻¹
        have hTpos : T.PosDef := by
          -- The positive square root of a positive definite matrix is positive definite.
          exact Matrix.isStrictlyPositive_iff_posDef.mp (hXpos.isStrictlyPositive.sqrt)
        have hTunit : IsUnit T := hTpos.isUnit
        have hTdet : IsUnit (Matrix.det T) := (Matrix.isUnit_iff_isUnit_det T).mp hTunit
        have hTtrans : Tᵀ = T := by
          simpa [T] using hTpos.isHermitian.eq
        have hTstar : star T = T := by
          simp [Matrix.star_eq_conjTranspose, hTtrans]
        have hTinvsymm : T⁻¹.IsSymm := by
          -- Symmetry is preserved under inversion.
          change (T⁻¹)ᵀ = T⁻¹
          rw [Matrix.transpose_nonsing_inv]
          simpa using congrArg (fun A : Matrix n n ℝ => A⁻¹) hTtrans
        have hKsymm : K.IsSymm := by
          -- Conjugating a symmetric matrix by a symmetric inverse preserves symmetry.
          change (T⁻¹ * H * T⁻¹)ᵀ = T⁻¹ * H * T⁻¹
          simp [Matrix.transpose_mul, hTinvsymm.eq, hHsymm.eq, Matrix.mul_assoc]
        have hTT : T * T = X := by
          -- `T` squares back to `X`.
          simpa [T] using CFC.sqrt_mul_sqrt_self X (show 0 ≤ X from hXpos.posSemidef.nonneg)
        have hTKT : T * K * T = H := by
          -- Undo the conjugation defining `K`.
          calc
            T * K * T = (T * T⁻¹) * H * (T⁻¹ * T) := by
              simp [K, Matrix.mul_assoc]
            _ = H := by
              simp [Matrix.mul_nonsing_inv _ hTdet, Matrix.nonsing_inv_mul _ hTdet]
        have hεpos : 0 < (1 : ℝ) / (‖K‖ + 1) := by positivity
        have hsmall :
            ∀ᶠ t : ℝ in 𝓝 0, |t| < (1 : ℝ) / (‖K‖ + 1) := by
          simpa [Metric.ball, Real.dist_eq, abs_sub_comm] using
            (Metric.ball_mem_nhds (0 : ℝ) hεpos)
        filter_upwards [hsmall] with t ht
        have htK : |t| * ‖K‖ < 1 := by
          have hfrac :
              (1 : ℝ) / (‖K‖ + 1) * ‖K‖ < 1 := by
            have hden : 0 < ‖K‖ + 1 := by positivity
            have hlt : ‖K‖ < ‖K‖ + 1 := by linarith [norm_nonneg K]
            have hdiv : ‖K‖ / (‖K‖ + 1) < 1 := by
              exact (div_lt_one hden).2 hlt
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
          have hmul_le :
              |t| * ‖K‖ ≤ (1 : ℝ) / (‖K‖ + 1) * ‖K‖ := by
            exact mul_le_mul_of_nonneg_right (le_of_lt ht) (norm_nonneg K)
          exact lt_of_le_of_lt hmul_le hfrac
        have hMidPos : (1 + t • K).PosDef := by
          -- Small symmetric perturbations of the identity stay positive definite.
          exact Matrix.isStrictlyPositive_iff_posDef.mp
            (isStrictlyPositive_one_add_smul_of_isSymm_norm_mul_lt_one K hKsymm htK)
        have hPos : (X + t • H).PosDef := by
          -- Conjugate the positive perturbation back by `sqrt X`.
          have hConj :
              (T * (1 + t • K) * star T).PosDef := by
            exact (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := 1 + t • K)
              (U := T) hTunit).2 hMidPos
          have hConjEq : T * (1 + t • K) * star T = X + t • H := by
            calc
              T * (1 + t • K) * star T = T * (1 + t • K) * T := by simp [hTstar]
              _ = T * T + t • (T * K * T) := by
                rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul,
                  Matrix.smul_mul, Matrix.mul_assoc]
              _ = X + t • H := by rw [hTT, hTKT]
          simpa [hConjEq] using hConj
        have hDiagLine : (X + t • H).diag = fun _ => (1 : ℝ) := by
          -- The diagonal constraint is preserved because `H.diag = 0`.
          ext a
          have hXa : X a a = 1 := by simpa [Matrix.diag] using congrFun hXd a
          have hHa : H a a = 0 := by simpa [Matrix.diag] using congrFun hHdiag a
          simp [Matrix.diag, hXa, hHa]
        exact ⟨hXsymm.add (hHsymm.smul t), hPos, hDiagLine⟩
      -- Differentiate the objective along the feasible line in direction `H`.
      let M : Matrix n n ℝ := X⁻¹ * H
      have hTraceLine :
          HasDerivAt (fun t : ℝ => Matrix.trace (P.C * (X + t • H)))
            (Matrix.trace (P.C * H)) 0 := by
        -- The trace term is affine in `t`.
        convert (((hasDerivAt_id (0 : ℝ)).mul_const (Matrix.trace (P.C * H))).const_add
          (Matrix.trace (P.C * X))) using 1
        · ext t
          simp [Matrix.mul_add, Matrix.trace_add, smul_eq_mul]
        · simp
      let q : Polynomial ℝ := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) •
        M.map (Polynomial.C : ℝ →+* Polynomial ℝ))).divX.divX
      have hRemainder :
          HasDerivAt (fun t : ℝ => q.eval t * t ^ 2) 0 0 := by
        -- The quadratic remainder has zero derivative at `0`.
        simpa using (q.hasDerivAt (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).pow 2)
      have hDetOne :
          HasDerivAt (fun t : ℝ => Matrix.det (1 + t • M)) (Matrix.trace M) 0 := by
        -- `det (1 + tM)` has first-order term `trace M * t`.
        convert ((((hasDerivAt_id (0 : ℝ)).mul_const (Matrix.trace M)).const_add 1).add
          hRemainder) using 1
        · ext t
          simpa [q, mul_comm] using (Matrix.det_one_add_smul t M)
        · ring
      have hXdet_ne : Matrix.det X ≠ 0 := ne_of_gt hXpos.det_pos
      have hDetLine :
          HasDerivAt (fun t : ℝ => Matrix.det (X + t • H))
            (Matrix.det X * Matrix.trace M) 0 := by
        have hXdet : IsUnit (Matrix.det X) := (Matrix.isUnit_iff_isUnit_det X).mp hXpos.isUnit
        convert (hDetOne.const_mul (Matrix.det X)) using 1
        ext t
        have hXM : X * M = H := by
          calc
            X * M = X * (X⁻¹ * H) := by rfl
            _ = (X * X⁻¹) * H := by rw [Matrix.mul_assoc]
            _ = H := by rw [Matrix.mul_nonsing_inv _ hXdet, one_mul]
        have hExpand : X * (1 + t • M) = X + t • H := by
          -- Factor the perturbation through `X`.
          calc
            X * (1 + t • M) = X + t • (X * M) := by
              rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
            _ = X + t • H := by rw [hXM]
        rw [← hExpand, Matrix.det_mul]
      have hLogDetLine :
          HasDerivAt (fun t : ℝ => logDet (X + t • H)) (Matrix.trace M) 0 := by
        -- Chain the determinant derivative with the real logarithm.
        have hdet0 : Matrix.det (X + (0 : ℝ) • H) ≠ 0 := by simpa using hXdet_ne
        simpa [logDet, M, hXdet_ne] using (hDetLine.log hdet0)
      have hObjectiveLine :
          HasLineDerivAt ℝ (fun Y : Matrix n n ℝ => P.objective Y)
            (Matrix.trace ((P.C - X⁻¹) * H)) X H := by
        -- Combine the trace derivative with the log-determinant derivative.
        change HasDerivAt (fun t : ℝ => P.objective (X + t • H))
          (Matrix.trace ((P.C - X⁻¹) * H)) 0
        simpa [LogDetSemidefiniteProgram.objective, M, Matrix.sub_mul, Matrix.trace_sub] using
          hTraceLine.sub hLogDetLine
      have hTraceZero : Matrix.trace ((P.C - X⁻¹) * H) = 0 := by
        -- Global optimality on the feasible set forces the line derivative to vanish.
        exact hMin.hasLineDerivAt_eq_zero hObjectiveLine hLineFeasible
      have hAsymm : (P.C - X⁻¹).IsSymm := by
        -- Both summands are symmetric.
        have hXinvSymm : X⁻¹.IsSymm := by
          change (X⁻¹)ᵀ = X⁻¹
          rw [Matrix.transpose_nonsing_inv]
          simpa using congrArg (fun A : Matrix n n ℝ => A⁻¹) hXsymm
        exact P.C_symm.sub hXinvSymm
      have hTraceOff :
          Matrix.trace ((P.C - X⁻¹) * H) = 2 * (P.C - X⁻¹) i j := by
        -- The special direction `H` extracts the `(i,j)` entry via `trace_mul_single`.
        calc
          Matrix.trace ((P.C - X⁻¹) * H)
              = Matrix.trace ((P.C - X⁻¹) * Matrix.single i j 1) +
                  Matrix.trace ((P.C - X⁻¹) * Matrix.single j i 1) := by
                  simp [H, Matrix.mul_add, Matrix.trace_add]
          _ = (P.C - X⁻¹) j i + (P.C - X⁻¹) i j := by
                simp [Matrix.trace_mul_single]
          _ = 2 * (P.C - X⁻¹) i j := by
                rw [hAsymm.apply i j]
                ring
      have hEntry : (P.C - X⁻¹) i j = 0 := by
        rw [hTraceOff] at hTraceZero
        linarith
      -- Convert the vanishing statement to the target sign convention.
      have hSign : (X⁻¹ - P.C) i j = -((P.C - X⁻¹) i j) := by
        simp [sub_eq_add_neg, add_comm]
      rw [hSign, hEntry]
      ring
    -- Once all off-diagonal entries vanish, the stationarity matrix is diagonal.
    have hIsDiag : (X⁻¹ - P.C).IsDiag := by
      intro i j hij
      exact hOffDiag i j hij
    refine ⟨Matrix.diag (X⁻¹ - P.C), ?_⟩
    simpa using ((Matrix.isDiag_iff_diagonal_diag (X⁻¹ - P.C)).mp hIsDiag).symm
  · rintro ⟨hXsymm, hXpos, hdiag, hXd⟩
    refine ⟨⟨hXsymm, hXpos, hXd⟩, ?_⟩
    intro Y hY
    rcases hY with ⟨hYsymm, hYpos, hYd⟩
    rcases hdiag with ⟨d, hd⟩
    have hgap := objective_gap_eq_barrier_gap P X Y hXpos hYpos hXd hYd hd
    have hApos : (CFC.sqrt (X⁻¹) * Y * CFC.sqrt (X⁻¹)).PosDef := by
      let S := CFC.sqrt (X⁻¹)
      have hSpos : S.PosDef := by
        -- Conjugating by the positive square root preserves positive definiteness.
        exact Matrix.isStrictlyPositive_iff_posDef.mp (hXpos.inv.isStrictlyPositive.sqrt)
      have hSeq : Sᵀ = S := by
        simpa [S] using hSpos.isHermitian.eq
      have hSunit : IsUnit S := hSpos.isUnit
      have hconj : (S * Y * star S).PosDef := by
        exact (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := Y) (U := S) hSunit).2 hYpos
      simpa [S, Matrix.star_eq_conjTranspose, hSeq] using hconj
    have hnonneg :=
      trace_sub_log_det_nonneg_of_posDef (CFC.sqrt (X⁻¹) * Y * CFC.sqrt (X⁻¹)) hApos
    have hgap_nonneg : 0 ≤ P.objective Y - P.objective X := by
      simpa [hgap] using hnonneg
    have hle : P.objective X ≤ P.objective Y := by
      linarith
    exact hle

end «problem-12»
