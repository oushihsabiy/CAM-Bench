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

namespace «problem-111»

/- [BLOCK Exercise 4.47-(c) | 11 | defn]
Given a partial symmetric matrix A, a completion is a symmetric matrix X that agrees with A on every
specified entry.
-/
def IsCompletion {n : Type*} (specified : Set (n × n)) (A X : Matrix n n ℝ) : Prop :=
  X.IsSymm ∧ ∀ ⦃i j : n⦄, (i, j) ∈ specified → X i j = A i j

/- [BLOCK Exercise 4.47-(c) | 12 | defn]
A positive definite completion of a partial symmetric matrix A is a completion X that is positive
definite.
-/
def IsPosDefCompletion {n : Type*} [Fintype n] [DecidableEq n]
    (specified : Set (n × n)) (A X : Matrix n n ℝ) : Prop :=
  IsCompletion specified A X ∧ X.PosDef

/- [BLOCK Exercise 4.47-(c) | 13 | defn]
A maximum-determinant completion of a partial symmetric matrix A is a positive definite completion X
whose determinant is at least the determinant of every other positive definite completion of A.
-/
def IsMaxDetCompletion {n : Type*} [Fintype n] [DecidableEq n]
    (specified : Set (n × n)) (A X : Matrix n n ℝ) : Prop :=
  IsPosDefCompletion specified A X ∧
    ∀ Y : Matrix n n ℝ, IsPosDefCompletion specified A Y → Y.det ≤ X.det

/-- Any specified diagonal entry is positive once a positive definite completion exists. -/
lemma specifiedDiagonalPositive
    {n : Type*} [Fintype n] [DecidableEq n]
    (specified : Set (n × n)) (A : Matrix n n ℝ)
    (hdiag : ∀ i : n, (i, i) ∈ specified)
    (hex : ∃ X : Matrix n n ℝ, IsPosDefCompletion specified A X) :
    ∀ i : n, 0 < A i i := by
  intro i
  rcases hex with ⟨X, hX⟩
  rcases hX with ⟨hXcompletion, hXpos⟩
  -- The completion witness identifies the diagonal entry of `X` with the prescribed diagonal data.
  have hXi : X i i = A i i := hXcompletion.2 (hdiag i)
  -- Positive definiteness forces every diagonal entry of the witness to be strictly positive.
  have hXi_pos : 0 < X i i := Matrix.PosDef.diag_pos hXpos
  simpa [← hXi] using hXi_pos

namespace IsCompletion

/-- The midpoint of two completions is again a completion of the same partial matrix. -/
lemma midpoint
    {n : Type*} (specified : Set (n × n)) (A X Y : Matrix n n ℝ)
    (hX : IsCompletion specified A X) (hY : IsCompletion specified A Y) :
    IsCompletion specified A ((1 / 2 : ℝ) • (X + Y)) := by
  constructor
  · -- Symmetry is preserved by addition and scalar multiplication.
    simpa using (hX.1.add hY.1).smul (1 / 2 : ℝ)
  · intro i j hij
    -- On each specified entry the midpoint simplifies to the common prescribed value.
    rw [Matrix.smul_apply, Matrix.add_apply, hX.2 hij, hY.2 hij]
    have hhalf : (1 / 2 : ℝ) * (2 * A i j) = A i j := by ring
    simpa [smul_eq_mul, two_mul, mul_assoc] using hhalf

end IsCompletion

namespace IsMaxDetCompletion

/-- Two maximum-determinant completions necessarily have the same determinant. -/
lemma det_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {specified : Set (n × n)} {A X Y : Matrix n n ℝ}
    (hX : IsMaxDetCompletion specified A X) (hY : IsMaxDetCompletion specified A Y) :
    X.det = Y.det := by
  -- Each completion is admissible for the other one's maximality inequality.
  apply le_antisymm
  · exact hY.2 X hX.1
  · exact hX.2 Y hY.1

end IsMaxDetCompletion

/- [BLOCK Exercise 4.47-(c) | 14 | thm]
Let A be a partial real symmetric matrix with symmetric specified pattern and all diagonal entries
specified. Assume A has at least one positive definite completion. Prove that the positive definite
completion with maximum determinant is unique.
-/
theorem maxDetCompletion_unique
    {n : Type*} [Fintype n] [DecidableEq n]
    (specified : Set (n × n)) (A : Matrix n n ℝ)
    (hA : A.IsSymm)
    (hspecified_symm : ∀ ⦃i j : n⦄, (i, j) ∈ specified ↔ (j, i) ∈ specified)
    (hdiag : ∀ i : n, (i, i) ∈ specified)
    (hex : ∃ X : Matrix n n ℝ, IsPosDefCompletion specified A X) :
    ∃! X : Matrix n n ℝ, IsMaxDetCompletion specified A X := by
  classical
  let _ := hA
  let _ := hspecified_symm
  by_cases hne : Nonempty n
  · -- Route correction: keep the compactness/maximization argument local instead of splitting it
    -- into several large auxiliary declarations.
    have hdiag_pos : ∀ i : n, 0 < A i i := specifiedDiagonalPositive specified A hdiag hex
    let K : Set (Matrix n n ℝ) := {X | IsCompletion specified A X ∧ X.PosSemidef}
    have hK_nonempty : K.Nonempty := by
      rcases hex with ⟨X, hX⟩
      rcases hX with ⟨hXcompletion, hXpos⟩
      exact ⟨X, hXcompletion, hXpos.posSemidef⟩
    -- The diagonal positivity extracted above is the fixed numerical input for the later
    -- compactness bound on all positive-semidefinite completions.
    have hdiag_sum_pos : 0 < ∑ i, A i i := by
      exact Finset.sum_pos (fun i _ => hdiag_pos i) Finset.univ_nonempty
    let C : ℝ := ∑ i, A i i
    have hC_pos : 0 < C := hdiag_sum_pos
    have hentry_abs_le :
        ∀ ⦃X : Matrix n n ℝ⦄, X ∈ K → ∀ i j : n, |X i j| ≤ C := by
      intro X hXK i j
      rcases hXK with ⟨hXcompletion, hXpsd⟩
      let e : Fin 2 → n := ![i, j]
      -- The `2 × 2` principal submatrix stays positive semidefinite, so its determinant is
      -- nonnegative.
      have hdet_nonneg : 0 ≤ (X.submatrix e e).det :=
        Matrix.PosSemidef.det_nonneg (hXpsd.submatrix e)
      have hentry_sq :
          (X i j) ^ 2 ≤ X i i * X j j := by
        have hsymm_ij : X j i = X i j := hXcompletion.1.apply i j
        have hdet_eval : (X.submatrix e e).det = X i i * X j j - X i j * X i j := by
          simp [e, Matrix.det_fin_two, hsymm_ij]
        rw [hdet_eval] at hdet_nonneg
        nlinarith
      -- The prescribed diagonal entries are fixed, so each diagonal entry is bounded by the
      -- common diagonal sum `C`.
      have hXii_nonneg : 0 ≤ X i i := hXpsd.diag_nonneg
      have hXjj_nonneg : 0 ≤ X j j := hXpsd.diag_nonneg
      have hXii_le : X i i ≤ C := by
        change X i i ≤ ∑ k, A k k
        rw [show X i i = A i i from hXcompletion.2 (hdiag i)]
        exact Finset.single_le_sum (fun k _ ↦ le_of_lt (hdiag_pos k)) (Finset.mem_univ i)
      have hXjj_le : X j j ≤ C := by
        change X j j ≤ ∑ k, A k k
        rw [show X j j = A j j from hXcompletion.2 (hdiag j)]
        exact Finset.single_le_sum (fun k _ ↦ le_of_lt (hdiag_pos k)) (Finset.mem_univ j)
      have hsq_le : (X i j) ^ 2 ≤ C ^ 2 := by
        nlinarith [hentry_sq, hXii_nonneg, hXjj_nonneg, hXii_le, hXjj_le, hC_pos.le]
      exact abs_le_of_sq_le_sq hsq_le hC_pos.le
    have hK_closed : IsClosed K := by
      have hsymm_closed : IsClosed {X : Matrix n n ℝ | X.IsSymm} := by
        simpa [Matrix.IsSymm] using
          (isClosed_eq (Continuous.matrix_transpose continuous_id) continuous_id)
      have hspecified_closed :
          IsClosed {X : Matrix n n ℝ | ∀ p : n × n, p ∈ specified → X p.1 p.2 = A p.1 p.2} := by
        classical
        rw [show {X : Matrix n n ℝ | ∀ p : n × n, p ∈ specified → X p.1 p.2 = A p.1 p.2} =
            ⋂ p : n × n, if hp : p ∈ specified then {X : Matrix n n ℝ | X p.1 p.2 = A p.1 p.2}
              else Set.univ by
              ext X
              simp only [Set.mem_setOf_eq, Set.mem_iInter]
              constructor
              · intro h p
                by_cases hp : p ∈ specified
                · simpa [hp] using h p hp
                · simp [hp]
              · intro h p hp
                simpa [hp] using h p]
        refine isClosed_iInter ?_
        intro p
        by_cases hp : p ∈ specified
        · simpa [hp] using
            (isClosed_eq (by fun_prop)
              (continuous_const : Continuous fun _ : Matrix n n ℝ => A p.1 p.2))
        · simp [hp]
      have hcompletion_closed : IsClosed {X : Matrix n n ℝ | IsCompletion specified A X} := by
        have hEq :
            {X : Matrix n n ℝ | IsCompletion specified A X} =
              {X : Matrix n n ℝ | X.IsSymm} ∩
                {X : Matrix n n ℝ |
                  ∀ p : n × n, p ∈ specified → X p.1 p.2 = A p.1 p.2} := by
          ext X
          constructor
          · intro hX
            exact ⟨hX.1, fun p hp ↦ hX.2 hp⟩
          · rintro ⟨hXsymm, hXspec⟩
            exact ⟨hXsymm, fun {_ _} hij ↦ hXspec _ hij⟩
        rw [hEq]
        exact hsymm_closed.inter hspecified_closed
      have hpsd_closed : IsClosed {X : Matrix n n ℝ | X.PosSemidef} := by
        have hhermitian_closed : IsClosed {X : Matrix n n ℝ | X.IsHermitian} := by
          simpa [Matrix.IsHermitian] using
            (isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id)
        have hquadratic_closed (x : n →₀ ℝ) :
            IsClosed
              {X : Matrix n n ℝ |
                0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * X i j * xj} := by
          let q : Matrix n n ℝ → ℝ :=
            fun X => x.support.sum fun i => x.support.sum fun j => star (x i) * X i j * x j
          have hq_cont : Continuous q := by
            refine continuous_finset_sum _ ?_
            intro i hi
            refine continuous_finset_sum _ ?_
            intro j hj
            have hterm : Continuous fun X : Matrix n n ℝ => star (x i) * X i j * x j := by
              fun_prop
            simpa [q] using hterm
          have hq_eq :
              q = fun X : Matrix n n ℝ =>
                x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * X i j * xj := by
            funext X
            simp [q, Finsupp.sum]
          rw [show {X : Matrix n n ℝ |
                0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * X i j * xj} =
                {X : Matrix n n ℝ | 0 ≤ q X} by
                ext X
                simp [hq_eq]]
          exact isClosed_le continuous_const hq_cont
        have hEq :
            {X : Matrix n n ℝ | X.PosSemidef} =
              {X : Matrix n n ℝ | X.IsHermitian} ∩
                ⋂ x : n →₀ ℝ,
                  {X : Matrix n n ℝ |
                    0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * X i j * xj} := by
          ext X
          simp [Matrix.PosSemidef]
        simpa [hEq] using hhermitian_closed.inter (isClosed_iInter hquadratic_closed)
      simpa [K] using hcompletion_closed.inter hpsd_closed
    have hK_bounded :
        @Bornology.IsBounded (n → n → ℝ) Pi.instBornology (K : Set (n → n → ℝ)) := by
      have hbox_bounded_fun :
          @Bornology.IsBounded (n → n → ℝ) Pi.instBornology
            (Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n => Set.Icc (-C) C) := by
        simpa using
          (Bornology.IsBounded.pi fun _ : n =>
            (Bornology.IsBounded.pi fun _ : n => Metric.isBounded_Icc (-C) C))
      have hbox_bounded :
          Bornology.IsBounded
            (Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n => Set.Icc (-C) C :
              Set (Matrix n n ℝ)) := by
        simpa using hbox_bounded_fun
      have hsubset :
          K ⊆
            (Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n => Set.Icc (-C) C :
              Set (Matrix n n ℝ)) := by
        intro X hXK i _ j _
        simpa [Set.mem_Icc, abs_le] using hentry_abs_le hXK i j
      have hbounded_fun :
          @Bornology.IsBounded (n → n → ℝ) Pi.instBornology (K : Set (n → n → ℝ)) :=
        hbox_bounded.subset hsubset
      exact hbounded_fun
    let Kfun : Set (n → n → ℝ) := K
    have hK_compact : IsCompact K := by
      have hK_closed_fun : IsClosed Kfun := by
        simpa [Kfun] using hK_closed
      have hK_bounded_fun : Bornology.IsBounded Kfun := by
        simpa [Kfun] using hK_bounded
      have hK_compact_fun : IsCompact Kfun :=
        Metric.isCompact_of_isClosed_isBounded hK_closed_fun hK_bounded_fun
      simpa [Kfun] using hK_compact_fun
    obtain ⟨Xmax, hXmaxK, hXmax_det_max⟩ :=
      hK_compact.exists_isMaxOn hK_nonempty (Continuous.matrix_det continuous_id).continuousOn
    rcases hXmaxK with ⟨hXmax_completion, hXmax_psd⟩
    rcases hex with ⟨W, hWcompletion, hWpos⟩
    have hWmemK : W ∈ K := ⟨hWcompletion, hWpos.posSemidef⟩
    -- Comparing the maximizer to the positive definite witness upgrades it from PSD to PD.
    have hXmax_det_pos : 0 < Xmax.det := by
      exact lt_of_lt_of_le (Matrix.PosDef.det_pos hWpos) (hXmax_det_max hWmemK)
    have hXmax_pos : Xmax.PosDef := by
      refine hXmax_psd.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det Xmax).mpr ?_)
      exact isUnit_iff_ne_zero.mpr (ne_of_gt hXmax_det_pos)
    have hXmax_isMax : IsMaxDetCompletion specified A Xmax := by
      constructor
      · exact ⟨hXmax_completion, hXmax_pos⟩
      · intro Y hY
        exact hXmax_det_max ⟨hY.1, hY.2.posSemidef⟩
    refine ⟨Xmax, hXmax_isMax, ?_⟩
    intro Y hYmax
    by_contra hYX
    have hdet_eq : Y.det = Xmax.det := IsMaxDetCompletion.det_eq hYmax hXmax_isMax
    let Z : Matrix n n ℝ := (1 / 2 : ℝ) • (Y + Xmax)
    have hZ_completion : IsCompletion specified A Z :=
      IsCompletion.midpoint specified A Y Xmax hYmax.1.1 hXmax_completion
    have hZ_pos : Z.PosDef := by
      -- The admissible set is convex, so the midpoint of two positive definite completions
      -- remains positive definite.
      exact Matrix.PosDef.smul (Matrix.PosDef.add hYmax.1.2 hXmax_pos) (by norm_num)
    have hmidpoint_det_gt : Y.det < Z.det := by
      let S : Matrix n n ℝ := CFC.sqrt Y
      let Wnorm : Matrix n n ℝ := S⁻¹ᵀ * Xmax * S⁻¹
      -- Normalize by the positive square root of `Y` so the comparison reduces to unit determinant.
      have hS_pos : S.PosDef := by
        exact Matrix.isStrictlyPositive_iff_posDef.mp (hYmax.1.2.isStrictlyPositive.sqrt)
      have hS_unit : IsUnit S := hS_pos.isUnit
      letI : Invertible S := hS_unit.invertible
      have hS_t : Sᵀ = S := by
        simpa [Matrix.IsHermitian, S] using hS_pos.1.eq
      have hSinv_t : S⁻¹ᵀ = S⁻¹ := by
        simpa [Matrix.IsHermitian, S] using (Matrix.IsHermitian.inv hS_pos.1).eq
      have hSinv_unit : IsUnit (S⁻¹) := by
        exact isUnit_of_invertible (S⁻¹)
      have hWnorm_pos : Wnorm.PosDef := by
        -- Conjugating `Xmax` by the inverse square root preserves positive definiteness.
        have htmp : ((S⁻¹)ᴴ * Xmax * S⁻¹).PosDef :=
          hXmax_pos.conjTranspose_mul_mul_same (B := S⁻¹)
            (Matrix.mulVec_injective_of_isUnit hSinv_unit)
        simpa [Wnorm, hSinv_t] using htmp
      have hsqrt_self : CFC.sqrt Y * CFC.sqrt Y = Y := by
        simpa using CFC.sqrt_mul_sqrt_self (a := Y) (ha := hYmax.1.2.isStrictlyPositive.nonneg)
      have hSdet_sq : S.det * S.det = Y.det := by
        -- The square root identity transfers directly to determinants.
        simpa [S, Matrix.det_mul] using congrArg Matrix.det hsqrt_self
      have hWnorm_det : Wnorm.det = 1 := by
        -- The normalization makes the determinant equal to `det Xmax / det Y`, hence `1`.
        calc
          Wnorm.det = (S.det)⁻¹ * Xmax.det * (S.det)⁻¹ := by
            simp [Wnorm, Matrix.det_mul, Matrix.det_nonsing_inv]
          _ = (S.det)⁻¹ * Y.det * (S.det)⁻¹ := by rw [← hdet_eq]
          _ = 1 := by
            have hSdet_ne : S.det ≠ 0 := ne_of_gt (Matrix.PosDef.det_pos hS_pos)
            rw [← hSdet_sq]
            field_simp [hSdet_ne]
      have hWnorm_ne : Wnorm ≠ 1 := by
        -- If the normalized matrix were the identity, then `Xmax` would have to equal `Y`.
        intro hW1
        have htmpY : Sᵀ * S = Y := by
          simpa [hS_t, S] using hsqrt_self
        have htmp := congrArg (fun M : Matrix n n ℝ => Sᵀ * M * S) hW1
        have hXeqY : Xmax = Y := by
          have hXeqS : Xmax = S * S := by
            simpa [Wnorm, Matrix.mul_assoc, hS_t, hSinv_t] using htmp
          simpa [← htmpY, hS_t] using hXeqS
        exact hYX hXeqY.symm
      have hZ_eq : Z = Sᵀ * ((1 / 2 : ℝ) • (1 + Wnorm)) * S := by
        -- Rewrite the midpoint using the normalized matrix.
        have hYeq : Y = Sᵀ * S := by
          simpa [hS_t, S] using hsqrt_self.symm
        have hXeq : Xmax = Sᵀ * Wnorm * S := by
          have : Sᵀ * Wnorm * S = Xmax := by
            simp [Wnorm, Matrix.mul_assoc, hS_t, hSinv_t]
          exact this.symm
        calc
          Z = (1 / 2 : ℝ) • (Sᵀ * S + Sᵀ * Wnorm * S) := by
            rw [show Z = (1 / 2 : ℝ) • (Y + Xmax) by rfl, hYeq, hXeq]
          _ = (1 / 2 : ℝ) • (Sᵀ * (1 + Wnorm) * S) := by
            simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
          _ = Sᵀ * ((1 / 2 : ℝ) • (1 + Wnorm)) * S := by
            calc
              (1 / 2 : ℝ) • (Sᵀ * (1 + Wnorm) * S)
                  = (1 / 2 : ℝ) • (Sᵀ * ((1 + Wnorm) * S)) := by rw [Matrix.mul_assoc]
              _ = Sᵀ * (((1 / 2 : ℝ) • (1 + Wnorm)) * S) := by
                rw [Matrix.smul_mul, Matrix.mul_smul]
              _ = Sᵀ * ((1 / 2 : ℝ) • (1 + Wnorm)) * S := by rw [Matrix.mul_assoc]
      have hZ_det :
          Z.det = Y.det * Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) := by
        -- Taking determinants isolates the strict growth in a single normalized factor.
        calc
          Z.det = (Sᵀ * ((1 / 2 : ℝ) • (1 + Wnorm)) * S).det := by rw [hZ_eq]
          _ = S.det * Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) * S.det := by
            rw [Matrix.det_mul, Matrix.det_mul]
            simp [hS_t]
          _ = Y.det * Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) := by
            rw [← hSdet_sq]
            ring
      have hfactor_gt :
          1 < Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) := by
        let eig : n → ℝ := hWnorm_pos.1.eigenvalues
        have hmid_cfc :
            ((1 / 2 : ℝ) • (1 + Wnorm)) = hWnorm_pos.1.cfc (fun x : ℝ => (1 + x) / 2) := by
          let U := hWnorm_pos.1.eigenvectorUnitary
          let D : Matrix n n ℝ := Matrix.diagonal eig
          -- Route correction: rather than expand the midpoint entrywise, diagonalize `Wnorm`
          -- and transport the affine function through the conjugation.
          have hspec : Wnorm = (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U) D := by
            simpa [D, U, eig] using hWnorm_pos.1.spectral_theorem
          conv_lhs => rw [hspec]
          change (1 / 2 : ℝ) • (1 + (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U) D) =
              (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U)
                (Matrix.diagonal ((fun x : ℝ => (1 + x) / 2) ∘ eig))
          rw [← map_one (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U), ← map_add, ← map_smul]
          congr 1
          ext i j
          by_cases hij : i = j
          · subst hij
            simp [D, eig]
            ring
          · simp [D, hij]
        have hdet_mid :
            Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) = ∏ i, ((1 + eig i) / 2 : ℝ) := by
          -- The determinant of the diagonalized midpoint is the product of scalar midpoint factors.
          rw [hmid_cfc]
          simp [Matrix.IsHermitian.cfc, eig, -Unitary.conjStarAlgAut_apply]
        have hprod_eig : ∏ i, eig i = 1 := by
          simpa [eig, hWnorm_pos.1.det_eq_prod_eigenvalues] using hWnorm_det
        have hexists : ∃ i, eig i ≠ 1 := by
          -- Nontriviality of `Wnorm` forces at least one eigenvalue away from `1`.
          by_contra hno
          apply hWnorm_ne
          have hvals : eig = fun _ : n => 1 := by
            funext i
            exact by_contra fun hi => hno ⟨i, hi⟩
          simpa [eig, hvals] using hWnorm_pos.1.spectral_theorem
        have hsqrt_prod : ∏ i, Real.sqrt (eig i) = 1 := by
          -- The geometric mean of the eigenvalues is `1` because their product is `1`.
          calc
            ∏ i, Real.sqrt (eig i) = Real.sqrt (∏ i, eig i) := by
              symm
              exact Real.sqrt_prod Finset.univ (fun i _ => (hWnorm_pos.eigenvalues_pos i).le)
            _ = 1 := by
              simp [hprod_eig]
        have hscalar_amgm : ∀ x : ℝ, 0 ≤ x → Real.sqrt x ≤ (1 + x) / 2 := by
          -- Isolate the scalar inequality so `nlinarith` only sees one real variable.
          intro x hx
          have hsq : 0 ≤ (Real.sqrt x - 1) ^ 2 := sq_nonneg _
          nlinarith [hsq, Real.sq_sqrt hx]
        have hscalar_amgm_strict :
            ∀ x : ℝ, 0 ≤ x → x ≠ 1 → Real.sqrt x < (1 + x) / 2 := by
          -- Strictness comes from the square being strictly positive when `x ≠ 1`.
          intro x hx hx1
          have hsq_pos : 0 < (Real.sqrt x - 1) ^ 2 := by
            apply sq_pos_of_ne_zero
            intro hs
            apply hx1
            exact Real.sqrt_eq_one.mp (sub_eq_zero.mp hs)
          nlinarith [hsq_pos, Real.sq_sqrt hx]
        have hfactor_le : ∀ i, Real.sqrt (eig i) ≤ (1 + eig i) / 2 := by
          -- This is the scalar AM-GM inequality in the form `2√t ≤ 1 + t`.
          intro i
          have heig : 0 ≤ eig i := (hWnorm_pos.eigenvalues_pos i).le
          exact hscalar_amgm (eig i) heig
        have hfactor_lt : ∀ i, eig i ≠ 1 → Real.sqrt (eig i) < (1 + eig i) / 2 := by
          -- A non-unit eigenvalue gives a strict scalar AM-GM inequality.
          intro i hi
          have heig : 0 ≤ eig i := (hWnorm_pos.eigenvalues_pos i).le
          exact hscalar_amgm_strict (eig i) heig hi
        have hprod_lt : ∏ i, Real.sqrt (eig i) < ∏ i, ((1 + eig i) / 2 : ℝ) := by
          -- Multiply the scalar inequalities, using strictness at one eigenvalue.
          apply Finset.prod_lt_prod
          · intro i hi
            exact Real.sqrt_pos.2 (hWnorm_pos.eigenvalues_pos i)
          · intro i hi
            exact hfactor_le i
          · rcases hexists with ⟨i, hi⟩
            exact ⟨i, Finset.mem_univ i, hfactor_lt i hi⟩
        calc
          1 = ∏ i, Real.sqrt (eig i) := hsqrt_prod.symm
          _ < ∏ i, ((1 + eig i) / 2 : ℝ) := hprod_lt
          _ = Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) := hdet_mid.symm
      have hY_det_pos : 0 < Y.det := Matrix.PosDef.det_pos hYmax.1.2
      have hmul :
          Y.det * 1 < Y.det * Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) :=
        mul_lt_mul_of_pos_left hfactor_gt hY_det_pos
      -- Multiplying the strict normalized factor by the positive determinant of `Y` finishes.
      calc
        Y.det = Y.det * 1 := by ring
        _ < Y.det * Matrix.det ((1 / 2 : ℝ) • (1 + Wnorm)) := hmul
        _ = Z.det := hZ_det.symm
    exact (not_lt_of_ge (hYmax.2 Z ⟨hZ_completion, hZ_pos⟩)) hmidpoint_det_gt
  · haveI : IsEmpty n := not_nonempty_iff.mp hne
    let X₀ : Matrix n n ℝ := Classical.choose hex
    have hX₀_pos : IsPosDefCompletion specified A X₀ := Classical.choose_spec hex
    refine ⟨X₀, ?_, ?_⟩
    · constructor
      · exact hX₀_pos
      · intro Y hY
        -- In the empty-index case all matrices coincide, so maximality is automatic.
        have hYX : Y = X₀ := Subsingleton.elim _ _
        simp [hYX]
    · intro Y hY
      -- Uniqueness is also forced by subsingletonity of the ambient matrix space.
      exact Subsingleton.elim _ _

/- [BLOCK Exercise 4.47-(c) | 15 | thm]
With the same setup, let A* be the maximum-determinant positive definite completion. Prove that the
inverse matrix (A*)^{-1} has zero entries at every position that was unspecified in the original
partial matrix.
-/
/-- The normalized determinant curve has derivative equal to the trace of the perturbation. -/
lemma det_one_add_smul_hasDerivAt_zero
    {n : Type*} [Fintype n] [DecidableEq n] (B : Matrix n n ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.det (1 + t • B)) (Matrix.trace B) 0 := by
  let q : Polynomial ℝ :=
    (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • B.map Polynomial.C)).divX.divX
  have hlinear : HasDerivAt (fun t : ℝ => Matrix.trace B * t) (Matrix.trace B) 0 := by
    -- The linear part contributes exactly the trace.
    simpa [mul_comm] using (hasDerivAt_id (0 : ℝ)).const_mul (Matrix.trace B)
  have hq_eval : HasDerivAt (fun t : ℝ => q.eval t) (q.derivative.eval 0) 0 := q.hasDerivAt 0
  have hsq : HasDerivAt (fun t : ℝ => t * t) 0 0 := by
    -- The quadratic remainder has zero derivative at the origin.
    simpa [pow_two] using (hasDerivAt_pow 2 (0 : ℝ))
  have hrem : HasDerivAt (fun t : ℝ => q.eval t * (t * t)) 0 0 := by
    simpa using hq_eval.mul hsq
  have hsum : HasDerivAt (fun t : ℝ => Matrix.trace B * t + q.eval t * (t * t)) (Matrix.trace B) 0 := by
    simpa [Pi.add_apply] using hlinear.add hrem
  convert hsum.const_add 1 using 1
  ext t
  simpa [q, pow_two, add_assoc, add_left_comm, add_comm] using (Matrix.det_one_add_smul t B)

/-- A symmetric real perturbation of the identity stays positive definite for small scalars. -/
lemma isSymm_small_smul_one_posDef
    {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℝ} (hB : B.IsSymm) :
    ∃ ε > 0, ∀ ⦃t : ℝ⦄, |t| < ε → (1 + t • B).PosDef := by
  let hBherm : B.IsHermitian := by
    simpa [Matrix.IsHermitian] using hB
  let eig : n → ℝ := hBherm.eigenvalues
  let bound : ℝ := (∑ k, |eig k|) + 1
  have hbound_pos : 0 < bound := by
    have hsum_nonneg : 0 ≤ ∑ k, |eig k| := by positivity
    nlinarith
  refine ⟨bound⁻¹, by positivity, ?_⟩
  intro t ht
  have hdiag_pos : ∀ k, 0 < 1 + t * eig k := by
    intro k
    have heig_le : |eig k| ≤ ∑ l, |eig l| := by
      exact Finset.single_le_sum (fun l _ ↦ abs_nonneg (eig l)) (Finset.mem_univ k)
    have heig_lt : |eig k| < bound := by
      exact lt_of_le_of_lt heig_le (by simp [bound])
    have habs_mul : |t * eig k| < 1 := by
      rw [abs_mul]
      have ht_bound : |t| * bound < bound⁻¹ * bound :=
        mul_lt_mul_of_pos_right ht hbound_pos
      have ht_bound' : |t| * bound < 1 := by
        simpa [hbound_pos.ne'] using ht_bound
      have hprod : |t| * |eig k| < 1 := by
        have hmul_le : |t| * |eig k| ≤ |t| * bound := by
          exact mul_le_mul_of_nonneg_left (le_of_lt heig_lt) (abs_nonneg _)
        exact lt_of_le_of_lt hmul_le ht_bound'
      exact hprod
    have hlower : -1 < t * eig k := (abs_lt.mp habs_mul).1
    nlinarith
  have hdiag_repr :
      1 + t • B =
        Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hBherm.eigenvectorUnitary
          (Matrix.diagonal fun k => 1 + t * eig k) := by
    conv_lhs => rw [hBherm.spectral_theorem]
    rw [← map_one (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hBherm.eigenvectorUnitary)]
    rw [← map_smul (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hBherm.eigenvectorUnitary)]
    rw [← map_add (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hBherm.eigenvectorUnitary)]
    congr 1
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal, smul_eq_mul, eig]
    · simp [Matrix.diagonal, hab]
  have hdiag_pd : (Matrix.diagonal fun k => 1 + t * eig k).PosDef := by
    -- After diagonalization, positivity reduces to positivity of each scalar factor.
    simpa using (Matrix.posDef_diagonal_iff).2 hdiag_pos
  have hU_unit : IsUnit ((hBherm.eigenvectorUnitary : Matrix.unitaryGroup n ℝ) : Matrix n n ℝ) := by
    simpa using (Unitary.isUnit_coe (U := hBherm.eigenvectorUnitary))
  rw [hdiag_repr]
  -- Conjugating a positive definite diagonal matrix by a unitary preserves positivity.
  simpa [Unitary.conjStarAlgAut_apply] using
    (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (U := ((hBherm.eigenvectorUnitary : Matrix.unitaryGroup n ℝ) : Matrix n n ℝ))
      (x := Matrix.diagonal fun k => 1 + t * eig k) hU_unit).2 hdiag_pd

theorem maxDetCompletion_inv_eq_zero_of_unspecified
    {n : Type*} [Fintype n] [DecidableEq n]
    (specified : Set (n × n)) (A : Matrix n n ℝ)
    (hA : A.IsSymm)
    (hspecified_symm : ∀ ⦃i j : n⦄, (i, j) ∈ specified ↔ (j, i) ∈ specified)
    (hdiag : ∀ i : n, (i, i) ∈ specified)
    (hex : ∃ X : Matrix n n ℝ, IsPosDefCompletion specified A X) :
    ∀ ⦃Astar : Matrix n n ℝ⦄,
      IsMaxDetCompletion specified A Astar →
      ∀ ⦃i j : n⦄, (i, j) ∉ specified → Astar⁻¹ i j = 0 := by
  let _ := hA
  let _ := hex
  intro Astar hmax i j hij_unspec
  let E : Matrix n n ℝ := Matrix.single i j 1 + Matrix.single j i 1
  let S : Matrix n n ℝ := CFC.sqrt Astar
  let B : Matrix n n ℝ := S⁻¹ * E * S⁻¹
  have hAstar_completion : IsCompletion specified A Astar := hmax.1.1
  have hAstar_pos : Astar.PosDef := hmax.1.2
  have hij_ne : i ≠ j := by
    -- An unspecified entry cannot lie on the diagonal because every diagonal entry is specified.
    intro hij
    apply hij_unspec
    simpa [hij] using hdiag i
  have hE_symm : E.IsSymm := by
    -- The perturbation changes the `(i,j)` and `(j,i)` entries symmetrically.
    rw [Matrix.IsSymm]
    ext a b
    by_cases hia : i = a <;> by_cases hjb : j = b <;> by_cases hja : j = a <;>
        by_cases hib : i = b <;>
          simp [E, Matrix.single_apply, hia, hjb, hja, hib, eq_comm] <;> ring
  have hE_spec_zero : ∀ ⦃a b : n⦄, (a, b) ∈ specified → E a b = 0 := by
    have hji_unspec : (j, i) ∉ specified := by
      intro hji
      exact hij_unspec ((hspecified_symm (i := j) (j := i)).mp hji)
    intro a b hab
    -- Unspecified positions are exactly where the perturbation is allowed to be nonzero.
    have hne_ij : ¬ (a = i ∧ b = j) := by
      rintro ⟨rfl, rfl⟩
      exact hij_unspec hab
    have hne_ji : ¬ (a = j ∧ b = i) := by
      rintro ⟨rfl, rfl⟩
      exact hji_unspec hab
    by_cases haij : a = i ∧ b = j
    · exact False.elim (hne_ij haij)
    · by_cases haji : a = j ∧ b = i
      · exact False.elim (hne_ji haji)
      · have hij' : ¬ (i = a ∧ j = b) := by simpa [eq_comm] using haij
        have hji' : ¬ (j = a ∧ i = b) := by simpa [eq_comm] using haji
        simp [E, hij', hji']
  have hS_pos : S.PosDef := by
    -- The positive square root of a positive definite matrix is again positive definite.
    exact Matrix.isStrictlyPositive_iff_posDef.mp (hAstar_pos.isStrictlyPositive.sqrt)
  have hS_unit : IsUnit S := hS_pos.isUnit
  letI : Invertible S := hS_unit.invertible
  have hS_t : Sᵀ = S := by
    -- Over `ℝ`, Hermitian square roots are symmetric.
    simpa [Matrix.IsHermitian, S] using hS_pos.1.eq
  have hSinv_t : S⁻¹ᵀ = S⁻¹ := by
    -- The inverse of a symmetric invertible matrix is symmetric.
    simpa [Matrix.IsHermitian, S] using (Matrix.IsHermitian.inv hS_pos.1).eq
  have hsqrt_self : S * S = Astar := by
    -- This is the defining square-root identity for positive matrices.
    simpa [S] using
      CFC.sqrt_mul_sqrt_self (a := Astar) (ha := hAstar_pos.isStrictlyPositive.nonneg)
  have hB_symm : B.IsSymm := by
    -- Route correction: normalize the perturbation to `1 + t • B` so the derivative formula
    -- is the existing `det (1 + X • B)` theorem rather than a bespoke Jacobi formula at `Astar`.
    have hE_herm : E.IsHermitian := by
      simpa [Matrix.IsHermitian] using hE_symm
    have hB_herm : B.IsHermitian := by
      simpa [B, hSinv_t] using Matrix.isHermitian_conjTranspose_mul_mul (S⁻¹) hE_herm
    simpa [Matrix.IsHermitian] using hB_herm
  have hconj_B : S * B * S = E := by
    -- Conjugating back by `S` recovers the original sparse perturbation.
    simp [B, Matrix.mul_assoc]
  have hperturb_eq (t : ℝ) : S * (1 + t • B) * S = Astar + t • E := by
    -- The normalized perturbation corresponds exactly to changing the unspecified entry.
    calc
      S * (1 + t • B) * S = S * S + t • (S * B * S) := by
        simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = Astar + t • E := by rw [hsqrt_self, hconj_B]
  have hSdet_sq : S.det * S.det = Astar.det := by
    -- Determinants also square under the square-root identity.
    simpa [Matrix.det_mul] using congrArg Matrix.det hsqrt_self
  have hdet_normalized (t : ℝ) :
      Matrix.det (Astar + t • E) = Astar.det * Matrix.det (1 + t • B) := by
    -- Conjugation by `S` factors the determinant into the fixed `det Astar` and the normalized part.
    calc
      Matrix.det (Astar + t • E) = Matrix.det (S * (1 + t • B) * S) := by
        rw [hperturb_eq t]
      _ = S.det * Matrix.det (1 + t • B) * S.det := by
        rw [Matrix.det_mul, Matrix.det_mul]
      _ = Astar.det * Matrix.det (1 + t • B) := by
        rw [← hSdet_sq]
        ring
  obtain ⟨ε, hε_pos, hsmall_pos⟩ := isSymm_small_smul_one_posDef hB_symm
  have hlocal_max :
      IsLocalMax (fun t : ℝ => Matrix.det (1 + t • B)) 0 := by
    -- Every sufficiently small admissible perturbation remains a positive definite completion,
    -- so maximality of `Astar` bounds the normalized determinant from above near `0`.
    refine Metric.eventually_nhds_iff.2 ⟨ε, hε_pos, ?_⟩
    intro t ht
    have ht' : |t| < ε := by
      simpa [Real.dist_eq] using ht
    have hpert_completion : IsCompletion specified A (Astar + t • E) := by
      constructor
      · simpa [E, Matrix.add_apply, Matrix.smul_apply] using
          hAstar_completion.1.add (hE_symm.smul t)
      · intro a b hab
        rw [Matrix.add_apply, Matrix.smul_apply, hAstar_completion.2 hab, hE_spec_zero hab]
        simp
    have hpert_pos : (Astar + t • E).PosDef := by
      -- The small-`t` normalized positivity transports back through the square root.
      have hnorm_pos : (1 + t • B).PosDef := hsmall_pos ht'
      have hconj_pos : (Sᴴ * (1 + t • B) * S).PosDef :=
        hnorm_pos.conjTranspose_mul_mul_same
          (B := S) (Matrix.mulVec_injective_of_isUnit hS_unit)
      simpa [hS_t, hperturb_eq t] using hconj_pos
    have hmax_le :
        Matrix.det (Astar + t • E) ≤ Astar.det :=
      hmax.2 (Astar + t • E) ⟨hpert_completion, hpert_pos⟩
    have hnormalized_le :
        Astar.det * Matrix.det (1 + t • B) ≤ Astar.det := by
      simpa [hdet_normalized t] using hmax_le
    have hAstar_det_pos : 0 < Astar.det := Matrix.PosDef.det_pos hAstar_pos
    have : Matrix.det (1 + t • B) ≤ 1 := by
      nlinarith [hnormalized_le, hAstar_det_pos]
    simpa using this
  have htrace_zero : Matrix.trace B = 0 := by
    -- The derivative of the normalized determinant vanishes at a local maximum.
    exact hlocal_max.hasDerivAt_eq_zero (det_one_add_smul_hasDerivAt_zero B)
  have hAstar_inv_symm : (Astar⁻¹).IsSymm := by
    -- Inverses of symmetric positive definite matrices are symmetric.
    simpa [Matrix.IsHermitian] using (Matrix.IsHermitian.inv hAstar_pos.1)
  have hAstar_inv_eq : Astar⁻¹ = S⁻¹ * S⁻¹ := by
    -- Inverting `Astar = S * S` gives the square of the inverse square root.
    rw [← hsqrt_self, Matrix.mul_inv_rev]
  have htrace_B :
      Matrix.trace B = 2 * Astar⁻¹ i j := by
    -- Cycling the trace reduces the normalized perturbation to the two affected inverse entries.
    calc
      Matrix.trace B = Matrix.trace (S⁻¹ * E * S⁻¹) := by rfl
      _ = Matrix.trace (E * S⁻¹ * S⁻¹) := by
        simpa [Matrix.mul_assoc] using (Matrix.trace_mul_cycle E S⁻¹ S⁻¹).symm
      _ = Matrix.trace (E * Astar⁻¹) := by
        simp [hAstar_inv_eq, Matrix.mul_assoc]
      _ = 2 * Astar⁻¹ i j := by
        rw [show E = Matrix.single i j 1 + Matrix.single j i 1 by rfl, Matrix.add_mul,
          Matrix.trace_add]
        simp only [Matrix.trace_single_mul, one_smul]
        have hsymm_entry : Astar⁻¹ j i = Astar⁻¹ i j := (hAstar_inv_symm.apply j i).symm
        nlinarith
  have hentry_twice_zero : 2 * Astar⁻¹ i j = 0 := by
    simpa [htrace_B] using htrace_zero
  nlinarith

end «problem-111»
