import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-182»
/- [BLOCK Exercise 4.17-(a) | 34 | opt_prob]
Then
\[
\sup\{\operatorname{tr}(AX) \mid X \in S^n,\ \operatorname{tr}(X)=r,\ 0 \preceq X,\ X \preceq I\} = f(A).
\]
-/
structure SpectralTraceMaximization where
  n : Type*
  fintype_n : Fintype n
  decEq_n : DecidableEq n
  A : Matrix n n ℝ
  r : ℝ
  f : Matrix n n ℝ → ℝ

def SpectralTraceMaximization.feasibleSet (P : SpectralTraceMaximization) :
    Set (Matrix P.n P.n ℝ) :=
  letI := P.fintype_n
  letI := P.decEq_n
  {X | X.IsSymm ∧ Matrix.trace X = P.r ∧ X.PosSemidef ∧ (1 - X).PosSemidef}

def SpectralTraceMaximization.objective (P : SpectralTraceMaximization) :
    Matrix P.n P.n ℝ → ℝ :=
  letI := P.fintype_n
  letI := P.decEq_n
  fun X => Matrix.trace (P.A * X)

/-- A decreasing real sequence attains its maximum weighted sum over the hypersimplex
`{w ∈ [0,1]^n | ∑ w = r}` at the characteristic vector of the first `r` indices. -/
lemma weighted_sum_le_top_r_sum_nat
    {n r : ℕ} (hr_lower : 1 ≤ r) (hr_upper : r ≤ n)
    (lam w : Nat → ℝ)
    (hw_nonneg : ∀ i < n, 0 ≤ w i)
    (hw_le_one : ∀ i < n, w i ≤ 1)
    (hw_sum : Finset.sum (Finset.range n) w = (r : ℝ))
    (hmono : ∀ {i j : Nat}, i < n → j < n → i ≤ j → lam i ≥ lam j) :
    Finset.sum (Finset.range n) (fun i => lam i * w i) ≤ Finset.sum (Finset.range r) lam := by
  have hr_pos : 0 < r := by omega
  have hpivot_lt_n : r - 1 < n := by omega
  -- Compare the deficit in the first `r` entries with the tail mass past `r`.
  have hmass :
      Finset.sum (Finset.range r) (fun i => 1 - w i) = Finset.sum (Finset.Ico r n) w := by
    have hsplit :
        Finset.sum (Finset.range r) w + Finset.sum (Finset.Ico r n) w = Finset.sum (Finset.range n) w := by
      rw [Finset.sum_range_add_sum_Ico _ hr_upper]
    calc
      Finset.sum (Finset.range r) (fun i => 1 - w i)
          = Finset.sum (Finset.range r) (fun _ => (1 : ℝ)) - Finset.sum (Finset.range r) w := by
              rw [Finset.sum_sub_distrib]
      _ = (r : ℝ) - Finset.sum (Finset.range r) w := by simp
      _ = Finset.sum (Finset.Ico r n) w := by
            linarith [hw_sum, hsplit]
  have hweighted_split :
      Finset.sum (Finset.range n) (fun i => lam i * w i) =
        Finset.sum (Finset.range r) (fun i => lam i * w i) +
          Finset.sum (Finset.Ico r n) (fun i => lam i * w i) := by
    symm
    exact Finset.sum_range_add_sum_Ico (fun i => lam i * w i) hr_upper
  have hdecomp :
      Finset.sum (Finset.range r) lam - Finset.sum (Finset.range n) (fun i => lam i * w i) =
        Finset.sum (Finset.range r) (fun i => lam i * (1 - w i)) -
          Finset.sum (Finset.Ico r n) (fun i => lam i * w i) := by
    rw [hweighted_split]
    calc
      Finset.sum (Finset.range r) lam -
          (Finset.sum (Finset.range r) (fun i => lam i * w i) +
            Finset.sum (Finset.Ico r n) (fun i => lam i * w i))
          = (Finset.sum (Finset.range r) lam -
              Finset.sum (Finset.range r) (fun i => lam i * w i)) -
              Finset.sum (Finset.Ico r n) (fun i => lam i * w i) := by ring
      _ = Finset.sum (Finset.range r) (fun i => lam i * (1 - w i)) -
            Finset.sum (Finset.Ico r n) (fun i => lam i * w i) := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  -- The prefix terms are all at least the pivot value `lam (r - 1)`.
  have hfront :
      lam (r - 1) * Finset.sum (Finset.range r) (fun i => 1 - w i) ≤
        Finset.sum (Finset.range r) (fun i => lam i * (1 - w i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_lt_r : i < r := Finset.mem_range.mp hi
    have hi_lt_n : i < n := lt_of_lt_of_le hi_lt_r hr_upper
    have hi_le_pivot : i ≤ r - 1 := by omega
    have hlam : lam (r - 1) ≤ lam i := by
      exact hmono hi_lt_n hpivot_lt_n hi_le_pivot
    have hfactor : 0 ≤ 1 - w i := sub_nonneg.mpr (hw_le_one i hi_lt_n)
    exact mul_le_mul_of_nonneg_right hlam hfactor
  -- The tail terms are all at most the same pivot value.
  have htail :
      Finset.sum (Finset.Ico r n) (fun i => lam i * w i) ≤
        lam (r - 1) * Finset.sum (Finset.Ico r n) w := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_mem : i ∈ Finset.Ico r n := hi
    have hi_lt_n : i < n := (Finset.mem_Ico.mp hi_mem).2
    have hr_le_i : r ≤ i := (Finset.mem_Ico.mp hi_mem).1
    have hpivot_le_i : r - 1 ≤ i := by omega
    have hlam : lam i ≤ lam (r - 1) := by
      exact hmono hpivot_lt_n hi_lt_n hpivot_le_i
    exact mul_le_mul_of_nonneg_right hlam (hw_nonneg i hi_lt_n)
  -- The front deficit and the tail mass coincide, so the pivot comparisons cancel exactly.
  have hdiff_nonneg :
      0 ≤ Finset.sum (Finset.range r) (fun i => lam i * (1 - w i)) -
        Finset.sum (Finset.Ico r n) (fun i => lam i * w i) := by
    have hpivot_cancel :
        lam (r - 1) * Finset.sum (Finset.range r) (fun i => 1 - w i) -
            lam (r - 1) * Finset.sum (Finset.Ico r n) w = 0 := by
      rw [hmass]
      ring
    linarith
  have htop_minus_nonneg :
      0 ≤ Finset.sum (Finset.range r) lam - Finset.sum (Finset.range n) (fun i => lam i * w i) := by
    rwa [hdecomp]
  linarith

/- [BLOCK Exercise 4.17-(a) | 35 | thm]
Let \(S^n\) be the set of real \(n \times n\) symmetric matrices. Let \(A \in S^n\), and let \(\lambda_1(A),\ldots,\lambda_n(A)\) be the eigenvalues of \(A\) ordered so that \(\lambda_1(A) \ge \lambda_2(A) \ge \cdots \ge \lambda_n(A)\). Fix \(r \in \{1,\ldots,n\}\), and define \(f(A)=\sum_{k=1}^r \lambda_k(A)\). Then spectral trace maximization.
-/
theorem spectral_trace_maximization
    (n r : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm)
    (hr_lower : 1 ≤ r)
    (hr_upper : r ≤ n)
    (hordered :
      ∀ i j : Fin n,
        i.1 ≤ j.1 →
          (by simpa using hA : A.IsHermitian).eigenvalues i ≥
            (by simpa using hA : A.IsHermitian).eigenvalues j) :
    sSup {t : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.IsSymm ∧
      Matrix.trace X = (r : ℝ) ∧
      X.PosSemidef ∧
      (1 - X).PosSemidef ∧
      t = Matrix.trace (A * X)} =
      ∑ k : Fin r,
        (by simpa using hA : A.IsHermitian).eigenvalues
          ⟨k.1, Nat.lt_of_lt_of_le k.2 hr_upper⟩ := by
  classical
  have hAh : A.IsHermitian := by simpa using hA
  let U := hAh.eigenvectorUnitary
  let Uc : Matrix (Fin n) (Fin n) ℝ := (U : Matrix _ _ _)
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => if i.1 < r then 1 else 0)
  let X0 : Matrix (Fin n) (Fin n) ℝ := Uc * D * star Uc
  let topSum : ℝ :=
    ∑ k : Fin r, hAh.eigenvalues ⟨k.1, Nat.lt_of_lt_of_le k.2 hr_upper⟩
  -- Route correction: fix the unitary diagonalization and the canonical spectral projector first,
  -- so the remaining work is only the scalar weight inequality plus the `sSup` packaging.
  have hdiagA : star Uc * A * Uc = Matrix.diagonal hAh.eigenvalues := by
    simpa [U, Uc] using hAh.conjStarAlgAut_star_eigenvectorUnitary
  have hUstar : Uc * star Uc = 1 := by
    simp [U, Uc]
  have hstarU : star Uc * Uc = 1 := by
    simp [U, Uc]
  -- The diagonal projector is a positive contraction.
  have hD_psd : D.PosSemidef := by
    rw [show D = Matrix.diagonal (fun i : Fin n => if i.1 < r then 1 else 0) by rfl]
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    split_ifs <;> positivity
  have hD_comp : 1 - D = Matrix.diagonal (fun i : Fin n => if i.1 < r then (0 : ℝ) else 1) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h : i.1 < r <;> simp [D, Matrix.diagonal, h]
    · simp [D, Matrix.diagonal, hij]
  have hD_le_one_psd : (1 - D).PosSemidef := by
    rw [hD_comp, Matrix.posSemidef_diagonal_iff]
    intro i
    split_ifs <;> positivity
  have hcard_diag_indices : (Finset.univ.filter fun i : Fin n => i.1 < r).card = r := by
    let e : {i : Fin n // i.1 < r} ≃ Fin r :=
      { toFun := fun i => (⟨(i.1 : ℕ), i.2⟩ : Fin r)
        invFun := fun i =>
          (⟨(⟨(i : ℕ), lt_of_lt_of_le i.2 hr_upper⟩ : Fin n), i.2⟩ :
            {i : Fin n // i.1 < r})
        left_inv := by
          intro i
          rcases i with ⟨⟨i, hi_lt_n⟩, hi_lt_r⟩
          rfl
        right_inv := by
          intro i
          rcases i with ⟨i, hi_lt_r⟩
          rfl }
    calc
      (Finset.univ.filter fun i : Fin n => i.1 < r).card = Fintype.card {i : Fin n // i.1 < r} := by
        symm
        exact Fintype.card_ofFinset (p := {i : Fin n | i.1 < r}) _ (by
          intro i
          simp [Set.mem_setOf_eq])
      _ = Fintype.card (Fin r) := Fintype.card_congr e
      _ = r := Fintype.card_fin r
  -- The trace of the canonical witness already has the correct rank parameter.
  have htraceX0 : Matrix.trace X0 = (r : ℝ) := by
    calc
      Matrix.trace X0 = Matrix.trace ((Uc * D) * star Uc) := by simp [X0, Matrix.mul_assoc]
      _ = Matrix.trace (star Uc * (Uc * D)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((star Uc * Uc) * D) := by simp [Matrix.mul_assoc]
      _ = Matrix.trace D := by rw [hstarU, one_mul]
      _ = (r : ℝ) := by
            simp [D, Matrix.trace_diagonal]
            exact_mod_cast hcard_diag_indices
  let lamNat : Nat → ℝ := fun i => if h : i < n then hAh.eigenvalues ⟨i, h⟩ else 0
  have hlamNat :
      ∀ {i j : Nat}, i < n → j < n → i ≤ j → lamNat i ≥ lamNat j := by
    intro i j hi hj hij
    simp [lamNat, hi, hj]
    exact hordered ⟨i, hi⟩ ⟨j, hj⟩ hij
  have htopSum_range : topSum = Finset.sum (Finset.range r) lamNat := by
    calc
      topSum = ∑ i : Fin r, lamNat i := by
        change (∑ k : Fin r, hAh.eigenvalues ⟨k.1, Nat.lt_of_lt_of_le k.2 hr_upper⟩) =
          ∑ i : Fin r, lamNat i
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi' : (i : Nat) < n := lt_of_lt_of_le i.2 hr_upper
        simp [lamNat, hi']
      _ = Finset.sum (Finset.range r) lamNat := Fin.sum_univ_eq_sum_range lamNat r
  have hUunit : IsUnit Uc := by
    simpa [U, Uc] using (Unitary.isUnit_coe (U := U))
  have hX0_psd : X0.PosSemidef := by
    -- The canonical witness is the unitary conjugate of the diagonal rank-`r` projector.
    simpa [X0] using (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hUunit).2 hD_psd
  have hX0_sub_eq : Uc * (1 - D) * star Uc = 1 - X0 := by
    -- Conjugation commutes with taking the orthogonal complement projector.
    calc
      Uc * (1 - D) * star Uc = (Uc * (1 - D)) * star Uc := by simp [Matrix.mul_assoc]
      _ = (Uc - Uc * D) * star Uc := by simp [Matrix.mul_sub]
      _ = Uc * star Uc - (Uc * D) * star Uc := by simp [Matrix.sub_mul, Matrix.mul_assoc]
      _ = 1 - X0 := by simp [X0, hUstar]
  have hX0_le_one_psd : (1 - X0).PosSemidef := by
    -- The complement projector stays positive semidefinite after the same unitary conjugation.
    rw [← hX0_sub_eq]
    simpa using (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hUunit).2 hD_le_one_psd
  have hX0_symm : X0.IsSymm := by
    -- Over `ℝ`, Hermitian and symmetric coincide.
    simpa using hX0_psd.1
  have htraceAX0 : Matrix.trace (A * X0) = topSum := by
    -- Move the trace into the eigenbasis of `A`, where the witness becomes diagonal.
    calc
      Matrix.trace (A * X0) = Matrix.trace ((A * Uc * D) * star Uc) := by
        simp [X0, Matrix.mul_assoc]
      _ = Matrix.trace (star Uc * (A * Uc * D)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((star Uc * A * Uc) * D) := by
        have hmul : star Uc * (A * Uc * D) = (star Uc * A * Uc) * D := by
          simp [Matrix.mul_assoc]
        rw [hmul]
      _ = Matrix.trace (Matrix.diagonal hAh.eigenvalues * D) := by rw [hdiagA]
      _ = ∑ i : Fin n, if i.1 < r then hAh.eigenvalues i else 0 := by
        rw [Matrix.trace]
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hir : i.1 < r
        · simp [Matrix.diag, D, hir]
        · simp [Matrix.diag, D, hir]
      _ = topSum := by
        rw [htopSum_range]
        calc
          (∑ i : Fin n, (if i.1 < r then hAh.eigenvalues i else (0 : ℝ)))
              = ∑ i : Fin n, (if i.1 < r then lamNat i else (0 : ℝ)) := by
                  simp [lamNat]
          _ = Finset.sum (Finset.range n) (fun i => if i < r then lamNat i else (0 : ℝ)) := by
                exact Fin.sum_univ_eq_sum_range (fun i => if i < r then lamNat i else (0 : ℝ)) n
          _ = Finset.sum (Finset.range r) (fun i => if i < r then lamNat i else (0 : ℝ)) +
                Finset.sum (Finset.Ico r n) (fun i => if i < r then lamNat i else (0 : ℝ)) := by
                  symm
                  exact Finset.sum_range_add_sum_Ico (fun i => if i < r then lamNat i else (0 : ℝ)) hr_upper
          _ = Finset.sum (Finset.range r) lamNat +
                Finset.sum (Finset.Ico r n) (fun i => if i < r then lamNat i else (0 : ℝ)) := by
                  congr 1
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  simp [Finset.mem_range.mp hi]
          _ = Finset.sum (Finset.range r) lamNat := by
                have htail_zero :
                    Finset.sum (Finset.Ico r n) (fun i => if i < r then lamNat i else (0 : ℝ)) = 0 := by
                  refine Finset.sum_eq_zero ?_
                  intro i hi
                  simp [Nat.not_lt_of_ge (Finset.mem_Ico.mp hi).1]
                simp [htail_zero]
  let S : Set ℝ := {t : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.IsSymm ∧
      Matrix.trace X = (r : ℝ) ∧
      X.PosSemidef ∧
      (1 - X).PosSemidef ∧
      t = Matrix.trace (A * X)}
  change sSup S = topSum
  have hS_le_top : ∀ t ∈ S, t ≤ topSum := by
    intro t ht
    rcases ht with ⟨X, hXsymm, htraceX, hX_psd, hOneSubX_psd, rfl⟩
    let Y : Matrix (Fin n) (Fin n) ℝ := star Uc * X * Uc
    let wNat : Nat → ℝ := fun i => if h : i < n then Y ⟨i, h⟩ ⟨i, h⟩ else 0
    have hY_psd : Y.PosSemidef := by
      -- Feasibility is preserved under unitary conjugation.
      simpa [Y] using (Matrix.IsUnit.posSemidef_star_left_conjugate_iff hUunit).2 hX_psd
    have hOneSubY_eq : star Uc * (1 - X) * Uc = 1 - Y := by
      -- Conjugation also transports the contraction constraint `X ≤ I`.
      calc
        star Uc * (1 - X) * Uc = (star Uc * (1 - X)) * Uc := by simp [Matrix.mul_assoc]
        _ = (star Uc - star Uc * X) * Uc := by simp [Matrix.mul_sub]
        _ = star Uc * Uc - (star Uc * X) * Uc := by simp [Matrix.sub_mul, Matrix.mul_assoc]
        _ = 1 - Y := by simp [Y, hstarU]
    have hOneSubY_psd : (1 - Y).PosSemidef := by
      rw [← hOneSubY_eq]
      simpa using (Matrix.IsUnit.posSemidef_star_left_conjugate_iff hUunit).2 hOneSubX_psd
    have htraceY : Matrix.trace Y = (r : ℝ) := by
      -- Trace is invariant under cyclic permutation.
      calc
        Matrix.trace Y = Matrix.trace ((star Uc * X) * Uc) := by simp [Y, Matrix.mul_assoc]
        _ = Matrix.trace (Uc * (star Uc * X)) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace ((Uc * star Uc) * X) := by simp [Matrix.mul_assoc]
        _ = Matrix.trace X := by rw [hUstar, one_mul]
        _ = (r : ℝ) := htraceX
    have hobjective_diag :
        Matrix.trace (A * X) = ∑ i : Fin n, hAh.eigenvalues i * Y i i := by
      -- After diagonalizing `A`, only the diagonal of `Y` contributes to the trace.
      calc
        Matrix.trace (A * X) = Matrix.trace ((A * X * Uc) * star Uc) := by
          rw [Matrix.mul_assoc, hUstar, Matrix.mul_one]
        _ = Matrix.trace (star Uc * (A * X * Uc)) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace ((star Uc * A * Uc) * (star Uc * X * Uc)) := by
          have hmul :
              (star Uc * A * Uc) * (star Uc * X * Uc) = star Uc * (A * X * Uc) := by
            calc
              (star Uc * A * Uc) * (star Uc * X * Uc)
                  = star Uc * A * (Uc * star Uc) * X * Uc := by simp [Matrix.mul_assoc]
              _ = star Uc * A * X * Uc := by rw [hUstar]; simp [Matrix.mul_assoc]
              _ = star Uc * (A * X * Uc) := by simp [Matrix.mul_assoc]
          rw [← hmul]
        _ = Matrix.trace (Matrix.diagonal hAh.eigenvalues * Y) := by rw [hdiagA]
        _ = ∑ i : Fin n, hAh.eigenvalues i * Y i i := by
          rw [Matrix.trace]
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [Matrix.diagonal_mul]
    have hw_nonneg :
        ∀ i < n, 0 ≤ wNat i := by
      intro i hi
      simpa [wNat, hi] using (Matrix.PosSemidef.diag_nonneg hY_psd : 0 ≤ Y ⟨i, hi⟩ ⟨i, hi⟩)
    have hw_le_one :
        ∀ i < n, wNat i ≤ 1 := by
      intro i hi
      have hdiag := (Matrix.PosSemidef.diag_nonneg hOneSubY_psd : 0 ≤ (1 - Y) ⟨i, hi⟩ ⟨i, hi⟩)
      simpa [wNat, hi] using hdiag
    have hw_sum :
        Finset.sum (Finset.range n) wNat = (r : ℝ) := by
      have htraceY_diag : ∑ i : Fin n, Y i i = (r : ℝ) := by
        simpa [Matrix.trace, Matrix.diag] using htraceY
      calc
        Finset.sum (Finset.range n) wNat = ∑ i : Fin n, wNat i := by
          symm
          exact Fin.sum_univ_eq_sum_range wNat n
        _ = ∑ i : Fin n, Y i i := by
          simp [wNat]
        _ = (r : ℝ) := htraceY_diag
    have hobjective_nat :
        Matrix.trace (A * X) = Finset.sum (Finset.range n) (fun i => lamNat i * wNat i) := by
      calc
        Matrix.trace (A * X) = ∑ i : Fin n, hAh.eigenvalues i * Y i i := hobjective_diag
        _ = ∑ i : Fin n, lamNat i * wNat i := by
          simp [lamNat, wNat]
        _ = Finset.sum (Finset.range n) (fun i => lamNat i * wNat i) := by
          exact Fin.sum_univ_eq_sum_range (fun i => lamNat i * wNat i) n
    have hscalar :
        Finset.sum (Finset.range n) (fun i => lamNat i * wNat i) ≤ Finset.sum (Finset.range r) lamNat :=
      weighted_sum_le_top_r_sum_nat hr_lower hr_upper lamNat wNat hw_nonneg hw_le_one hw_sum hlamNat
    rw [hobjective_nat, htopSum_range]
    exact hscalar
  have hS_bddAbove : BddAbove S := ⟨topSum, hS_le_top⟩
  have htop_mem : topSum ∈ S := by
    exact ⟨X0, hX0_symm, htraceX0, hX0_psd, hX0_le_one_psd, htraceAX0.symm⟩
  have hS_nonempty : S.Nonempty := by
    exact ⟨topSum, htop_mem⟩
  apply le_antisymm
  · exact csSup_le hS_nonempty hS_le_top
  · exact le_csSup hS_bddAbove htop_mem

end «problem-182»
