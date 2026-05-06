import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-39»
/- [BLOCK Exercise 3.33-(b) | 34 | thm]
Let S^n be the vector space of real symmetric n × n matrices, and write X succeq 0 when X is
positive semidefinite. Consider the feasible set F={X∈ S^n : tr(A_iX)=bᵢ for i=1,ldots,m, Xsucceq
0}, where A₁,ldots,Aₘ∈ S^n and b₁,ldots,bₘ∈ ℝ. A matrix hat X∈ F is an extreme point of F if the
only matrix V∈ S^n such that tr(A_iV)=0 quad for i=1,ldots,m, hat X+Vsucceq 0, hat X-Vsucceq 0 is
V=0. Let hat X∈ F and let r=rank(hat X). Show that if (r(r+1))/(2)>m, then hat X is not an extreme
point of F.
-/
open Matrix

theorem not_extremePoint_of_rank_condition
    {n m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (Xhat : Matrix (Fin n) (Fin n) ℝ)
    (hA_symm : ∀ i : Fin m, (A i).IsSymm)
    (hXhat_symm : Xhat.IsSymm)
    (hXhat_psd : Xhat.PosSemidef)
    (hfeas : ∀ i : Fin m, Matrix.trace (A i * Xhat) = b i)
    (hineq : Matrix.rank Xhat * (Matrix.rank Xhat + 1) / 2 > m) :
    ∃ V : Matrix (Fin n) (Fin n) ℝ,
      V.IsSymm ∧
      (∀ i : Fin m, Matrix.trace (A i * V) = 0) ∧
      (Xhat + V).PosSemidef ∧
      (Xhat - V).PosSemidef ∧
      V ≠ 0 := by
  classical
  -- Keep the original symmetry and feasibility data available without changing the theorem header.
  let _ := hA_symm
  let _ := hXhat_symm
  let _ := hfeas
  -- Route correction: instead of introducing more standalone scaffolding, compress `Xhat`
  -- directly to its positive spectral support, solve the trace equations on a `Sym2`-indexed
  -- coefficient space, and then lift the scaled perturbation back to the ambient matrix.
  let hH : Xhat.IsHermitian := hXhat_psd.isHermitian
  let s : Type := {i : Fin n // hH.eigenvalues i ≠ 0}
  letI : Fintype s := inferInstance
  let U : Matrix (Fin n) (Fin n) ℝ := hH.eigenvectorUnitary
  let P : Matrix (Fin n) s ℝ := fun i j => U i j.1 * Real.sqrt (hH.eigenvalues j)
  let D : Matrix s s ℝ := diagonal (fun j : s => hH.eigenvalues j)
  let YOf : (Sym2 s → ℝ) →ₗ[ℝ] Matrix s s ℝ :=
    { toFun := fun c i j => c s(i, j)
      map_add' := by
        intro c d
        ext i j
        simp
      map_smul' := by
        intro t c
        ext i j
        simp }
  let L : (Sym2 s → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun c i => Matrix.trace ((Pᵀ * A i * P) * YOf c)
      map_add' := by
        intro c d
        ext i
        change Matrix.trace ((Pᵀ * A i * P) * YOf (c + d)) =
          Matrix.trace ((Pᵀ * A i * P) * YOf c) + Matrix.trace ((Pᵀ * A i * P) * YOf d)
        rw [show YOf (c + d) = YOf c + YOf d by
              ext a b
              simp [YOf]]
        rw [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        intro t c
        ext i
        change Matrix.trace ((Pᵀ * A i * P) * YOf (t • c)) =
          t * Matrix.trace ((Pᵀ * A i * P) * YOf c)
        rw [show YOf (t • c) = t • YOf c by
              ext a b
              simp [YOf]]
        simp [Matrix.trace_smul] }
  -- The support size is exactly the rank of `Xhat`.
  have hs_card : Fintype.card s = Matrix.rank Xhat := by
    simpa [s, hH] using hH.rank_eq_card_non_zero_eigs.symm
  have hrank_pos : 0 < Matrix.rank Xhat := by
    by_contra hzero
    have hr : Matrix.rank Xhat = 0 := Nat.eq_zero_of_not_pos hzero
    simp [hr] at hineq
  have hs_nonempty : Nonempty s := by
    rw [← Fintype.card_pos_iff, hs_card]
    exact hrank_pos
  -- The restricted factor `P` has orthogonal columns with positive squared norms.
  have hPtP : Pᵀ * P = D := by
    ext j k
    have horth : (∑ i, U i j.1 * U i k.1) = if j.1 = k.1 then 1 else 0 := by
      simpa [U, Matrix.mul_apply] using
        congrFun (congrFun (Unitary.coe_star_mul_self hH.eigenvectorUnitary) j.1) k.1
    by_cases h : j = k
    · subst h
      change ∑ x,
          (U x j.1 * Real.sqrt (hH.eigenvalues j)) *
            (U x j.1 * Real.sqrt (hH.eigenvalues j)) =
          D j j
      calc
        _ = ∑ x,
            (U x j.1 * U x j.1) *
              (Real.sqrt (hH.eigenvalues j) * Real.sqrt (hH.eigenvalues j)) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
        _ = (∑ x, U x j.1 * U x j.1) *
            (Real.sqrt (hH.eigenvalues j) * Real.sqrt (hH.eigenvalues j)) := by
              rw [Finset.sum_mul]
        _ = hH.eigenvalues j := by
              rw [horth, if_pos rfl, one_mul, Real.mul_self_sqrt (hXhat_psd.eigenvalues_nonneg j.1)]
        _ = D j j := by
              simp [D]
    · have hjk : j.1 ≠ k.1 := fun h' => h (Subtype.ext h')
      change ∑ x,
          (U x j.1 * Real.sqrt (hH.eigenvalues j)) *
            (U x k.1 * Real.sqrt (hH.eigenvalues k)) =
          D j k
      calc
        _ = ∑ x,
            (U x j.1 * U x k.1) *
              (Real.sqrt (hH.eigenvalues j) * Real.sqrt (hH.eigenvalues k)) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
        _ = (∑ x, U x j.1 * U x k.1) *
            (Real.sqrt (hH.eigenvalues j) * Real.sqrt (hH.eigenvalues k)) := by
              rw [Finset.sum_mul]
        _ = 0 := by
              rw [horth, if_neg hjk, zero_mul]
        _ = D j k := by
              simp [D, h]
  -- Replacing the zero-eigenvalue columns by nothing keeps the factorization of `Xhat`.
  have hXhat_eq : Xhat = P * Pᵀ := by
    ext i k
    have hentry : Xhat i k = ∑ l, (U i l * hH.eigenvalues l) * U k l := by
      calc
        Xhat i k = (U * diagonal hH.eigenvalues * star U) i k := by
          simpa [U, Unitary.conjStarAlgAut_apply] using congrFun (congrFun hH.spectral_theorem i) k
        _ = ∑ l, (U i l * hH.eigenvalues l) * U k l := by
          simp [Matrix.mul_apply, Matrix.diagonal]
    have hfilter := Finset.sum_subtype
      (s := Finset.univ.filter (fun l : Fin n => hH.eigenvalues l ≠ 0))
      (F := inferInstance)
      (p := fun l : Fin n => hH.eigenvalues l ≠ 0)
      (h := by intro x; simp)
      (f := fun l : Fin n => (U i l * hH.eigenvalues l) * U k l)
    calc
      Xhat i k = ∑ l, (U i l * hH.eigenvalues l) * U k l := hentry
      _ = Finset.sum (Finset.univ.filter (fun l : Fin n => hH.eigenvalues l ≠ 0))
            (fun l => (U i l * hH.eigenvalues l) * U k l) := by
              symm
              calc
                Finset.sum (Finset.univ.filter (fun l : Fin n => hH.eigenvalues l ≠ 0))
                    (fun l => (U i l * hH.eigenvalues l) * U k l)
                    = Finset.sum Finset.univ (fun l => (U i l * hH.eigenvalues l) * U k l) := by
                        apply Finset.sum_subset
                        · intro x hx
                          simp
                        · intro x hx hxnot
                          simp at hxnot
                          simp [hxnot]
                _ = ∑ l, (U i l * hH.eigenvalues l) * U k l := by
                      simp
      _ = Finset.univ.sum (fun j : s => (U i j.1 * hH.eigenvalues j.1) * U k j.1) := by
            simpa [s] using hfilter
      _ = Finset.univ.sum
            (fun j : s =>
              (U i j.1 * Real.sqrt (hH.eigenvalues j)) *
                (U k j.1 * Real.sqrt (hH.eigenvalues j))) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [show (U i j.1 * hH.eigenvalues j.1) * U k j.1 =
                    (U i j.1 * U k j.1) * hH.eigenvalues j.1 by ring]
              rw [show (U i j.1 * Real.sqrt (hH.eigenvalues j)) *
                    (U k j.1 * Real.sqrt (hH.eigenvalues j)) =
                    (U i j.1 * U k j.1) *
                      (Real.sqrt (hH.eigenvalues j) * Real.sqrt (hH.eigenvalues j)) by ring]
              rw [Real.mul_self_sqrt (hXhat_psd.eigenvalues_nonneg j.1)]
      _ = (P * Pᵀ) i k := by
            simp [P, Matrix.mul_apply]
  have hD_pos : ∀ j : s, 0 < hH.eigenvalues j := by
    intro j
    exact lt_of_le_of_ne (hXhat_psd.eigenvalues_nonneg j.1) (by simpa using j.property.symm)
  -- The coefficient model produces symmetric matrices and detects nonzero coefficients.
  have hYOf_symm : ∀ c, (YOf c).IsSymm := by
    intro c
    ext i j
    simp [YOf, Sym2.eq_swap]
  have hYOf_injective : Function.Injective YOf := by
    intro c d hcd
    funext p
    rcases Quot.exists_rep p with ⟨a, ha⟩
    rcases a with ⟨i, j⟩
    have := congrArg (fun M : Matrix s s ℝ => M i j) hcd
    simpa [YOf, ha] using this
  -- The compressed symmetric coefficient space has dimension `rank(Xhat) * (rank(Xhat) + 1) / 2`.
  have hdim_source : Module.finrank ℝ (Sym2 s → ℝ) =
      Matrix.rank Xhat * (Matrix.rank Xhat + 1) / 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Nat.choose_two_right, hs_card]
    simp
    ring_nf
  have hdim_target : Module.finrank ℝ (Fin m → ℝ) = m := by
    simp
  have hker_ne_bot : LinearMap.ker L ≠ ⊥ := by
    apply L.ker_ne_bot_of_finrank_lt
    rw [hdim_target, hdim_source]
    simpa using hineq
  -- Choose a nonzero compressed symmetric perturbation annihilating all trace constraints.
  obtain ⟨c, hc_memker, hc_ne⟩ := L.ker.ne_bot_iff.mp hker_ne_bot
  let Z₀ : Matrix s s ℝ := YOf c
  have hZ₀_symm : Z₀.IsSymm := hYOf_symm c
  have hZ₀_ne : Z₀ ≠ 0 := by
    intro hzero
    apply hc_ne
    apply hYOf_injective
    simpa [Z₀] using hzero
  have htraceZ₀ : ∀ i : Fin m, Matrix.trace ((Pᵀ * A i * P) * Z₀) = 0 := by
    intro i
    simpa [L, Z₀] using congrFun hc_memker i
  -- Scale the perturbation so that the compressed identity dominates it in both signs.
  let hZ₀H : Z₀.IsHermitian := by
    simpa [Matrix.IsSymm, Matrix.IsHermitian] using hZ₀_symm
  let t : ℝ := (Finset.univ.sum fun j : s => (|hZ₀H.eigenvalues j| + 1 : ℝ))⁻¹
  have hsum_pos : 0 < Finset.univ.sum fun j : s => (|hZ₀H.eigenvalues j| + 1 : ℝ) := by
    rcases hs_nonempty with ⟨j0⟩
    have hle :
        |hZ₀H.eigenvalues j0| + 1 ≤
          Finset.sum Finset.univ (fun j : s => (|hZ₀H.eigenvalues j| + 1 : ℝ)) := by
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun j : s => (|hZ₀H.eigenvalues j| + 1 : ℝ))
        (fun j _ => by positivity) (Finset.mem_univ j0)
    have hpos : 0 < |hZ₀H.eigenvalues j0| + 1 := by
      positivity
    exact lt_of_lt_of_le hpos (by simpa using hle)
  have ht_pos : 0 < t := by
    dsimp [t]
    exact inv_pos.mpr hsum_pos
  have ht_ne : t ≠ 0 := ht_pos.ne'
  let Z : Matrix s s ℝ := t • Z₀
  have hZ_symm : Z.IsSymm := by
    simpa [Z] using hZ₀_symm.smul t
  have hZ_ne : Z ≠ 0 := by
    simpa [Z] using smul_ne_zero ht_ne hZ₀_ne
  have htraceZ : ∀ i : Fin m, Matrix.trace ((Pᵀ * A i * P) * Z) = 0 := by
    intro i
    simp [Z, htraceZ₀ i]
  have hbound : ∀ j : s, |t * hZ₀H.eigenvalues j| < 1 := by
    intro j
    have hlt_sum : |hZ₀H.eigenvalues j| <
        Finset.univ.sum (fun k : s => (|hZ₀H.eigenvalues k| + 1 : ℝ)) := by
      have hle :
          |hZ₀H.eigenvalues j| + 1 ≤
            Finset.sum Finset.univ (fun k : s => (|hZ₀H.eigenvalues k| + 1 : ℝ)) := by
        exact Finset.single_le_sum
          (s := Finset.univ) (f := fun k : s => (|hZ₀H.eigenvalues k| + 1 : ℝ))
          (fun k _ => by positivity) (Finset.mem_univ j)
      have hle' :
          |hZ₀H.eigenvalues j| + 1 ≤
            Finset.univ.sum (fun k : s => (|hZ₀H.eigenvalues k| + 1 : ℝ)) := by
        simpa using hle
      linarith
    rw [show t = (Finset.univ.sum fun j : s => (|hZ₀H.eigenvalues j| + 1 : ℝ))⁻¹ by rfl,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr hsum_pos.le), mul_comm]
    have hinv_pos :
        0 < (Finset.univ.sum fun k : s => (|hZ₀H.eigenvalues k| + 1 : ℝ))⁻¹ := inv_pos.mpr hsum_pos
    calc
      |hZ₀H.eigenvalues j| *
          (Finset.univ.sum fun k : s => (|hZ₀H.eigenvalues k| + 1 : ℝ))⁻¹
          < (Finset.univ.sum fun k : s => (|hZ₀H.eigenvalues k| + 1 : ℝ)) *
              (Finset.univ.sum fun k : s => (|hZ₀H.eigenvalues k| + 1 : ℝ))⁻¹ := by
              exact mul_lt_mul_of_pos_right hlt_sum hinv_pos
      _ = 1 := by
            rw [mul_inv_cancel₀ hsum_pos.ne']
  have hplus_diag : ∀ j : s, 0 ≤ 1 + t * hZ₀H.eigenvalues j := by
    intro j
    have hj := hbound j
    have hpair := abs_lt.mp hj
    nlinarith
  have hminus_diag : ∀ j : s, 0 ≤ 1 - t * hZ₀H.eigenvalues j := by
    intro j
    have hj := hbound j
    have hpair := abs_lt.mp hj
    nlinarith
  have hplusZ_psd : ((1 : Matrix s s ℝ) + Z).PosSemidef := by
    let U₀ : Matrix s s ℝ := hZ₀H.eigenvectorUnitary
    have hdiag_eq :
        (1 : Matrix s s ℝ) + t • diagonal hZ₀H.eigenvalues =
          diagonal (fun j => 1 + t * hZ₀H.eigenvalues j) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
    have hrepr :
        (1 : Matrix s s ℝ) + Z =
          U₀ * diagonal (fun j => 1 + t * hZ₀H.eigenvalues j) * star U₀ := by
      have hspec : Z₀ = U₀ * diagonal hZ₀H.eigenvalues * star U₀ := by
        simpa [U₀, Unitary.conjStarAlgAut_apply] using hZ₀H.spectral_theorem
      have hunit : U₀ * star U₀ = 1 := by
        simp [U₀]
      calc
        (1 : Matrix s s ℝ) + Z = 1 + t • Z₀ := by
          simp [Z]
        _ = 1 + t • (U₀ * diagonal hZ₀H.eigenvalues * star U₀) := by
              simpa using congrArg (fun M : Matrix s s ℝ => (1 : Matrix s s ℝ) + t • M) hspec
        _ = U₀ * star U₀ + U₀ * (t • diagonal hZ₀H.eigenvalues) * star U₀ := by
              rw [hunit]
              simp [Matrix.mul_assoc]
        _ = U₀ * ((1 : Matrix s s ℝ) + t • diagonal hZ₀H.eigenvalues) * star U₀ := by
              simp [Matrix.mul_assoc, add_mul, mul_add]
        _ = U₀ * diagonal (fun j => 1 + t * hZ₀H.eigenvalues j) * star U₀ := by
              rw [hdiag_eq]
    rw [hrepr]
    have hdiag :
        (diagonal (fun j => 1 + t * hZ₀H.eigenvalues j)).PosSemidef := Matrix.PosSemidef.diagonal hplus_diag
    simpa [U₀] using hdiag.mul_mul_conjTranspose_same U₀
  have hminusZ_psd : ((1 : Matrix s s ℝ) - Z).PosSemidef := by
    let U₀ : Matrix s s ℝ := hZ₀H.eigenvectorUnitary
    have hdiag_eq :
        (1 : Matrix s s ℝ) - t • diagonal hZ₀H.eigenvalues =
          diagonal (fun j => 1 - t * hZ₀H.eigenvalues j) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij, sub_eq_add_neg]
    have hrepr :
        (1 : Matrix s s ℝ) - Z =
          U₀ * diagonal (fun j => 1 - t * hZ₀H.eigenvalues j) * star U₀ := by
      have hspec : Z₀ = U₀ * diagonal hZ₀H.eigenvalues * star U₀ := by
        simpa [U₀, Unitary.conjStarAlgAut_apply] using hZ₀H.spectral_theorem
      have hunit : U₀ * star U₀ = 1 := by
        simp [U₀]
      calc
        (1 : Matrix s s ℝ) - Z = 1 - t • Z₀ := by
          simp [Z]
        _ = 1 - t • (U₀ * diagonal hZ₀H.eigenvalues * star U₀) := by
              simpa using congrArg (fun M : Matrix s s ℝ => (1 : Matrix s s ℝ) - t • M) hspec
        _ = U₀ * star U₀ - U₀ * (t • diagonal hZ₀H.eigenvalues) * star U₀ := by
              rw [hunit]
              simp [Matrix.mul_assoc, sub_eq_add_neg]
        _ = U₀ * ((1 : Matrix s s ℝ) - t • diagonal hZ₀H.eigenvalues) * star U₀ := by
              simp [Matrix.mul_assoc, sub_eq_add_neg, add_mul, mul_add]
        _ = U₀ * diagonal (fun j => 1 - t * hZ₀H.eigenvalues j) * star U₀ := by
              rw [hdiag_eq]
    rw [hrepr]
    have hdiag :
        (diagonal (fun j => 1 - t * hZ₀H.eigenvalues j)).PosSemidef := Matrix.PosSemidef.diagonal hminus_diag
    simpa [U₀] using hdiag.mul_mul_conjTranspose_same U₀
  -- Lift the scaled compressed perturbation back to the original space.
  let V : Matrix (Fin n) (Fin n) ℝ := P * Z * Pᵀ
  have hV_symm : V.IsSymm := by
    have htrans : (P * Z * Pᵀ)ᵀ = P * Z * Pᵀ := by
      calc
        (P * Z * Pᵀ)ᵀ = P * Zᵀ * Pᵀ := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = P * Z * Pᵀ := by
          rw [hZ_symm.eq]
    simpa [V, Matrix.IsSymm] using htrans
  have htraceV : ∀ i : Fin m, Matrix.trace (A i * V) = 0 := by
    intro i
    calc
      Matrix.trace (A i * V) = Matrix.trace (A i * (P * Z * Pᵀ)) := by
        rfl
      _ = Matrix.trace ((A i * P) * Z * Pᵀ) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace (Pᵀ * (A i * P) * Z) := by
            rw [Matrix.trace_mul_cycle (A i * P) Z Pᵀ]
      _ = Matrix.trace (Pᵀ * A i * P * Z) := by
            simp [Matrix.mul_assoc]
      _ = 0 := htraceZ i
  have hplus_psd : (Xhat + V).PosSemidef := by
    have hrepr : Xhat + V = P * ((1 : Matrix s s ℝ) + Z) * Pᵀ := by
      calc
        Xhat + V = P * Pᵀ + V := by
          simp [hXhat_eq]
        _ = P * Pᵀ + P * Z * Pᵀ := by
              rfl
        _ = P * ((1 : Matrix s s ℝ) + Z) * Pᵀ := by
              simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    rw [hrepr]
    simpa using hplusZ_psd.mul_mul_conjTranspose_same P
  have hminus_psd : (Xhat - V).PosSemidef := by
    have hrepr : Xhat - V = P * ((1 : Matrix s s ℝ) - Z) * Pᵀ := by
      calc
        Xhat - V = P * Pᵀ - V := by
          simp [hXhat_eq]
        _ = P * Pᵀ - P * Z * Pᵀ := by
              rfl
        _ = P * ((1 : Matrix s s ℝ) - Z) * Pᵀ := by
              simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, sub_eq_add_neg]
    rw [hrepr]
    simpa using hminusZ_psd.mul_mul_conjTranspose_same P
  have hD_posDef : D.PosDef := by
    exact Matrix.PosDef.diagonal hD_pos
  have hD_det : IsUnit D.det := by
    exact D.isUnit_iff_isUnit_det.mp hD_posDef.isUnit
  have hV_ne : V ≠ 0 := by
    intro hzero
    have hDZ : D * Z * D = 0 := by
      have h' := congrArg (fun M => Pᵀ * M * P) hzero
      have h'' : Pᵀ * (P * Z * Pᵀ) * P = 0 := by
        simpa [V] using h'
      calc
        D * Z * D = (Pᵀ * P) * Z * D := by
          rw [hPtP]
        _ = Pᵀ * (P * Z) * D := by
              simp [Matrix.mul_assoc]
        _ = Pᵀ * (P * Z) * (Pᵀ * P) := by
              rw [hPtP]
        _ = Pᵀ * (P * Z * Pᵀ) * P := by
              simp [Matrix.mul_assoc]
        _ = 0 := h''
    have hDZ' : D * Z = 0 := by
      have h' := congrArg (fun M => M * D⁻¹) hDZ
      simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv D hD_det] using h'
    have h'' := congrArg (fun M => D⁻¹ * M) hDZ'
    have hZ_zero : Z = 0 := by
      have h''' : D⁻¹ * D * Z = 0 := by
        simpa [Matrix.mul_assoc] using h''
      simpa [Matrix.nonsing_inv_mul D hD_det] using h'''
    exact hZ_ne hZ_zero
  exact ⟨V, hV_symm, htraceV, hplus_psd, hminus_psd, hV_ne⟩

end «problem-39»
