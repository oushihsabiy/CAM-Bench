import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-169»
/-
For a matrix B ∈ ℝ^n × m, the induced ell_∞ - operator norm is ‖B‖_∞ = sup_z ≠ 0 (‖Bz‖_∞)/(‖z‖_∞) =
max_1 ≤ i ≤ n sum_j = 1^m |B_ij|.
-/
open Matrix

def inducedLInfOperatorNorm {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (B : Matrix n m ℝ) : ℝ :=
  sSup (Set.range fun i : n => ∑ j, |B i j|)

/-
A linear estimator hat x = By is minimax if its worst - case estimation error over the prescribed
uncertainty set is minimal; that is, if φ(B) ≤ φ(wideB̃) for every admissible linear estimator hat x
= wideB̃ y.
-/
structure MinimumInfinityNormLeftInverseProblemData
    (n m : Type*) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n] where
  A : Matrix m n ℝ

def MinimumInfinityNormLeftInverseProblemData.standard
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (A : Matrix m n ℝ) : MinimumInfinityNormLeftInverseProblemData n m where
  A := A

abbrev MinimumInfinityNormLeftInverseProblem
    (n m : Type*) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n] :=
  MinimumInfinityNormLeftInverseProblemData n m

def MinimumInfinityNormLeftInverseProblem.standard
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (A : Matrix m n ℝ) : MinimumInfinityNormLeftInverseProblem n m :=
  ⟨A⟩

def MinimumInfinityNormLeftInverseProblem.isFeasible
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (P : MinimumInfinityNormLeftInverseProblem n m) (B : Matrix n m ℝ) : Prop :=
  B * P.A = 1

def MinimumInfinityNormLeftInverseProblem.isOptimal
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (P : MinimumInfinityNormLeftInverseProblem n m) (B : Matrix n m ℝ) : Prop :=
  (B * P.A = 1) ∧
    ∀ B' : Matrix n m ℝ, B' * P.A = 1 → inducedLInfOperatorNorm B ≤ inducedLInfOperatorNorm B'

/-
Consider the linear measurement model y = Ax + v, where A ∈ ℝ^{m × n} has rank n with m ≥ n, x ∈
ℝ^n, y, v ∈ ℝ^m, and the noise satisfies ‖v‖_{∞} ≤ ε, ε ≥ 0, with ‖z‖_{∞} = max_{1 ≤ i ≤ k} |zᵢ| for
z = (z₁, ..., zₖ) ∈ ℝ^k. Restrict the estimator to the linear form x = By, where B ∈ ℝ^{n × m}, and
define the estimation error by e = x - x. For each B, define φ(B) = sup{‖By - x‖_{∞} | y = Ax + v, x
∈
ℝ^n, v ∈ ℝ^m, ‖v‖_{∞} ≤ ε}. Prove that φ(B) = cases ε ‖B‖_{∞}, & if BA = Iₙ,; + ∞, & if BA ≠ Iₙ,
cases where ‖B‖_{∞} = max_{1 ≤ i ≤ n} \sum_{j = 1}^m |B_{ij}| is the induced ell_∞ - operator norm.
-/
/-- Rewriting the measurement equation turns the estimation error into propagated noise. -/
lemma error_eq_mulVec_noise_of_left_inverse
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) (x : n → ℝ) (y v : m → ℝ)
    (hBA : B * A = 1) (hy : y = A *ᵥ x + v) :
    (fun i : n => (B *ᵥ y) i - x i) = B *ᵥ v := by
  -- Replace the measurement by `A *ᵥ x + v` so the left-inverse identity can cancel the signal part.
  subst hy
  ext i
  -- Evaluate the matrix-vector algebra coordinatewise and simplify the remaining subtraction.
  simp [Matrix.mulVec_add, Matrix.mulVec_mulVec, hBA, sub_eq_add_neg, add_assoc]

/-- Every coordinate is bounded by the supremum of the absolute-value range. -/
lemma abs_le_of_sSup_range_le
    {m : Type*} [Fintype m] [DecidableEq m] (v : m → ℝ) {ε : ℝ}
    (hv : sSup (Set.range fun i : m => |v i|) ≤ ε) (j : m) :
    |v j| ≤ ε := by
  -- Insert the chosen coordinate into the finite range and compare it with the supremum.
  exact (le_csSup (Finite.bddAbove_range _) ⟨j, rfl⟩).trans hv

/-- Each coordinate of `B *ᵥ v` is controlled by `ε` times the corresponding absolute row sum. -/
lemma abs_mulVec_le_epsilon_mul_rowSum
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (B : Matrix n m ℝ) (v : m → ℝ) {ε : ℝ}
    (hv : sSup (Set.range fun j : m => |v j|) ≤ ε) :
    ∀ i : n, |(B *ᵥ v) i| ≤ ε * ∑ j, |B i j| := by
  intro i
  -- Expand the matrix-vector product and take absolute values termwise.
  calc
    |(B *ᵥ v) i| = |∑ j, B i j * v j| := by simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, |B i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |B i j| * |v j| := by
      simp [abs_mul]
    _ ≤ ∑ j, |B i j| * ε := by
      refine Finset.sum_le_sum ?_
      intro j hj
      -- Bound each noise coordinate by the given `ℓ∞` constraint before multiplying by `|B i j|`.
      exact mul_le_mul_of_nonneg_left (abs_le_of_sSup_range_le v hv j) (abs_nonneg _)
    _ = ∑ j, ε * |B i j| := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [mul_comm]
    _ = ε * ∑ j, |B i j| := by
      rw [Finset.mul_sum]

/-- The `ℓ∞`-error of `B *ᵥ v` is bounded by `ε` times the induced `ℓ∞` operator norm. -/
lemma sSup_abs_mulVec_le_epsilon_mul_inducedLInfOperatorNorm
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (B : Matrix n m ℝ) (v : m → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hv : sSup (Set.range fun j : m => |v j|) ≤ ε) :
    sSup (Set.range fun i : n => |(B *ᵥ v) i|) ≤ ε * inducedLInfOperatorNorm B := by
  -- Show every coordinate is bounded by the row sum, then compare that row sum with the operator norm.
  refine csSup_le ?_ ?_
  · rcases ‹Nonempty n› with ⟨i⟩
    exact ⟨_, ⟨i, rfl⟩⟩
  · intro z hz
    rcases hz with ⟨i, rfl⟩
    have hrow : |(B *ᵥ v) i| ≤ ε * ∑ j, |B i j| :=
      abs_mulVec_le_epsilon_mul_rowSum B v hv i
    have hnorm : (∑ j, |B i j|) ≤ inducedLInfOperatorNorm B := by
      -- Each row sum is one element of the finite range defining the operator norm.
      exact le_csSup (Finite.bddAbove_range _) ⟨i, rfl⟩
    exact hrow.trans <| mul_le_mul_of_nonneg_left hnorm hε

theorem phi_eq_epsilon_mul_inducedLInfOperatorNorm_or_top
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (A : Matrix m n ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : Function.Injective fun x : n → ℝ => A *ᵥ x) :
    ∀ B : Matrix n m ℝ,
      (let φ : Matrix n m ℝ → EReal := fun B =>
        sSup
          ((fun p : (n → ℝ) × (m → ℝ) × (m → ℝ) =>
            let x := p.1
            let y := p.2.1
            let v := p.2.2
            (((sSup (Set.range fun i : n => |(B *ᵥ y) i - x i|)) : ℝ) : EReal)) ''
            {p : (n → ℝ) × (m → ℝ) × (m → ℝ) |
              let x := p.1
              let y := p.2.1
              let v := p.2.2
              y = A *ᵥ x + v ∧ sSup (Set.range fun i : m => |v i|) ≤ ε})
      φ B) ≤
        if B * A = 1 then
          ((ε * inducedLInfOperatorNorm B : ℝ) : EReal)
        else
          ⊤ := by
  intro B
  by_cases hBA : B * A = 1
  · -- Rewrite the admissible error through the noise vector, then bound the two finite suprema.
    simp only [hBA, if_true]
    dsimp
    refine sSup_le ?_
    rintro z ⟨⟨x, y, v⟩, hp, rfl⟩
    dsimp at hp ⊢
    rcases hp with ⟨hy, hv⟩
    have herror :
        (fun i : n => (B *ᵥ y) i - x i) = B *ᵥ v :=
      error_eq_mulVec_noise_of_left_inverse A B x y v hBA hy
    have herror_apply : ∀ i : n, (B *ᵥ y) i - x i = (B *ᵥ v) i := by
      -- Read the vector identity coordinatewise so it rewrites the absolute-value range.
      intro i
      simpa using congrFun herror i
    have hsSup :
        sSup (Set.range fun i : n => |(B *ᵥ y) i - x i|) ≤ ε * inducedLInfOperatorNorm B := by
      -- Replace the error range by the noise-propagation range, then apply the operator-norm bound.
      simpa [herror_apply] using
        sSup_abs_mulVec_le_epsilon_mul_inducedLInfOperatorNorm B v hε hv
    exact EReal.coe_le_coe_iff.mpr hsSup
  · -- If `B * A ≠ 1`, the right-hand side is `⊤`, so the estimate is immediate.
    simp [hBA]

/-
Consider the linear measurement model y = Ax + v, where A ∈ ℝ^{m × n} has rank n with m ≥ n, x ∈
ℝ^n, y, v ∈ ℝ^m, and the noise satisfies ‖v‖_{∞} ≤ ε, ε ≥ 0, with ‖z‖_{∞} = max_{1 ≤ i ≤ k} |zᵢ| for
z = (z₁, ..., zₖ) ∈ ℝ^k. Restrict the estimator to the linear form x = By, where B ∈ ℝ^{n × m}, and
define the estimation error by e = x - x. For each B, define φ(B) = sup{‖By - x‖_{∞} | y = Ax + v, x
∈
ℝ^n, v ∈ ℝ^m, ‖v‖_{∞} ≤ ε}. Consequently, prove that the minimax linear estimator is obtained by
solving minimum infinity - norm left inverse.
-/
theorem minimax_linear_estimator_iff_optimal_minimum_infinity_norm_left_inverse
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (A : Matrix m n ℝ) (ε : ℝ)
    (hε : 0 < ε)
    (hA : Function.Injective fun x : n → ℝ => A *ᵥ x)
    (B : Matrix n m ℝ) :
    (let φ : Matrix n m ℝ → EReal := fun B' =>
      sSup
        ((fun p : (n → ℝ) × (m → ℝ) × (m → ℝ) =>
          let x := p.1
          let y := p.2.1
          let v := p.2.2
          (((sSup (Set.range fun i : n => |(B' *ᵥ y) i - x i|)) : ℝ) : EReal)) ''
          {p : (n → ℝ) × (m → ℝ) × (m → ℝ) |
            let x := p.1
            let y := p.2.1
            let v := p.2.2
            y = A *ᵥ x + v ∧ sSup (Set.range fun i : m => |v i|) ≤ ε});
      (∀ Btilde : Matrix n m ℝ, φ B ≤ φ Btilde)) →
    MinimumInfinityNormLeftInverseProblem.isOptimal
      (MinimumInfinityNormLeftInverseProblem.standard A) B := by
  intro hmin
  set φ : Matrix n m ℝ → EReal := fun B' =>
    sSup
      ((fun p : (n → ℝ) × (m → ℝ) × (m → ℝ) =>
        let x := p.1
        let y := p.2.1
        let v := p.2.2
        (((sSup (Set.range fun i : n => |(B' *ᵥ y) i - x i|)) : ℝ) : EReal)) ''
        {p : (n → ℝ) × (m → ℝ) × (m → ℝ) |
          let x := p.1
          let y := p.2.1
          let v := p.2.2
          y = A *ᵥ x + v ∧ sSup (Set.range fun i : m => |v i|) ≤ ε}) with hφ
  have hmin' : ∀ Btilde : Matrix n m ℝ, φ B ≤ φ Btilde := by
    intro Btilde
    simpa [φ, hφ] using hmin Btilde
  -- First build one feasible estimator from injectivity so the minimax value is finite somewhere.
  have hker : LinearMap.ker (Matrix.toLin' A) = ⊥ := by
    refine LinearMap.ker_eq_bot.mpr ?_
    simpa [Matrix.toLin'_apply] using hA
  obtain ⟨g, hg⟩ := (Matrix.toLin' A).exists_leftInverse_of_injective hker
  let B0 : Matrix n m ℝ := LinearMap.toMatrix' g
  have hB0A : B0 * A = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg, Matrix.toLin'_one]
  have hphi_B0 : φ B0 ≤ ((ε * inducedLInfOperatorNorm B0 : ℝ) : EReal) := by
    simpa [φ, hφ, hB0A] using
      phi_eq_epsilon_mul_inducedLInfOperatorNorm_or_top A ε hε.le hA B0
  -- Next rule out the case `B * A ≠ 1` by producing arbitrarily large admissible errors.
  have hBA : B * A = 1 := by
    by_contra hBA
    have hentry : ∃ i : n, ∃ j : n, (B * A) i j ≠ (1 : Matrix n n ℝ) i j := by
      by_contra hentry
      apply hBA
      ext i j
      by_contra hij
      exact hentry ⟨i, j, hij⟩
    rcases hentry with ⟨i, j, hij⟩
    let δ : ℝ := (B * A) i j - (1 : Matrix n n ℝ) i j
    have hδ : δ ≠ 0 := by
      exact sub_ne_zero.mpr hij
    have hδabs : 0 < |δ| := abs_pos.mpr hδ
    let R0 : ℝ := ε * inducedLInfOperatorNorm B0 + 1
    obtain ⟨N, hN⟩ := exists_nat_gt (R0 / |δ|)
    let x : n → ℝ := Pi.single j (N : ℝ)
    have hcoord :
        (B *ᵥ (A *ᵥ x)) i - x i = (N : ℝ) * δ := by
      have hmulAx : (B *ᵥ (A *ᵥ x)) i = ((B * A) *ᵥ x) i := by
        simpa using congrFun (Matrix.mulVec_mulVec x B A) i
      have hsingle : ((B * A) *ᵥ x) i = (N : ℝ) * (B * A) i j := by
        dsimp [x]
        simp [Matrix.mulVec_single, mul_comm]
      have hx_i : x i = (N : ℝ) * (1 : Matrix n n ℝ) i j := by
        dsimp [x]
        by_cases hji : i = j
        · subst hji
          simp
        · simp [Pi.single_apply, hji, Matrix.one_apply]
      calc
        (B *ᵥ (A *ᵥ x)) i - x i = ((B * A) *ᵥ x) i - x i := by rw [hmulAx]
        _ = (N : ℝ) * (B * A) i j - (N : ℝ) * (1 : Matrix n n ℝ) i j := by rw [hsingle, hx_i]
        _ = (N : ℝ) * ((B * A) i j - (1 : Matrix n n ℝ) i j) := by ring
        _ = (N : ℝ) * δ := by rfl
    have hcoord_abs :
        R0 < |(B *ᵥ (A *ᵥ x)) i - x i| := by
      have hN' : R0 / |δ| < (N : ℝ) := by
        exact_mod_cast hN
      have hmul : R0 < (N : ℝ) * |δ| := by
        exact (div_lt_iff₀ hδabs).mp hN'
      have hNnonneg : 0 ≤ (N : ℝ) := by
        exact_mod_cast Nat.zero_le N
      calc
        R0 < (N : ℝ) * |δ| := hmul
        _ = |(N : ℝ) * δ| := by rw [abs_mul, abs_of_nonneg hNnonneg]
        _ = |(B *ᵥ (A *ᵥ x)) i - x i| := by rw [hcoord]
    have hvalue :
        R0 ≤ sSup (Set.range fun k : n => |(B *ᵥ (A *ᵥ x)) k - x k|) := by
      exact (le_of_lt hcoord_abs).trans <|
        le_csSup (Finite.bddAbove_range _) ⟨i, rfl⟩
    have hphi_lower : ((R0 : ℝ) : EReal) ≤ φ B := by
      have hmem :
          (((sSup (Set.range fun k : n => |(B *ᵥ (A *ᵥ x)) k - x k|)) : ℝ) : EReal) ∈
            ((fun p : (n → ℝ) × (m → ℝ) × (m → ℝ) =>
              let x := p.1
              let y := p.2.1
              let v := p.2.2
              (((sSup (Set.range fun k : n => |(B *ᵥ y) k - x k|)) : ℝ) : EReal)) ''
              {p : (n → ℝ) × (m → ℝ) × (m → ℝ) |
                let x := p.1
                let y := p.2.1
                let v := p.2.2
                y = A *ᵥ x + v ∧ sSup (Set.range fun k : m => |v k|) ≤ ε}) := by
        refine ⟨(x, A *ᵥ x, 0), ?_, rfl⟩
        dsimp
        constructor
        · simp
        · by_cases hm : Nonempty m
          · exact csSup_le (Set.range_nonempty fun k : m => |(0 : m → ℝ) k|) fun b hb => by
              rcases hb with ⟨k, rfl⟩
              simp [hε.le]
          · haveI : IsEmpty m := not_nonempty_iff.mp hm
            have hrange : Set.range (fun k : m => |(0 : ℝ)|) = (∅ : Set ℝ) := by
              ext b
              constructor
              · intro hb
                rcases hb with ⟨k, rfl⟩
                exact isEmptyElim k
              · intro hb
                exact False.elim hb
            rw [hrange]
            simp [hε.le]
      exact (EReal.coe_le_coe_iff.mpr hvalue).trans (le_sSup hmem)
    have hbound :
        ((R0 : ℝ) : EReal) ≤ ((ε * inducedLInfOperatorNorm B0 : ℝ) : EReal) := by
      exact hphi_lower.trans ((hmin' B0).trans hphi_B0)
    have hbound_real : R0 ≤ ε * inducedLInfOperatorNorm B0 := by
      exact EReal.coe_le_coe_iff.mp hbound
    linarith
  -- Finally compare `B` with every other left inverse using the matching lower and upper bounds.
  have hrow :
      ∃ i : n, (∑ j, |B i j|) = inducedLInfOperatorNorm B := by
    have hmem :
        inducedLInfOperatorNorm B ∈ Set.range fun i : n => ∑ j, |B i j| := by
      simpa [inducedLInfOperatorNorm] using
        Set.Nonempty.csSup_mem (Set.range_nonempty fun i : n => ∑ j, |B i j|) (Set.finite_range _)
    rcases hmem with ⟨i, hi⟩
    exact ⟨i, hi⟩
  rcases hrow with ⟨i0, hi0⟩
  let v : m → ℝ := fun j => ε * Real.sign (B i0 j)
  have hv : sSup (Set.range fun j : m => |v j|) ≤ ε := by
    by_cases hm : Nonempty m
    · exact csSup_le (Set.range_nonempty fun j : m => |v j|) fun b hb => by
        rcases hb with ⟨j, rfl⟩
        have hsign : |Real.sign (B i0 j)| ≤ 1 := by
          rcases Real.sign_apply_eq (B i0 j) with hsign | hsign | hsign
          · rw [hsign]
            norm_num
          · rw [hsign]
            norm_num
          · rw [hsign]
            norm_num
        dsimp [v]
        calc
          |ε * Real.sign (B i0 j)| = ε * |Real.sign (B i0 j)| := by
            rw [abs_mul, abs_of_nonneg hε.le]
          _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hsign hε.le
          _ = ε := by ring
    · haveI : IsEmpty m := not_nonempty_iff.mp hm
      have hrange : Set.range (fun j : m => |v j|) = (∅ : Set ℝ) := by
        ext b
        constructor
        · intro hb
          rcases hb with ⟨j, rfl⟩
          exact isEmptyElim j
        · intro hb
          exact False.elim hb
      rw [hrange]
      simp [hε.le]
  have hcoord_i0 :
      (B *ᵥ v) i0 = ε * ∑ j, |B i0 j| := by
    calc
      (B *ᵥ v) i0 = ∑ j, B i0 j * v j := by
        simp [Matrix.mulVec, dotProduct]
      _ = ∑ j, ε * |B i0 j| := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        dsimp [v]
        have hsignmul : B i0 j * Real.sign (B i0 j) = |B i0 j| := by
          obtain hneg | hzero | hpos := lt_trichotomy (B i0 j) 0
          · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
            ring
          · rw [hzero, Real.sign_zero]
            simp
          · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
            ring
        calc
          B i0 j * (ε * Real.sign (B i0 j)) = ε * (B i0 j * Real.sign (B i0 j)) := by ring
          _ = ε * |B i0 j| := by rw [hsignmul]
      _ = ε * ∑ j, |B i0 j| := by
        rw [Finset.mul_sum]
  have hnorm_lower :
      ((ε * inducedLInfOperatorNorm B : ℝ) : EReal) ≤ φ B := by
    have hsum_nonneg : 0 ≤ ∑ j, |B i0 j| := by
      exact Finset.sum_nonneg fun j hj => abs_nonneg (B i0 j)
    have hvalue :
        ε * inducedLInfOperatorNorm B ≤ sSup (Set.range fun k : n => |(B *ᵥ v) k|) := by
      have habs :
          |(B *ᵥ v) i0| = ε * inducedLInfOperatorNorm B := by
        rw [hcoord_i0, hi0]
        have hnonneg : 0 ≤ ε * inducedLInfOperatorNorm B := by
          rw [← hi0]
          exact mul_nonneg hε.le hsum_nonneg
        exact abs_of_nonneg hnonneg
      calc
        ε * inducedLInfOperatorNorm B = |(B *ᵥ v) i0| := habs.symm
        _ ≤ sSup (Set.range fun k : n => |(B *ᵥ v) k|) := by
          exact le_csSup (Finite.bddAbove_range _) ⟨i0, rfl⟩
    have hmem :
        (((sSup (Set.range fun k : n => |(B *ᵥ v) k|)) : ℝ) : EReal) ∈
          ((fun p : (n → ℝ) × (m → ℝ) × (m → ℝ) =>
            let x := p.1
            let y := p.2.1
            let v := p.2.2
            (((sSup (Set.range fun k : n => |(B *ᵥ y) k - x k|)) : ℝ) : EReal)) ''
            {p : (n → ℝ) × (m → ℝ) × (m → ℝ) |
              let x := p.1
              let y := p.2.1
              let v := p.2.2
              y = A *ᵥ x + v ∧ sSup (Set.range fun k : m => |v k|) ≤ ε}) := by
      refine ⟨(0, v, v), ?_, ?_⟩
      · dsimp
        constructor
        · simp
        · exact hv
      · dsimp
        simp
    exact (EReal.coe_le_coe_iff.mpr hvalue).trans (le_sSup hmem)
  refine ⟨hBA, ?_⟩
  intro Btilde hBtilde
  have hBtildeA : Btilde * A = 1 := by
    simpa [MinimumInfinityNormLeftInverseProblem.standard] using hBtilde
  have hphi_Btilde :
      φ Btilde ≤ ((ε * inducedLInfOperatorNorm Btilde : ℝ) : EReal) := by
    have hphi_Btilde' :
        φ Btilde ≤ if Btilde * A = 1 then ((ε * inducedLInfOperatorNorm Btilde : ℝ) : EReal) else ⊤ := by
      simpa [φ, hφ] using
        phi_eq_epsilon_mul_inducedLInfOperatorNorm_or_top A ε hε.le hA Btilde
    rw [if_pos hBtildeA] at hphi_Btilde'
    exact hphi_Btilde'
  have hcompare :
      ((ε * inducedLInfOperatorNorm B : ℝ) : EReal) ≤
        ((ε * inducedLInfOperatorNorm Btilde : ℝ) : EReal) := by
    exact hnorm_lower.trans ((hmin' Btilde).trans hphi_Btilde)
  have hcompare_real :
      ε * inducedLInfOperatorNorm B ≤ ε * inducedLInfOperatorNorm Btilde := by
    exact EReal.coe_le_coe_iff.mp hcompare
  exact le_of_mul_le_mul_left hcompare_real hε

end «problem-169»
