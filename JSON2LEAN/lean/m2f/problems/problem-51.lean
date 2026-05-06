import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-51»
/-
A second-order cone program is an optimization problem with an affine objective, affine equality or
inequality constraints, and finitely many second-order cone constraints of the form ‖Aᵢ x + bᵢ‖_2 ≤
c_iᵀ x + dᵢ.
-/
structure SecondOrderConeProgram where
  n : ℕ
  m : ℕ
  k : ℕ
  objective : Fin n → ℝ
  objectiveConst : ℝ
  eqA : Fin m → Fin n → ℝ
  eqb : Fin m → ℝ
  ineqA : Fin m → Fin n → ℝ
  ineqb : Fin m → ℝ
  socDim : Fin k → ℕ
  socA : (i : Fin k) → Fin (socDim i) → Fin n → ℝ
  socb : (i : Fin k) → Fin (socDim i) → ℝ
  socc : Fin k → Fin n → ℝ
  socd : Fin k → ℝ

def SecondOrderConeProgram.objectiveValue (P : SecondOrderConeProgram) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.objective j * x j + P.objectiveConst

def SecondOrderConeProgram.satisfiesSocConstraint
    (P : SecondOrderConeProgram) (i : Fin P.k) (x : Fin P.n → ℝ) : Prop :=
  Real.sqrt
      (∑ r : Fin (P.socDim i),
        (∑ j : Fin P.n, P.socA i r j * x j + P.socb i r) ^ 2) ≤
    (∑ j : Fin P.n, P.socc i j * x j) + P.socd i

def SecondOrderConeProgram.IsFeasible
    (P : SecondOrderConeProgram) (x : Fin P.n → ℝ) : Prop :=
  (∀ h : Fin P.m, (∑ j : Fin P.n, P.eqA h j * x j) + P.eqb h = 0) ∧
    (∀ h : Fin P.m, (∑ j : Fin P.n, P.ineqA h j * x j) + P.ineqb h ≤ 0) ∧
    ∀ i : Fin P.k, P.satisfiesSocConstraint i x


/-
A point is feasible for an optimization problem if it satisfies all the constraints.
-/
def SecondOrderConeProgram.IsOptimalMinimizer
    (P : SecondOrderConeProgram) (xStar : Fin P.n → ℝ) : Prop :=
  P.IsFeasible xStar ∧
    ∀ x : Fin P.n → ℝ, P.IsFeasible x → P.objectiveValue xStar ≤ P.objectiveValue x

def SecondOrderConeProgram.optimalValueMin (P : SecondOrderConeProgram) : ℝ :=
  sInf { v : ℝ | ∃ x : Fin P.n → ℝ, P.IsFeasible x ∧ P.objectiveValue x = v }

structure ReciprocalSumMaximization where
  n : ℕ
  m : ℕ
  a : Fin m → Fin n → ℝ
  b : Fin m → ℝ

def ReciprocalSumMaximization.objectiveValue
    (P : ReciprocalSumMaximization) : (Fin P.n → ℝ) → ℝ :=
  fun x : Fin P.n → ℝ =>
    (∑ i : Fin P.m, ((∑ j : Fin P.n, P.a i j * x j) - P.b i)⁻¹)⁻¹

def ReciprocalSumMaximization.isFeasible
    (P : ReciprocalSumMaximization) : (Fin P.n → ℝ) → Prop :=
  fun x : Fin P.n → ℝ =>
    ∀ i : Fin P.m, (∑ j : Fin P.n, P.a i j * x j) > P.b i

def ReciprocalSumMaximization.IsOptimalSolution
    (P : ReciprocalSumMaximization) (xStar : Fin P.n → ℝ) : Prop :=
  P.isFeasible xStar ∧
    ∀ x : Fin P.n → ℝ, P.isFeasible x →
      P.objectiveValue x ≤ P.objectiveValue xStar

/-
Consider the second-order cone program minimize & sum_{i = 1}^m tᵢ; subject to & ≤ ft‖[2; tᵢ-(a_iᵀ
x-bᵢ)]‖_2 ≤ tᵢ+(a_iᵀ x-bᵢ), i = 1,..., m,; & tᵢ ≥ 0, i = 1,..., m, array
-/
structure ReciprocalSumSOCP where
  n : ℕ
  m : ℕ
  a : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  socLeft : (Fin n → ℝ) → (Fin m → ℝ) → Fin m → (Fin 2 → ℝ) :=
    fun x t i =>
      fun r =>
        if _ : (r : ℕ) = 0 then
          2
        else
          t i - ((∑ j : Fin n, a i j * x j) - b i)
  socRight : (Fin n → ℝ) → (Fin m → ℝ) → Fin m → ℝ :=
    fun x t i =>
      t i + ((∑ j : Fin n, a i j * x j) - b i)

def ReciprocalSumSOCP.objectiveValue
    (P : ReciprocalSumSOCP) : (Fin P.m → ℝ) → ℝ :=
  fun t => ∑ i : Fin P.m, t i

def ReciprocalSumSOCP.satisfiesSocConstraint
    (P : ReciprocalSumSOCP) : (Fin P.n → ℝ) → (Fin P.m → ℝ) → Fin P.m → Prop :=
  fun x t i =>
    Real.sqrt (∑ r : Fin 2, (P.socLeft x t i r) ^ 2) ≤ P.socRight x t i

def ReciprocalSumSOCP.isFeasible
    (P : ReciprocalSumSOCP) : (Fin P.n → ℝ) → (Fin P.m → ℝ) → Prop :=
  fun x t =>
    (∀ i : Fin P.m, P.satisfiesSocConstraint x t i) ∧
      ∀ i : Fin P.m, 0 ≤ t i

/-
Let A ∈ ℝ^{m × n}, b ∈ ℝ^m, and let a_iᵀ denote the ith row of A. For x ∈ ℝ^n and y, z ∈ ℝ, prove
that xᵀ x ≤ yz, y ≥ 0, z ≥ 0 if and only if ≤ ft‖[2x; y-z]‖_2 ≤ y+z, y ≥ 0, z ≥ 0.
-/
theorem sq_le_mul_iff_soc_constraint
    {n : ℕ} (x : Fin n → ℝ) (y z : ℝ) :
    ((∑ i : Fin n, (x i) ^ 2) ≤ y * z ∧ 0 ≤ y ∧ 0 ≤ z) ↔
      (Real.sqrt
          ((∑ i : Fin n, (2 * x i) ^ 2) + (y - z) ^ 2) ≤ y + z ∧
        0 ≤ y ∧ 0 ≤ z) := by
  -- Normalize the doubled-square term so both directions reduce to polynomial algebra.
  have hsum : (∑ i : Fin n, (2 * x i) ^ 2) = 4 * ∑ i : Fin n, (x i) ^ 2 := by
    calc
      ∑ i : Fin n, (2 * x i) ^ 2 = ∑ i : Fin n, 4 * (x i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = 4 * ∑ i : Fin n, (x i) ^ 2 := by
        symm
        exact Finset.mul_sum _ _ _
  constructor
  · rintro ⟨hxy, hy, hz⟩
    refine ⟨?_, hy, hz⟩
    -- Convert the square-root inequality to a squared inequality using nonnegativity of `y + z`.
    rw [Real.sqrt_le_iff]
    constructor
    · nlinarith
    · -- After rewriting the norm term, the result is a direct quadratic consequence of `hxy`.
      rw [hsum]
      nlinarith [hxy]
  · rintro ⟨hsqrt, hy, hz⟩
    refine ⟨?_, hy, hz⟩
    -- Extract the squared bound from the square-root constraint and normalize the sum of squares.
    have hsq : ((∑ i : Fin n, (2 * x i) ^ 2) + (y - z) ^ 2) ≤ (y + z) ^ 2 := by
      exact (Real.sqrt_le_iff).mp hsqrt |>.2
    rw [hsum] at hsq
    -- The normalized squared inequality is equivalent to the original product bound.
    nlinarith

/-
Let A ∈ ℝ^{m × n}, b ∈ ℝ^m, and let a_iᵀ denote the ith row of A. Also prove that reciprocal sum
maximization is equivalent to equivalent second-order cone program in the following sense: for each
feasible x, the minimum over t equals sum_{i = 1}^m (1)/(a_iᵀ x-bᵢ), so the two problems have the
same optimal solutions in x, and if p* is the optimal value of the original problem and q* is the
optimal value of the SOCP, then p* = 1/q*.
-/
theorem reciprocal_sum_maximization_equiv_socp
    (P : ReciprocalSumMaximization)
    (hsoc_attained :
      let Q : ReciprocalSumSOCP := {
        n := P.n
        m := P.m
        a := P.a
        b := P.b
      }
      ∃ xStar : Fin P.n → ℝ, ∃ tStar : Fin P.m → ℝ,
        Q.isFeasible xStar tStar ∧
        0 < Q.objectiveValue tStar ∧
        ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ,
          Q.isFeasible x t → Q.objectiveValue tStar ≤ Q.objectiveValue t) :
    let Q : ReciprocalSumSOCP := {
      n := P.n
      m := P.m
      a := P.a
      b := P.b
    }
    (∀ x : Fin P.n → ℝ, P.isFeasible x →
      sInf {v : ℝ | ∃ t : Fin P.m → ℝ, Q.isFeasible x t ∧ Q.objectiveValue t = v} =
        ∑ i : Fin P.m, (((∑ j : Fin P.n, P.a i j * x j) - P.b i)⁻¹)) ∧
    (∀ xStar : Fin P.n → ℝ,
      P.IsOptimalSolution xStar ↔
        ∃ tStar : Fin P.m → ℝ,
          Q.isFeasible xStar tStar ∧
          ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ,
            Q.isFeasible x t → Q.objectiveValue tStar ≤ Q.objectiveValue t) ∧
    (sSup {v : ℝ | ∃ x : Fin P.n → ℝ, P.isFeasible x ∧ P.objectiveValue x = v} =
      (sInf {v : ℝ | ∃ xt : (Fin P.n → ℝ) × (Fin P.m → ℝ),
        Q.isFeasible xt.1 xt.2 ∧ Q.objectiveValue xt.2 = v})⁻¹) := by
  classical
  dsimp
  let Q : ReciprocalSumSOCP := {
    n := P.n
    m := P.m
    a := P.a
    b := P.b
  }
  let slack : (Fin P.n → ℝ) → Fin P.m → ℝ :=
    fun x i => (∑ j : Fin P.n, P.a i j * x j) - P.b i
  by_cases hm : P.m = 0
  · -- With no SOC coordinates, the assumed positive attained SOCP value is impossible.
    have hsoc_attained' :
        ∃ xStar : Fin P.n → ℝ, ∃ tStar : Fin P.m → ℝ,
          Q.isFeasible xStar tStar ∧
          0 < Q.objectiveValue tStar ∧
          ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ,
            Q.isFeasible x t → Q.objectiveValue tStar ≤ Q.objectiveValue t := by
      simpa [Q] using hsoc_attained
    rcases hsoc_attained' with ⟨xStar, tStar, _, htStar_pos, _⟩
    have hzero : Q.objectiveValue tStar = 0 := by
      letI : IsEmpty (Fin P.m) := by
        rw [hm]
        infer_instance
      simp [Q, ReciprocalSumSOCP.objectiveValue]
    exfalso
    linarith
  · haveI : NeZero P.m := ⟨hm⟩
    let fixedSocValues : (Fin P.n → ℝ) → Set ℝ :=
      fun x => {v : ℝ | ∃ t : Fin P.m → ℝ, Q.isFeasible x t ∧ Q.objectiveValue t = v}
    -- Route correction: rewriting the SOC constraint to the explicit `sqrt (4 + ...)` form
    -- makes the product bound `1 ≤ t_i * slack_i` available by direct squaring.
    have hsoc_explicit :
        ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ, ∀ i : Fin P.m,
          Q.satisfiesSocConstraint x t i ↔
            Real.sqrt (4 + (t i - slack x i) ^ 2) ≤ t i + slack x i := by
      intro x t i
      simp [Q, slack, ReciprocalSumSOCP.satisfiesSocConstraint, Fin.sum_univ_two]
      norm_num
    -- Convert each SOC constraint together with `t_i ≥ 0` into the key product lower bound.
    have hsoc_product :
        ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ, ∀ i : Fin P.m,
          Q.isFeasible x t → 1 ≤ t i * slack x i := by
      intro x t i hfeas
      rcases hfeas with ⟨hsoc_all, _⟩
      have hsoc_i : Real.sqrt (4 + (t i - slack x i) ^ 2) ≤ t i + slack x i := by
        exact (hsoc_explicit x t i).1 (hsoc_all i)
      have hsq : 4 + (t i - slack x i) ^ 2 ≤ (t i + slack x i) ^ 2 := by
        exact (Real.sqrt_le_iff).1 hsoc_i |>.2
      nlinarith
    -- The product lower bound forces each slack term to be strictly positive.
    have hsoc_slack_pos :
        ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ, ∀ i : Fin P.m,
          Q.isFeasible x t → 0 < slack x i := by
      intro x t i hfeas
      have hprod : 1 ≤ t i * slack x i := hsoc_product x t i hfeas
      have ht0 : 0 ≤ t i := hfeas.2 i
      by_contra hsnot
      have hsle : slack x i ≤ 0 := le_of_not_gt hsnot
      have hts : t i * slack x i ≤ 0 := by nlinarith
      linarith
    -- Any SOCP-feasible pair gives an original feasible `x` because all slacks are positive.
    have horig_of_soc :
        ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ, Q.isFeasible x t → P.isFeasible x := by
      intro x t hfeas i
      have hspos : 0 < slack x i := hsoc_slack_pos x t i hfeas
      simpa [slack, sub_pos] using hspos
    -- The reciprocal slack vector is feasible for the SOCP at every feasible `x`.
    have hreciprocal_feasible :
        ∀ x : Fin P.n → ℝ, P.isFeasible x → Q.isFeasible x (fun i => (slack x i)⁻¹) := by
      intro x hx
      refine ⟨?_, ?_⟩
      · intro i
        have hspos : 0 < slack x i := by
          simpa [slack, sub_pos] using hx i
        have hsq :
            ((∑ j : Fin 1, ((fun _ : Fin 1 => (1 : ℝ)) j) ^ 2) ≤
                (slack x i)⁻¹ * slack x i ∧
              0 ≤ (slack x i)⁻¹ ∧ 0 ≤ slack x i) := by
          constructor
          · simp [hspos.ne']
          · constructor
            · positivity
            · exact hspos.le
        have hsoc_i :
            Real.sqrt
                ((∑ j : Fin 1, (2 * (fun _ : Fin 1 => (1 : ℝ)) j) ^ 2) +
                  ((slack x i)⁻¹ - slack x i) ^ 2) ≤
              (slack x i)⁻¹ + slack x i := by
          exact (sq_le_mul_iff_soc_constraint (fun _ : Fin 1 => (1 : ℝ)) ((slack x i)⁻¹)
            (slack x i)).1 hsq |>.1
        simpa [Q, slack, ReciprocalSumSOCP.satisfiesSocConstraint, Fin.sum_univ_two] using hsoc_i
      · intro i
        have hspos : 0 < slack x i := by
          simpa [slack, sub_pos] using hx i
        positivity
    -- Every feasible SOCP vector dominates the reciprocal slack vector pointwise.
    have hpointwise_lower :
        ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ, ∀ i : Fin P.m,
          Q.isFeasible x t → (slack x i)⁻¹ ≤ t i := by
      intro x t i hfeas
      have hspos : 0 < slack x i := hsoc_slack_pos x t i hfeas
      have hprod : 1 ≤ t i * slack x i := hsoc_product x t i hfeas
      have hdiv : 1 / (slack x i) ≤ t i := by
        exact (div_le_iff₀ hspos).2 (by simpa [mul_comm] using hprod)
      simpa [one_div] using hdiv
    -- SOCP objective values are nonnegative because every feasible `t_i` is nonnegative.
    have hsoc_objective_nonneg :
        ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ, Q.isFeasible x t → 0 ≤ Q.objectiveValue t := by
      intro x t hfeas
      rcases hfeas with ⟨_, ht_nonneg⟩
      simp [Q, ReciprocalSumSOCP.objectiveValue]
      exact Finset.sum_nonneg fun i _ => ht_nonneg i
    -- Because `m ≠ 0`, a feasible original point has a strictly positive reciprocal-sum.
    have hsum_inv_pos :
        ∀ x : Fin P.n → ℝ, P.isFeasible x → 0 < ∑ i : Fin P.m, (slack x i)⁻¹ := by
      intro x hx
      have hnonneg : ∀ i : Fin P.m, 0 ≤ (slack x i)⁻¹ := by
        intro i
        have hspos : 0 < slack x i := by
          simpa [slack, sub_pos] using hx i
        exact le_of_lt (inv_pos.mpr hspos)
      have hzero_pos : 0 < (slack x 0)⁻¹ := by
        have hspos : 0 < slack x 0 := by
          simpa [slack, sub_pos] using hx 0
        exact inv_pos.mpr hspos
      have hzero_le : (slack x 0)⁻¹ ≤ ∑ i : Fin P.m, (slack x i)⁻¹ := by
        simpa using
          (Finset.single_le_sum (fun i _ => hnonneg i) (by simp : (0 : Fin P.m) ∈ Finset.univ))
      exact lt_of_lt_of_le hzero_pos hzero_le
    -- For fixed feasible `x`, the reciprocal slack vector attains the SOCP infimum.
    have hfixed_inf :
        ∀ x : Fin P.n → ℝ, P.isFeasible x →
          sInf (fixedSocValues x) = ∑ i : Fin P.m, (slack x i)⁻¹ := by
      intro x hx
      let tRec : Fin P.m → ℝ := fun i => (slack x i)⁻¹
      have htRec_feas : Q.isFeasible x tRec := hreciprocal_feasible x hx
      have hnonempty : (fixedSocValues x).Nonempty := by
        refine ⟨Q.objectiveValue tRec, ?_⟩
        exact ⟨tRec, htRec_feas, rfl⟩
      have hlower :
          ∀ v ∈ fixedSocValues x, (∑ i : Fin P.m, (slack x i)⁻¹) ≤ v := by
        intro v hv
        rcases hv with ⟨t, ht_feas, rfl⟩
        calc
          ∑ i : Fin P.m, (slack x i)⁻¹ ≤ ∑ i : Fin P.m, t i := by
            exact Finset.sum_le_sum fun i _ => hpointwise_lower x t i ht_feas
          _ = Q.objectiveValue t := by
            simp [Q, ReciprocalSumSOCP.objectiveValue]
      have hle_inf :
          (∑ i : Fin P.m, (slack x i)⁻¹) ≤ sInf (fixedSocValues x) := by
        exact le_csInf hnonempty hlower
      have hbdd_below : BddBelow (fixedSocValues x) := by
        refine ⟨0, ?_⟩
        intro v hv
        rcases hv with ⟨t, ht_feas, rfl⟩
        exact hsoc_objective_nonneg x t ht_feas
      have hmem :
          (∑ i : Fin P.m, (slack x i)⁻¹) ∈ fixedSocValues x := by
        refine ⟨tRec, htRec_feas, ?_⟩
        simp [tRec, Q, ReciprocalSumSOCP.objectiveValue]
      have hinf_le :
          sInf (fixedSocValues x) ≤ ∑ i : Fin P.m, (slack x i)⁻¹ := by
        exact csInf_le hbdd_below hmem
      exact le_antisymm hinf_le hle_inf
    -- Optimal original solutions are exactly the `x`-coordinates of global SOCP minimizers.
    have hoptimal_x :
        ∀ xStar : Fin P.n → ℝ,
          P.IsOptimalSolution xStar ↔
            ∃ tStar : Fin P.m → ℝ,
              Q.isFeasible xStar tStar ∧
              ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ,
                Q.isFeasible x t → Q.objectiveValue tStar ≤ Q.objectiveValue t := by
      intro xStar
      constructor
      · intro hxStar_opt
        rcases hxStar_opt with ⟨hxStar_feas, hopt⟩
        refine ⟨fun i => (slack xStar i)⁻¹, hreciprocal_feasible xStar hxStar_feas, ?_⟩
        intro x t hxt
        have hx_feas : P.isFeasible x := horig_of_soc x t hxt
        have hobj_le :
            P.objectiveValue x ≤ P.objectiveValue xStar := hopt x hx_feas
        have hx_sum_pos : 0 < ∑ i : Fin P.m, (slack x i)⁻¹ := hsum_inv_pos x hx_feas
        have hStar_sum_pos :
            0 < ∑ i : Fin P.m, (slack xStar i)⁻¹ := hsum_inv_pos xStar hxStar_feas
        have hsum_order :
            (∑ i : Fin P.m, (slack xStar i)⁻¹) ≤ ∑ i : Fin P.m, (slack x i)⁻¹ := by
          have hdiv_order :
              1 / (∑ i : Fin P.m, (slack x i)⁻¹) ≤
                1 / (∑ i : Fin P.m, (slack xStar i)⁻¹) := by
            simpa [ReciprocalSumMaximization.objectiveValue, slack, one_div] using hobj_le
          exact (one_div_le_one_div hx_sum_pos hStar_sum_pos).1 hdiv_order
        have hinf_le_t :
            (∑ i : Fin P.m, (slack x i)⁻¹) ≤ Q.objectiveValue t := by
          have hbdd_below : BddBelow (fixedSocValues x) := by
            refine ⟨0, ?_⟩
            intro v hv
            rcases hv with ⟨u, hu_feas, rfl⟩
            exact hsoc_objective_nonneg x u hu_feas
          have hmem : Q.objectiveValue t ∈ fixedSocValues x := by
            exact ⟨t, hxt, rfl⟩
          have hinf_le : sInf (fixedSocValues x) ≤ Q.objectiveValue t := by
            exact csInf_le hbdd_below hmem
          simpa [hfixed_inf x hx_feas] using hinf_le
        calc
          Q.objectiveValue (fun i => (slack xStar i)⁻¹) =
              ∑ i : Fin P.m, (slack xStar i)⁻¹ := by
                simp [Q, ReciprocalSumSOCP.objectiveValue]
          _ ≤ ∑ i : Fin P.m, (slack x i)⁻¹ := hsum_order
          _ ≤ Q.objectiveValue t := hinf_le_t
      · rintro ⟨tStar, htStar_feas, htmin⟩
        have hxStar_feas : P.isFeasible xStar := horig_of_soc xStar tStar htStar_feas
        refine ⟨hxStar_feas, ?_⟩
        intro x hx
        have htRec_feas : Q.isFeasible x (fun i => (slack x i)⁻¹) := hreciprocal_feasible x hx
        have htStarRec_feas :
            Q.isFeasible xStar (fun i => (slack xStar i)⁻¹) := hreciprocal_feasible xStar hxStar_feas
        have htStar_le_sum_x :
            Q.objectiveValue tStar ≤ ∑ i : Fin P.m, (slack x i)⁻¹ := by
          simpa [Q, ReciprocalSumSOCP.objectiveValue] using
            htmin x (fun i => (slack x i)⁻¹) htRec_feas
        have htStar_le_sum_star :
            Q.objectiveValue tStar ≤ ∑ i : Fin P.m, (slack xStar i)⁻¹ := by
          simpa [Q, ReciprocalSumSOCP.objectiveValue] using
            htmin xStar (fun i => (slack xStar i)⁻¹) htStarRec_feas
        have hsum_star_le_tStar :
            (∑ i : Fin P.m, (slack xStar i)⁻¹) ≤ Q.objectiveValue tStar := by
          have hbdd_below : BddBelow (fixedSocValues xStar) := by
            refine ⟨0, ?_⟩
            intro v hv
            rcases hv with ⟨u, hu_feas, rfl⟩
            exact hsoc_objective_nonneg xStar u hu_feas
          have hmem : Q.objectiveValue tStar ∈ fixedSocValues xStar := by
            exact ⟨tStar, htStar_feas, rfl⟩
          have hinf_le : sInf (fixedSocValues xStar) ≤ Q.objectiveValue tStar := by
            exact csInf_le hbdd_below hmem
          simpa [hfixed_inf xStar hxStar_feas] using hinf_le
        have hsum_star_eq :
            ∑ i : Fin P.m, (slack xStar i)⁻¹ = Q.objectiveValue tStar := by
          exact le_antisymm hsum_star_le_tStar htStar_le_sum_star
        have hsum_order :
            (∑ i : Fin P.m, (slack xStar i)⁻¹) ≤ ∑ i : Fin P.m, (slack x i)⁻¹ := by
          simpa [hsum_star_eq] using htStar_le_sum_x
        have hx_sum_pos : 0 < ∑ i : Fin P.m, (slack x i)⁻¹ := hsum_inv_pos x hx
        have hStar_sum_pos :
            0 < ∑ i : Fin P.m, (slack xStar i)⁻¹ := hsum_inv_pos xStar hxStar_feas
        have hobj_le :
            1 / (∑ i : Fin P.m, (slack x i)⁻¹) ≤
              1 / (∑ i : Fin P.m, (slack xStar i)⁻¹) := by
          exact (one_div_le_one_div hx_sum_pos hStar_sum_pos).2 hsum_order
        simpa [ReciprocalSumMaximization.objectiveValue, slack, one_div] using hobj_le
    have hsoc_attained' :
        ∃ xStar : Fin P.n → ℝ, ∃ tStar : Fin P.m → ℝ,
          Q.isFeasible xStar tStar ∧
          0 < Q.objectiveValue tStar ∧
          ∀ x : Fin P.n → ℝ, ∀ t : Fin P.m → ℝ,
            Q.isFeasible x t → Q.objectiveValue tStar ≤ Q.objectiveValue t := by
      simpa [Q] using hsoc_attained
    rcases hsoc_attained' with ⟨xStar, tStar, htStar_feas, htStar_pos, htmin⟩
    -- Use the attained SOCP minimizer to identify both extremal values by witnesses.
    have hxStar_opt : P.IsOptimalSolution xStar := by
      exact (hoptimal_x xStar).2 ⟨tStar, htStar_feas, htmin⟩
    have hxStar_feas : P.isFeasible xStar := hxStar_opt.1
    let originalValues : Set ℝ :=
      {v : ℝ | ∃ x : Fin P.n → ℝ, P.isFeasible x ∧ P.objectiveValue x = v}
    let socValues : Set ℝ :=
      {v : ℝ | ∃ xt : (Fin P.n → ℝ) × (Fin P.m → ℝ),
        Q.isFeasible xt.1 xt.2 ∧ Q.objectiveValue xt.2 = v}
    have hsup_original : sSup originalValues = P.objectiveValue xStar := by
      have hnonempty : originalValues.Nonempty := by
        refine ⟨P.objectiveValue xStar, ?_⟩
        exact ⟨xStar, hxStar_feas, rfl⟩
      have hupper : BddAbove originalValues := by
        refine ⟨P.objectiveValue xStar, ?_⟩
        intro v hv
        rcases hv with ⟨x, hx, rfl⟩
        exact hxStar_opt.2 x hx
      refine le_antisymm ?_ (le_csSup hupper ?_)
      · exact csSup_le hnonempty fun v hv => by
          rcases hv with ⟨x, hx, rfl⟩
          exact hxStar_opt.2 x hx
      · exact ⟨xStar, hxStar_feas, rfl⟩
    have hinf_soc : sInf socValues = Q.objectiveValue tStar := by
      have hnonempty : socValues.Nonempty := by
        refine ⟨Q.objectiveValue tStar, ?_⟩
        exact ⟨(xStar, tStar), htStar_feas, rfl⟩
      have hlower : ∀ v ∈ socValues, Q.objectiveValue tStar ≤ v := by
        intro v hv
        rcases hv with ⟨xt, hxt, rfl⟩
        exact htmin xt.1 xt.2 hxt
      have hbdd_below : BddBelow socValues := by
        exact ⟨Q.objectiveValue tStar, hlower⟩
      refine le_antisymm (csInf_le hbdd_below ?_) (le_csInf hnonempty hlower)
      exact ⟨(xStar, tStar), htStar_feas, rfl⟩
    have hsum_star_le_tStar :
        (∑ i : Fin P.m, (slack xStar i)⁻¹) ≤ Q.objectiveValue tStar := by
      have hbdd_below : BddBelow (fixedSocValues xStar) := by
        refine ⟨0, ?_⟩
        intro v hv
        rcases hv with ⟨u, hu_feas, rfl⟩
        exact hsoc_objective_nonneg xStar u hu_feas
      have hmem : Q.objectiveValue tStar ∈ fixedSocValues xStar := by
        exact ⟨tStar, htStar_feas, rfl⟩
      have hinf_le : sInf (fixedSocValues xStar) ≤ Q.objectiveValue tStar := by
        exact csInf_le hbdd_below hmem
      simpa [hfixed_inf xStar hxStar_feas] using hinf_le
    have htStar_le_sum_star :
        Q.objectiveValue tStar ≤ ∑ i : Fin P.m, (slack xStar i)⁻¹ := by
      simpa [Q, ReciprocalSumSOCP.objectiveValue] using
        htmin xStar (fun i => (slack xStar i)⁻¹) (hreciprocal_feasible xStar hxStar_feas)
    have hsum_star_eq :
        ∑ i : Fin P.m, (slack xStar i)⁻¹ = Q.objectiveValue tStar := by
      exact le_antisymm hsum_star_le_tStar htStar_le_sum_star
    have hvalue_eq : P.objectiveValue xStar = (Q.objectiveValue tStar)⁻¹ := by
      calc
        P.objectiveValue xStar = (∑ i : Fin P.m, (slack xStar i)⁻¹)⁻¹ := by
          simp [ReciprocalSumMaximization.objectiveValue, slack]
        _ = (Q.objectiveValue tStar)⁻¹ := by
          rw [hsum_star_eq]
    refine ⟨?_, ?_, ?_⟩
    · -- This first conjunct is the fixed-`x` infimum formula established above.
      intro x hx
      simpa [Q, fixedSocValues, slack] using hfixed_inf x hx
    · -- This second conjunct records the equivalence between original maximizers and SOCP minimizers.
      intro x
      simpa [Q] using hoptimal_x x
    · -- The last conjunct identifies the attained supremum and infimum through the same witness.
      calc
        sSup {v : ℝ | ∃ x : Fin P.n → ℝ, P.isFeasible x ∧ P.objectiveValue x = v} =
            P.objectiveValue xStar := by
              simpa [originalValues] using hsup_original
        _ = (Q.objectiveValue tStar)⁻¹ := hvalue_eq
        _ = (sInf {v : ℝ | ∃ xt : (Fin P.n → ℝ) × (Fin P.m → ℝ),
              Q.isFeasible xt.1 xt.2 ∧ Q.objectiveValue xt.2 = v})⁻¹ := by
              rw [hinf_soc]

end «problem-51»
