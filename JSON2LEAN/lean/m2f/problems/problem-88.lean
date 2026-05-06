import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-88»

-- Exercise_17_7__a_

/- [BLOCK Exercise 17.7-(a) | 14 | defn]
For a directed graph with n nodes and m edges, the node-edge incidence matrix is the matrix A ∈
ℝ^n × m with entries A_ij=-1 if edge j leaves node i, A_ij=1 if edge j enters node
i, and A_ij=0 otherwise.
-/
def nodeEdgeIncidenceMatrix (n m : ℕ) (tail head : Fin m → Fin n) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j =>
    if i = head j then
      1
    else if i = tail j then
      -1
    else
      0

/-- The `i`-th consumer coordinate corresponds to the node with index `k + i`. -/
private lemma consumerNode_lt {n k : ℕ} (hk : k ≤ n) (i : Fin (n - k)) :
    k + i.1 < n := by
  -- Rewrite the consumer index bound in the ambient node range.
  have hi : i.1 < n - k := i.2
  omega

/-- Convert a consumer index into the corresponding node index in the full network. -/
private def consumerNode {n k : ℕ} (hk : k ≤ n) (i : Fin (n - k)) : Fin n :=
  ⟨k + i.1, consumerNode_lt hk i⟩

/-- The hydraulic capacity attached to each descending edge is strictly positive. -/
private lemma edgeCapacity_pos {n m : ℕ}
    (tail head : Fin m → Fin n)
    (h : Fin n → ℝ)
    (alpha0 : ℝ)
    (halpha0 : 0 < alpha0)
    (L R : Fin m → ℝ)
    (hL : ∀ j, 0 < L j)
    (hR : ∀ j, 0 < R j)
    (edge_descends : ∀ j, h (tail j) > h (head j)) :
    ∀ j : Fin m,
      0 < alpha0 * (R j)^2 * (h (tail j) - h (head j)) / L j := by
  intro j
  -- Each factor in the capacity formula is positive because the edge descends and all parameters
  -- are physically positive.
  have hdrop : 0 < h (tail j) - h (head j) := sub_pos.mpr (edge_descends j)
  have hsq : 0 < (R j)^2 := sq_pos_of_pos (hR j)
  have hnum : 0 < alpha0 * (R j)^2 * (h (tail j) - h (head j)) := by
    exact mul_pos (mul_pos halpha0 hsq) hdrop
  -- Division by the positive length preserves strict positivity.
  exact div_pos hnum (hL j)

/-- For a positive edge capacity, a valve opening in `[0, 1]` is equivalent to a boxed flow. -/
private lemma exists_valveOpening_iff_nonneg_le_capacity {cap f : ℝ} (hcap : 0 < cap) :
    (∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ f = cap * θ) ↔ 0 ≤ f ∧ f ≤ cap := by
  constructor
  · intro h
    rcases h with ⟨θ, hθ0, hθ1, rfl⟩
    constructor
    · -- A nonnegative valve opening produces nonnegative flow.
      exact mul_nonneg (le_of_lt hcap) hθ0
    · -- The upper valve bound transfers directly to the capacity upper bound.
      have hmul : cap * θ ≤ cap * 1 := by
        exact mul_le_mul_of_nonneg_left hθ1 (le_of_lt hcap)
      simpa using hmul
  · intro h
    rcases h with ⟨hf0, hfle⟩
    refine ⟨f / cap, ?_, ?_, ?_⟩
    · -- Normalizing by a positive capacity preserves nonnegativity.
      exact div_nonneg hf0 (le_of_lt hcap)
    · -- The boxed flow upper bound becomes the valve constraint `θ ≤ 1`.
      simpa using (div_le_one hcap).2 hfle
    · -- Multiplying the normalized valve opening by the capacity recovers the original flow.
      calc
        f = (f / cap) * cap := by
          exact (div_eq_iff (ne_of_gt hcap)).mp rfl
        _ = cap * (f / cap) := by ring

/-- Positive capacities let us eliminate valve openings in favor of box constraints on the flows. -/
private lemma supportable_iff_exists_boxed_flow_supply
    {n m k : ℕ}
    (edgeCapacity : Fin m → ℝ)
    (hedgeCapacity_pos : ∀ j : Fin m, 0 < edgeCapacity j)
    (smax : Fin k → ℝ)
    (supplyEq : (Fin m → ℝ) → (Fin k → ℝ) → Prop)
    (consumerEq : (Fin m → ℝ) → (Fin (n - k) → ℝ) → Prop)
    (c' : Fin (n - k) → ℝ) :
    ((∀ i, 0 ≤ c' i) ∧
      ∃ f : Fin m → ℝ, ∃ s : Fin k → ℝ, ∃ theta : Fin m → ℝ,
        (∀ j, 0 ≤ f j) ∧
        (∀ i, 0 ≤ s i ∧ s i ≤ smax i) ∧
        (∀ j, 0 ≤ theta j ∧ theta j ≤ 1) ∧
        supplyEq f s ∧
        consumerEq f c' ∧
        (∀ j, f j = edgeCapacity j * theta j)) ↔
    ((∀ i, 0 ≤ c' i) ∧
      ∃ f : Fin m → ℝ, ∃ s : Fin k → ℝ,
        (∀ j, 0 ≤ f j ∧ f j ≤ edgeCapacity j) ∧
        (∀ i, 0 ≤ s i ∧ s i ≤ smax i) ∧
        supplyEq f s ∧
        consumerEq f c') := by
  constructor
  · intro h
    rcases h with ⟨hc', f, s, theta, hf, hs, htheta, hsupply, hconsumer, hmul⟩
    refine ⟨hc', f, s, ?_, hs, hsupply, hconsumer⟩
    intro j
    -- The explicit valve witness is equivalent to the corresponding box constraint on `f j`.
    exact (exists_valveOpening_iff_nonneg_le_capacity (hedgeCapacity_pos j)).1
      ⟨theta j, (htheta j).1, (htheta j).2, hmul j⟩
  · intro h
    rcases h with ⟨hc', f, s, hf, hs, hsupply, hconsumer⟩
    refine ⟨hc', f, s, fun j => f j / edgeCapacity j, ?_, hs, ?_, hsupply, hconsumer, ?_⟩
    · -- The boxed-flow form already contains the original nonnegativity requirement on `f`.
      intro j
      exact (hf j).1
    · -- Dividing by the positive capacity recovers a valve opening in the unit interval.
      intro j
      constructor
      · exact div_nonneg (hf j).1 (le_of_lt (hedgeCapacity_pos j))
      · simpa using (div_le_one (hedgeCapacity_pos j)).2 (hf j).2
    · -- Re-expanding the normalized valve opening gives back the prescribed flow.
      intro j
      calc
        f j = (f j / edgeCapacity j) * edgeCapacity j := by
          exact (div_eq_iff (ne_of_gt (hedgeCapacity_pos j))).mp rfl
        _ = edgeCapacity j * (f j / edgeCapacity j) := by ring

/-- Slack variables for the boxed edge and supply upper bounds. -/
private abbrev SupportSlackVar (m k : ℕ) :=
  Fin m ⊕ (Fin k ⊕ (Fin m ⊕ Fin k))

/-- Rows of the affine system encoding supply balance, consumer balance, and both box constraints. -/
private abbrev SupportSlackEq (n m k : ℕ) :=
  Fin k ⊕ (Fin (n - k) ⊕ (Fin m ⊕ Fin k))

/-- Bundle flows, supplies, and their upper-bound slacks into one nonnegative vector. -/
private def supportSlackVector {m k : ℕ}
    (f : Fin m → ℝ) (s : Fin k → ℝ) (uf : Fin m → ℝ) (us : Fin k → ℝ) :
    SupportSlackVar m k → ℝ
  | Sum.inl j => f j
  | Sum.inr (Sum.inl i) => s i
  | Sum.inr (Sum.inr (Sum.inl j)) => uf j
  | Sum.inr (Sum.inr (Sum.inr i)) => us i

/-- The fixed coefficient matrix for the boxed supportability system. -/
private def supportSlackMatrix {n m k : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (hk : k ≤ n) :
    Matrix (SupportSlackEq n m k) (SupportSlackVar m k) ℝ :=
  fun row col =>
    match row, col with
    | Sum.inl i, Sum.inl j =>
        A ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ j
    | Sum.inl i, Sum.inr (Sum.inl i') =>
        if i = i' then 1 else 0
    | Sum.inl _, _ => 0
    | Sum.inr (Sum.inl i), Sum.inl j =>
        A (consumerNode hk i) j
    | Sum.inr (Sum.inl _), _ => 0
    | Sum.inr (Sum.inr (Sum.inl j)), Sum.inl j' =>
        if j = j' then 1 else 0
    | Sum.inr (Sum.inr (Sum.inl j)), Sum.inr (Sum.inr (Sum.inl j')) =>
        if j = j' then 1 else 0
    | Sum.inr (Sum.inr (Sum.inr i)), Sum.inr (Sum.inl i') =>
        if i = i' then 1 else 0
    | Sum.inr (Sum.inr (Sum.inr i)), Sum.inr (Sum.inr (Sum.inr i')) =>
        if i = i' then 1 else 0
    | _, _ => 0

/-- The constant right-hand side for the slack-variable formulation. -/
private def supportSlackRhs {n m k : ℕ}
    (edgeCapacity : Fin m → ℝ) (smax : Fin k → ℝ) :
    SupportSlackEq n m k → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl j)) => edgeCapacity j
  | Sum.inr (Sum.inr (Sum.inr i)) => smax i

/-- The consumer demand enters only in the consumer-balance rows of the slack system. -/
private def supportSlackConsumerMatrix {n m k : ℕ} :
    Matrix (SupportSlackEq n m k) (Fin (n - k)) ℝ :=
  fun row col =>
    match row with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl i) => if i = col then 1 else 0
    | Sum.inr (Sum.inr _) => 0

/-- The boxed flow-supply feasibility problem is equivalent to one nonnegative affine system with
slack variables for the upper bounds. -/
private lemma boxed_supportable_iff_exists_nonnegative_slack_rhs
    {n m k : ℕ}
    (hk : k ≤ n)
    (A : Matrix (Fin n) (Fin m) ℝ)
    (edgeCapacity : Fin m → ℝ)
    (smax : Fin k → ℝ)
    (c' : Fin (n - k) → ℝ) :
    ((∀ i, 0 ≤ c' i) ∧
      ∃ f : Fin m → ℝ, ∃ s : Fin k → ℝ,
        (∀ j, 0 ≤ f j ∧ f j ≤ edgeCapacity j) ∧
        (∀ i, 0 ≤ s i ∧ s i ≤ smax i) ∧
        (∀ i : Fin k,
          ∑ j : Fin m, A ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ j * f j = -s i) ∧
        (∀ i : Fin (n - k),
          ∑ j : Fin m, A (consumerNode hk i) j * f j = c' i)) ↔
    ((∀ i, 0 ≤ c' i) ∧
      ∃ x : SupportSlackVar m k → ℝ,
        (∀ a, 0 ≤ x a) ∧
        ((supportSlackMatrix A hk).mulVec x =
          supportSlackRhs (n := n) edgeCapacity smax +
            (supportSlackConsumerMatrix (n := n) (m := m) (k := k)).mulVec c')) := by
  constructor
  · intro h
    rcases h with ⟨hc', f, s, hf, hs, hsupply, hconsumer⟩
    let uf : Fin m → ℝ := fun j => edgeCapacity j - f j
    let us : Fin k → ℝ := fun i => smax i - s i
    refine ⟨hc', supportSlackVector f s uf us, ?_, ?_⟩
    · intro a
      -- Each coordinate of the bundled vector is one of the original nonnegative variables or an
      -- upper-bound slack.
      cases a with
      | inl j =>
          exact (hf j).1
      | inr a =>
          cases a with
          | inl i =>
              exact (hs i).1
          | inr a =>
              cases a with
              | inl j =>
                  exact sub_nonneg.mpr (hf j).2
              | inr i =>
                  exact sub_nonneg.mpr (hs i).2
    · ext row
      -- Each block row reproduces one original equation or one slack identity.
      cases row with
      | inl i =>
          have hsum :
              (∑ j : Fin m, A ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ j * f j) + s i = 0 := by
            linarith [hsupply i]
          simpa [supportSlackMatrix, supportSlackVector, supportSlackRhs,
            supportSlackConsumerMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
            using hsum
      | inr row =>
          cases row with
          | inl i =>
              simpa [supportSlackMatrix, supportSlackVector, supportSlackRhs,
                supportSlackConsumerMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
                consumerNode] using hconsumer i
          | inr row =>
              cases row with
              | inl j =>
                  have hsum : f j + uf j = edgeCapacity j := by
                    simp [uf]
                  simpa [supportSlackMatrix, supportSlackVector, supportSlackRhs,
                    supportSlackConsumerMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
                    using hsum
              | inr i =>
                  have hsum : s i + us i = smax i := by
                    simp [us]
                  simpa [supportSlackMatrix, supportSlackVector, supportSlackRhs,
                    supportSlackConsumerMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
                    using hsum
  · intro h
    rcases h with ⟨hc', x, hxnonneg, hxeq⟩
    let f : Fin m → ℝ := fun j => x (Sum.inl j)
    let s : Fin k → ℝ := fun i => x (Sum.inr (Sum.inl i))
    let uf : Fin m → ℝ := fun j => x (Sum.inr (Sum.inr (Sum.inl j)))
    let us : Fin k → ℝ := fun i => x (Sum.inr (Sum.inr (Sum.inr i)))
    refine ⟨hc', f, s, ?_, ?_, ?_, ?_⟩
    · intro j
      have hrow := congrArg (fun v => v (Sum.inr (Sum.inr (Sum.inl j)))) hxeq
      -- The flow-upper-bound row reads `f j + uf j = edgeCapacity j`.
      have hsum :
          f j + uf j = edgeCapacity j := by
        simpa [f, uf, supportSlackMatrix, supportSlackRhs, supportSlackConsumerMatrix,
          Matrix.mulVec, dotProduct, Fintype.sum_sum_type, add_assoc, add_left_comm, add_comm]
          using hrow
      constructor
      · exact hxnonneg _
      · linarith [hxnonneg (Sum.inr (Sum.inr (Sum.inl j))), hsum]
    · intro i
      have hrow := congrArg (fun v => v (Sum.inr (Sum.inr (Sum.inr i)))) hxeq
      -- The supply-upper-bound row reads `s i + us i = smax i`.
      have hsum :
          s i + us i = smax i := by
        simpa [s, us, supportSlackMatrix, supportSlackRhs, supportSlackConsumerMatrix,
          Matrix.mulVec, dotProduct, Fintype.sum_sum_type, add_assoc, add_left_comm, add_comm]
          using hrow
      constructor
      · exact hxnonneg _
      · linarith [hxnonneg (Sum.inr (Sum.inr (Sum.inr i))), hsum]
    · intro i
      have hrow := congrArg (fun v => v (Sum.inl i)) hxeq
      -- The supply-balance rows keep the original conservation equations.
      have hsum :
          (∑ j : Fin m, A ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ j * f j) + s i = 0 := by
        simpa [f, s, supportSlackMatrix, supportSlackRhs, supportSlackConsumerMatrix,
          Matrix.mulVec, dotProduct, Fintype.sum_sum_type, add_assoc, add_left_comm, add_comm]
          using hrow
      linarith
    · intro i
      have hrow := congrArg (fun v => v (Sum.inr (Sum.inl i))) hxeq
      -- The consumer-balance rows recover the prescribed consumer demand.
      simpa [f, supportSlackMatrix, supportSlackRhs, supportSlackConsumerMatrix, Matrix.mulVec,
        dotProduct, Fintype.sum_sum_type, add_assoc, add_left_comm, add_comm, consumerNode]
        using hrow

/-- The slack formulation of supportability is equivalent to finitely many affine inequalities in
the consumption vector alone. -/
private lemma coordinatewise_nonneg_iff_standard_inequalities
    {d : ℕ} (c : Fin d → ℝ) :
    (∀ i, 0 ≤ c i) ↔
      ∀ i : Fin d, ∑ j : Fin d, (if i = j then (-1 : ℝ) else 0) * c j ≤ 0 := by
  constructor
  · intro hc i
    -- Each standard row keeps only `-c i`, so the inequality is exactly `0 ≤ c i`.
    have hsum : ∑ j : Fin d, (if i = j then (-1 : ℝ) else 0) * c j = -c i := by
      classical
      simp
    rw [hsum]
    linarith [hc i]
  · intro hc i
    -- Reading the `i`-th row back gives `-c i ≤ 0`, hence `c i ≥ 0`.
    have hrow := hc i
    have hsum : ∑ j : Fin d, (if i = j then (-1 : ℝ) else 0) * c j = -c i := by
      classical
      simp
    rw [hsum] at hrow
    linarith

/-- Duplicate each matrix row with both signs. -/
private def signedRowMatrix {rowIdx colIdx : Type*}
    (A : Matrix rowIdx colIdx ℝ) :
    Matrix (rowIdx ⊕ rowIdx) colIdx ℝ
  | Sum.inl i, j => A i j
  | Sum.inr i, j => -A i j

/-- Duplicate each right-hand-side row with both signs. -/
private def signedRowVector {rowIdx : Type*} (r : rowIdx → ℝ) : rowIdx ⊕ rowIdx → ℝ
  | Sum.inl i => r i
  | Sum.inr i => -r i

/-- An affine equality system is equivalent to the doubled inequality system obtained by taking
both row signs. -/
private lemma affine_equality_system_iff_signed_affine_inequalities
    {eqIdx varIdx paramIdx : Type*}
    [Fintype eqIdx] [Fintype varIdx] [Fintype paramIdx]
    [DecidableEq eqIdx] [DecidableEq varIdx] [DecidableEq paramIdx]
    (B : Matrix eqIdx varIdx ℝ) (r : eqIdx → ℝ) (C : Matrix eqIdx paramIdx ℝ)
    (y : paramIdx → ℝ) :
    (∃ x : varIdx → ℝ, (∀ a, 0 ≤ x a) ∧ B.mulVec x = r + C.mulVec y) ↔
      ∃ x : varIdx → ℝ,
        (∀ a, 0 ≤ x a) ∧
        ∀ i : eqIdx ⊕ eqIdx,
          ((signedRowMatrix B).mulVec x) i ≤
            signedRowVector r i + ((signedRowMatrix C).mulVec y) i := by
  constructor
  · rintro ⟨x, hxnonneg, hEq⟩
    refine ⟨x, hxnonneg, ?_⟩
    intro i
    -- Read each equality row as two inequalities with opposite signs.
    cases i with
    | inl i =>
        have hi : (B.mulVec x) i = r i + (C.mulVec y) i := by
          simpa using congrArg (fun v => v i) hEq
        have hsigned :
            ((signedRowMatrix B).mulVec x) (Sum.inl i) =
              signedRowVector r (Sum.inl i) + ((signedRowMatrix C).mulVec y) (Sum.inl i) := by
          simpa [signedRowMatrix, signedRowVector, Matrix.mulVec, dotProduct] using hi
        exact le_of_eq hsigned
    | inr i =>
        have hi : (B.mulVec x) i = r i + (C.mulVec y) i := by
          simpa using congrArg (fun v => v i) hEq
        have hneg : -((B.mulVec x) i) = -r i + -((C.mulVec y) i) := by
          linarith
        have hsigned :
            ((signedRowMatrix B).mulVec x) (Sum.inr i) =
              signedRowVector r (Sum.inr i) + ((signedRowMatrix C).mulVec y) (Sum.inr i) := by
          simpa [signedRowMatrix, signedRowVector, Matrix.mulVec, dotProduct] using hneg
        exact le_of_eq hsigned
  · rintro ⟨x, hxnonneg, hxineq⟩
    refine ⟨x, hxnonneg, ?_⟩
    ext i
    -- The positive and negative copies force both inequalities, hence equality.
    have hpos : (B.mulVec x) i ≤ r i + (C.mulVec y) i := by
      simpa [signedRowMatrix, signedRowVector, Matrix.mulVec, dotProduct] using hxineq (Sum.inl i)
    have hneg : -((B.mulVec x) i) ≤ -r i + -((C.mulVec y) i) := by
      simpa [signedRowMatrix, signedRowVector, Matrix.mulVec, dotProduct] using hxineq (Sum.inr i)
    have hge : r i + (C.mulVec y) i ≤ (B.mulVec x) i := by
      linarith
    exact le_antisymm hpos hge

/-- If there are no existential variables, the affine inequalities already depend only on the
parameter vector. -/
private lemma
    exists_nonnegative_affine_inequality_solution_iff_projected_inequalities_of_isEmpty
    {rowIdx varIdx paramIdx : Type*}
    [Fintype rowIdx] [Fintype varIdx] [Fintype paramIdx]
    [DecidableEq rowIdx] [DecidableEq varIdx] [DecidableEq paramIdx]
    (hvar : IsEmpty varIdx)
    (A : Matrix rowIdx varIdx ℝ) (r : rowIdx → ℝ) (C : Matrix rowIdx paramIdx ℝ) :
    ∃ p : ℕ, ∃ M : Matrix (Fin p) paramIdx ℝ, ∃ b : Fin p → ℝ,
      ∀ y : paramIdx → ℝ,
        (∃ x : varIdx → ℝ, (∀ a, 0 ≤ x a) ∧
          ∀ i : rowIdx, (A.mulVec x) i ≤ r i + (C.mulVec y) i) ↔
          ∀ i : Fin p, ∑ j : paramIdx, M i j * y j ≤ b i := by
  classical
  letI : IsEmpty varIdx := hvar
  let rowEquiv : rowIdx ≃ Fin (Fintype.card rowIdx) := Fintype.equivFin rowIdx
  let M : Matrix (Fin (Fintype.card rowIdx)) paramIdx ℝ :=
    fun i j => -C (rowEquiv.symm i) j
  let b : Fin (Fintype.card rowIdx) → ℝ := fun i => r (rowEquiv.symm i)
  refine ⟨Fintype.card rowIdx, M, b, ?_⟩
  intro y
  constructor
  · rintro ⟨x, -, hxineq⟩ i
    -- With no existential coordinates, each inequality is already one projected row.
    have hxrow : (A.mulVec x) (rowEquiv.symm i) ≤
        r (rowEquiv.symm i) + (C.mulVec y) (rowEquiv.symm i) := hxineq (rowEquiv.symm i)
    have hAx : (A.mulVec x) (rowEquiv.symm i) = 0 := by
      simp [Matrix.mulVec, dotProduct]
    have hCy : -((C.mulVec y) (rowEquiv.symm i)) ≤ r (rowEquiv.symm i) := by
      linarith
    simpa [M, b, Matrix.mulVec, dotProduct] using hCy
  · intro hy
    let x : varIdx → ℝ := fun a => False.elim (hvar.false a)
    refine ⟨x, ?_, ?_⟩
    · intro a
      exact False.elim (hvar.false a)
    · intro i
      -- Re-expanding the projected row recovers the original inequality because `A.mulVec x = 0`.
      have hrow : ∑ j : paramIdx, M (rowEquiv i) j * y j ≤ b (rowEquiv i) := hy (rowEquiv i)
      have hCy : -((C.mulVec y) i) ≤ r i := by
        simpa [M, b, rowEquiv, Matrix.mulVec, dotProduct] using hrow
      have hAx : (A.mulVec x) i = 0 := by
        simp [x, Matrix.mulVec, dotProduct]
      linarith

/-- The rows created by eliminating the head variable in one Fourier-Motzkin step. -/
private abbrev fourierMotzkinStepRow {rowIdx : Type*} {n : ℕ}
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) :=
  {i : rowIdx // A i 0 = 0} ⊕
    ((Unit ⊕ {i : rowIdx // A i 0 < 0}) × {j : rowIdx // 0 < A j 0})

/-- Splitting a vector into head and tail separates one row into the eliminated variable plus the
remaining tail dot product. -/
private lemma mulVec_vecCons_eq_head_add_tail
    {rowIdx : Type*} {n : ℕ}
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) (t : ℝ) (z : Fin n → ℝ) (i : rowIdx) :
    (A.mulVec (Matrix.vecCons t z)) i =
      A i 0 * t + ((A.submatrix id Fin.succ).mulVec z) i := by
  -- Split the head coordinate off using the standard `Fin` dot-product decomposition.
  simpa [Matrix.mulVec, dotProduct] using
    (Matrix.dotProduct_cons (v := A i) (x := t) (w := z))

/-- The coefficient matrix produced by one Fourier-Motzkin elimination step. -/
private def fourierMotzkinStepMatrix
    {rowIdx : Type*} {n : ℕ}
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) :
    Matrix (fourierMotzkinStepRow A) (Fin n) ℝ :=
  let Atail := A.submatrix id Fin.succ
  fun row col =>
    match row with
    | Sum.inl i => Atail i.1 col
    | Sum.inr (Sum.inl _, j) => Atail j.1 col
    | Sum.inr (Sum.inr i, j) => A j.1 0 * Atail i.1 col - A i.1 0 * Atail j.1 col

/-- The right-hand side produced by one Fourier-Motzkin elimination step. -/
private def fourierMotzkinStepRhs
    {rowIdx : Type*} {n : ℕ}
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) (r : rowIdx → ℝ) :
    fourierMotzkinStepRow A → ℝ
  | Sum.inl i => r i.1
  | Sum.inr (Sum.inl _, j) => r j.1
  | Sum.inr (Sum.inr i, j) => A j.1 0 * r i.1 - A i.1 0 * r j.1

/-- The parameter matrix produced by one Fourier-Motzkin elimination step. -/
private def fourierMotzkinStepParamMatrix
    {rowIdx paramIdx : Type*} {n : ℕ}
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) (C : Matrix rowIdx paramIdx ℝ) :
    Matrix (fourierMotzkinStepRow A) paramIdx ℝ
  | Sum.inl i, j => C i.1 j
  | Sum.inr (Sum.inl _, i), j => C i.1 j
  | Sum.inr (Sum.inr i, j'), j => A j'.1 0 * C i.1 j - A i.1 0 * C j'.1 j

/-- Zero-head rows are copied unchanged by the FM elimination matrix. -/
@[simp] private lemma fourierMotzkinStepMatrix_mulVec_zero
    {rowIdx : Type*} {n : ℕ}
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) (z : Fin n → ℝ)
    (i : {i : rowIdx // A i 0 = 0}) :
    (fourierMotzkinStepMatrix A).mulVec z (Sum.inl i) =
      ((A.submatrix id Fin.succ).mulVec z) i.1 := by
  -- Expanding the copied row recovers the original tail dot product exactly.
  simp [fourierMotzkinStepMatrix, Matrix.mulVec, dotProduct]

/-- The extra unit-lower rows reduce to the upper row itself after eliminating the head variable. -/
@[simp] private lemma fourierMotzkinStepMatrix_mulVec_unit
    {rowIdx : Type*} {n : ℕ}
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) (z : Fin n → ℝ)
    (j : {j : rowIdx // 0 < A j 0}) :
    (fourierMotzkinStepMatrix A).mulVec z (Sum.inr (Sum.inl (), j)) =
      ((A.submatrix id Fin.succ).mulVec z) j.1 := by
  -- The unit lower bound contributes zero tail coefficients.
  simp [fourierMotzkinStepMatrix, Matrix.mulVec, dotProduct]

/-- Pair rows evaluate to the standard linear combination of the lower and upper tail rows. -/
@[simp] private lemma fourierMotzkinStepMatrix_mulVec_pair
    {rowIdx : Type*} {n : ℕ}
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) (z : Fin n → ℝ)
    (i : {i : rowIdx // A i 0 < 0}) (j : {j : rowIdx // 0 < A j 0}) :
    (fourierMotzkinStepMatrix A).mulVec z (Sum.inr (Sum.inr i, j)) =
      A j.1 0 * ((A.submatrix id Fin.succ).mulVec z) i.1 -
        A i.1 0 * ((A.submatrix id Fin.succ).mulVec z) j.1 := by
  -- Distribute the row combination through the finite sum defining `mulVec`.
  let Atail := A.submatrix id Fin.succ
  calc
    (fourierMotzkinStepMatrix A).mulVec z (Sum.inr (Sum.inr i, j))
        = ∑ l : Fin n, (A j.1 0 * Atail i.1 l - A i.1 0 * Atail j.1 l) * z l := by
            rfl
    _ = ∑ l : Fin n, (A j.1 0 * (Atail i.1 l * z l) - A i.1 0 * (Atail j.1 l * z l)) := by
          refine Finset.sum_congr rfl ?_
          intro l _
          ring
    _ = A j.1 0 * ∑ l : Fin n, Atail i.1 l * z l - A i.1 0 * ∑ l : Fin n, Atail j.1 l * z l := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = A j.1 0 * (Atail.mulVec z) i.1 - A i.1 0 * (Atail.mulVec z) j.1 := by
          rfl

/-- Zero-head rows preserve the original parameter contribution. -/
@[simp] private lemma fourierMotzkinStepParamMatrix_mulVec_zero
    {rowIdx paramIdx : Type*} {n : ℕ}
    [Fintype paramIdx]
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) (C : Matrix rowIdx paramIdx ℝ) (y : paramIdx → ℝ)
    (i : {i : rowIdx // A i 0 = 0}) :
    (fourierMotzkinStepParamMatrix A C).mulVec y (Sum.inl i) = (C.mulVec y) i.1 := by
  -- The copied parameter row is unchanged.
  simp [fourierMotzkinStepParamMatrix, Matrix.mulVec, dotProduct]

/-- The unit-lower rows keep the upper row's parameter contribution. -/
@[simp] private lemma fourierMotzkinStepParamMatrix_mulVec_unit
    {rowIdx paramIdx : Type*} {n : ℕ}
    [Fintype paramIdx]
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) (C : Matrix rowIdx paramIdx ℝ) (y : paramIdx → ℝ)
    (j : {j : rowIdx // 0 < A j 0}) :
    (fourierMotzkinStepParamMatrix A C).mulVec y (Sum.inr (Sum.inl (), j)) =
      (C.mulVec y) j.1 := by
  -- The extra lower bound has no parameter dependence.
  simp [fourierMotzkinStepParamMatrix, Matrix.mulVec, dotProduct]

/-- Pair rows carry the same linear combination of parameter rows as they do of inequality rows. -/
@[simp] private lemma fourierMotzkinStepParamMatrix_mulVec_pair
    {rowIdx paramIdx : Type*} {n : ℕ}
    [Fintype paramIdx]
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) (C : Matrix rowIdx paramIdx ℝ) (y : paramIdx → ℝ)
    (i : {i : rowIdx // A i 0 < 0}) (j : {j : rowIdx // 0 < A j 0}) :
    (fourierMotzkinStepParamMatrix A C).mulVec y (Sum.inr (Sum.inr i, j)) =
      A j.1 0 * (C.mulVec y) i.1 - A i.1 0 * (C.mulVec y) j.1 := by
  -- Distribute the same row combination through the parameter dot product.
  calc
    (fourierMotzkinStepParamMatrix A C).mulVec y (Sum.inr (Sum.inr i, j))
        = ∑ l, (A j.1 0 * C i.1 l - A i.1 0 * C j.1 l) * y l := by
            rfl
    _ = ∑ l, (A j.1 0 * (C i.1 l * y l) - A i.1 0 * (C j.1 l * y l)) := by
          refine Finset.sum_congr rfl ?_
          intro l _
          ring
    _ = A j.1 0 * ∑ l, C i.1 l * y l - A i.1 0 * ∑ l, C j.1 l * y l := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = A j.1 0 * (C.mulVec y) i.1 - A i.1 0 * (C.mulVec y) j.1 := by
          rfl

/-- One explicit Fourier-Motzkin step eliminates the head nonnegative variable. -/
private lemma exists_nonnegative_head_iff_fourierMotzkin_step
    {rowIdx paramIdx : Type*} {n : ℕ}
    [Fintype rowIdx] [Fintype paramIdx]
    [DecidableEq rowIdx] [DecidableEq paramIdx]
    (A : Matrix rowIdx (Fin (n + 1)) ℝ) (r : rowIdx → ℝ) (C : Matrix rowIdx paramIdx ℝ) :
    ∃ A_FM : Matrix (fourierMotzkinStepRow A) (Fin n) ℝ,
      ∃ r_FM : fourierMotzkinStepRow A → ℝ,
        ∃ C_FM : Matrix (fourierMotzkinStepRow A) paramIdx ℝ,
          ∀ y : paramIdx → ℝ,
            (∃ x : Fin (n + 1) → ℝ, (∀ a, 0 ≤ x a) ∧
              ∀ i : rowIdx, (A.mulVec x) i ≤ r i + (C.mulVec y) i) ↔
            (∃ z : Fin n → ℝ, (∀ a, 0 ≤ z a) ∧
              ∀ k : fourierMotzkinStepRow A,
                (A_FM.mulVec z) k ≤ r_FM k + (C_FM.mulVec y) k) := by
  classical
  let Atail : Matrix rowIdx (Fin n) ℝ := A.submatrix id Fin.succ
  let A_FM : Matrix (fourierMotzkinStepRow A) (Fin n) ℝ := fourierMotzkinStepMatrix A
  let r_FM : fourierMotzkinStepRow A → ℝ := fourierMotzkinStepRhs A r
  let C_FM : Matrix (fourierMotzkinStepRow A) paramIdx ℝ := fourierMotzkinStepParamMatrix A C
  refine ⟨A_FM, r_FM, C_FM, ?_⟩
  intro y
  constructor
  · rintro ⟨x, hxnonneg, hxineq⟩
    refine ⟨Matrix.vecTail x, ?_, ?_⟩
    · -- Every tail coordinate inherits nonnegativity from the original witness.
      intro a
      simpa [Matrix.vecTail] using hxnonneg a.succ
    · intro k
      have hhead_nonneg : 0 ≤ Matrix.vecHead x := by
        simpa [Matrix.vecHead] using hxnonneg 0
      cases k with
      | inl i =>
          -- Zero-head rows survive unchanged once the eliminated coefficient vanishes.
          have hrow0 :
              (A.mulVec (Matrix.vecCons (Matrix.vecHead x) (Matrix.vecTail x))) i.1 ≤
                r i.1 + (C.mulVec y) i.1 := by
            simpa [Matrix.cons_head_tail] using hxineq i.1
          have hmul :
              (A.mulVec (Matrix.vecCons (Matrix.vecHead x) (Matrix.vecTail x))) i.1 =
                A i.1 0 * Matrix.vecHead x + (Atail.mulVec (Matrix.vecTail x)) i.1 := by
            simpa [Atail] using
              (mulVec_vecCons_eq_head_add_tail (A := A)
                (t := Matrix.vecHead x) (z := Matrix.vecTail x) (i := i.1))
          have hrow :
              A i.1 0 * Matrix.vecHead x + (Atail.mulVec (Matrix.vecTail x)) i.1 ≤
                r i.1 + (C.mulVec y) i.1 := by
            exact hmul ▸ hrow0
          simpa [A_FM, r_FM, C_FM, Atail, i.2] using hrow
      | inr k =>
          cases k with
          | mk lower j =>
              have hrowj0 :
                  (A.mulVec (Matrix.vecCons (Matrix.vecHead x) (Matrix.vecTail x))) j.1 ≤
                    r j.1 + (C.mulVec y) j.1 := by
                simpa [Matrix.cons_head_tail] using hxineq j.1
              have hmulj :
                  (A.mulVec (Matrix.vecCons (Matrix.vecHead x) (Matrix.vecTail x))) j.1 =
                    A j.1 0 * Matrix.vecHead x + (Atail.mulVec (Matrix.vecTail x)) j.1 := by
                simpa [Atail] using
                  (mulVec_vecCons_eq_head_add_tail (A := A)
                    (t := Matrix.vecHead x) (z := Matrix.vecTail x) (i := j.1))
              have hrowj :
                  A j.1 0 * Matrix.vecHead x + (Atail.mulVec (Matrix.vecTail x)) j.1 ≤
                    r j.1 + (C.mulVec y) j.1 := by
                exact hmulj ▸ hrowj0
              cases lower with
              | inl _ =>
                  -- Pairing the extra lower bound `0 ≤ t` with an upper row removes the head term.
                  have hhead_term_nonneg : 0 ≤ A j.1 0 * Matrix.vecHead x := by
                    exact mul_nonneg (le_of_lt j.2) hhead_nonneg
                  have hunit :
                      (Atail.mulVec (Matrix.vecTail x)) j.1 ≤
                        r j.1 + (C.mulVec y) j.1 := by
                    linarith
                      [hrowj, hhead_term_nonneg]
                  simpa [A_FM, r_FM, C_FM, Atail] using hunit
              | inr i =>
                  -- The standard lower/upper row combination cancels the eliminated variable.
                  have hrowi0 :
                      (A.mulVec (Matrix.vecCons (Matrix.vecHead x) (Matrix.vecTail x))) i.1 ≤
                        r i.1 + (C.mulVec y) i.1 := by
                    simpa [Matrix.cons_head_tail] using hxineq i.1
                  have hmuli :
                      (A.mulVec (Matrix.vecCons (Matrix.vecHead x) (Matrix.vecTail x))) i.1 =
                        A i.1 0 * Matrix.vecHead x + (Atail.mulVec (Matrix.vecTail x)) i.1 := by
                    simpa [Atail] using
                      (mulVec_vecCons_eq_head_add_tail (A := A)
                        (t := Matrix.vecHead x) (z := Matrix.vecTail x) (i := i.1))
                  have hrowi :
                      A i.1 0 * Matrix.vecHead x + (Atail.mulVec (Matrix.vecTail x)) i.1 ≤
                        r i.1 + (C.mulVec y) i.1 := by
                    exact hmuli ▸ hrowi0
                  have hiScale :
                      A j.1 0 * (A i.1 0 * Matrix.vecHead x + (Atail.mulVec (Matrix.vecTail x)) i.1) ≤
                        A j.1 0 * (r i.1 + (C.mulVec y) i.1) := by
                    exact mul_le_mul_of_nonneg_left hrowi (le_of_lt j.2)
                  have hjScale :
                      (-A i.1 0) * (A j.1 0 * Matrix.vecHead x + (Atail.mulVec (Matrix.vecTail x)) j.1) ≤
                        (-A i.1 0) * (r j.1 + (C.mulVec y) j.1) := by
                    exact mul_le_mul_of_nonneg_left hrowj (le_of_lt (neg_pos.mpr i.2))
                  have hpair :
                      A j.1 0 * (Atail.mulVec (Matrix.vecTail x)) i.1 -
                          A i.1 0 * (Atail.mulVec (Matrix.vecTail x)) j.1 ≤
                        A j.1 0 * (r i.1 + (C.mulVec y) i.1) -
                          A i.1 0 * (r j.1 + (C.mulVec y) j.1) := by
                    nlinarith
                      [hiScale, hjScale]
                  have hpairRow :
                      (A_FM.mulVec (Matrix.vecTail x)) (Sum.inr (Sum.inr i, j)) ≤
                        r_FM (Sum.inr (Sum.inr i, j)) +
                          (C_FM.mulVec y) (Sum.inr (Sum.inr i, j)) := by
                    rw [show A_FM = fourierMotzkinStepMatrix A by rfl,
                      show r_FM = fourierMotzkinStepRhs A r by rfl,
                      show C_FM = fourierMotzkinStepParamMatrix A C by rfl,
                      fourierMotzkinStepMatrix_mulVec_pair,
                      fourierMotzkinStepParamMatrix_mulVec_pair]
                    have hrhs :
                        A j.1 0 * (r i.1 + (C.mulVec y) i.1) -
                            A i.1 0 * (r j.1 + (C.mulVec y) j.1) =
                          fourierMotzkinStepRhs A r (Sum.inr (Sum.inr i, j)) +
                            (A j.1 0 * (C.mulVec y) i.1 - A i.1 0 * (C.mulVec y) j.1) := by
                      simp [fourierMotzkinStepRhs]
                      ring_nf
                    exact hrhs ▸ hpair
                  exact hpairRow
  · rintro ⟨z, hznonneg, hzineq⟩
    let lowerBound : Unit ⊕ {i : rowIdx // A i 0 < 0} → ℝ
      | Sum.inl _ => 0
      | Sum.inr i =>
          (((Atail.mulVec z) i.1) - (r i.1 + (C.mulVec y) i.1)) / (-A i.1 0)
    let t : ℝ := Finset.sup' Finset.univ (by simp) lowerBound
    refine ⟨Matrix.vecCons t z, ?_, ?_⟩
    · -- The inserted head coordinate is the supremum of a family containing `0`.
      intro a
      refine Fin.cases ?_ ?_ a
      · have hzero : lowerBound (Sum.inl ()) ≤ t := by
          exact Finset.le_sup' (s := (Finset.univ : Finset (Unit ⊕ {i : rowIdx // A i 0 < 0})))
            (f := lowerBound) (b := Sum.inl ()) (by simp)
        simpa [t, lowerBound] using hzero
      · intro i
        exact hznonneg i
    · intro i
      by_cases hzero : A i 0 = 0
      · -- Zero-head rows are exactly among the preserved FM rows.
        let i0 : {i : rowIdx // A i 0 = 0} := ⟨i, hzero⟩
        have hrow : (A_FM.mulVec z) (Sum.inl i0) ≤ r_FM (Sum.inl i0) + (C_FM.mulVec y) (Sum.inl i0) :=
          hzineq (Sum.inl i0)
        simpa [A_FM, r_FM, C_FM, Atail, hzero, mulVec_vecCons_eq_head_add_tail] using hrow
      · by_cases hpos : 0 < A i 0
        · -- For an upper row, bound the chosen head coordinate by every upper bound.
          let iu : {j : rowIdx // 0 < A j 0} := ⟨i, hpos⟩
          have ht_le :
              t ≤ ((r i + (C.mulVec y) i) - (Atail.mulVec z) i) / (A i 0) := by
            let s : Finset (Unit ⊕ {i : rowIdx // A i 0 < 0}) := Finset.univ
            have hs : s.Nonempty := by
              simp [s]
            change s.sup' hs lowerBound ≤
              ((r i + (C.mulVec y) i) - (Atail.mulVec z) i) / (A i 0)
            exact (Finset.sup'_le_iff (s := s) (H := hs)
              (f := lowerBound)
              (a := ((r i + (C.mulVec y) i) - (Atail.mulVec z) i) / (A i 0))).2 (by
            intro l hl
            cases l with
            | inl _ =>
                have hunit :
                    (A_FM.mulVec z) (Sum.inr (Sum.inl (), iu)) ≤
                      r_FM (Sum.inr (Sum.inl (), iu)) +
                        (C_FM.mulVec y) (Sum.inr (Sum.inl (), iu)) :=
                  hzineq (Sum.inr (Sum.inl (), iu))
                have hnum :
                    0 ≤ (r i + (C.mulVec y) i) - (Atail.mulVec z) i := by
                  simpa [A_FM, r_FM, C_FM, Atail, sub_eq_add_neg] using hunit
                have hunit_le :
                    lowerBound (Sum.inl ()) ≤
                      ((r i + (C.mulVec y) i) - (Atail.mulVec z) i) / (A i 0) := by
                  have hupper_nonneg :
                      0 ≤ ((r i + (C.mulVec y) i) - (Atail.mulVec z) i) / (A i 0) := by
                    exact div_nonneg hnum (le_of_lt hpos)
                  simpa [lowerBound] using hupper_nonneg
                exact hunit_le
            | inr ilow =>
                have hiNeg : A ilow.1 0 < 0 := ilow.2
                have hpair :
                    (A_FM.mulVec z) (Sum.inr (Sum.inr ilow, iu)) ≤
                      r_FM (Sum.inr (Sum.inr ilow, iu)) +
                        (C_FM.mulVec y) (Sum.inr (Sum.inr ilow, iu)) :=
                  hzineq (Sum.inr (Sum.inr ilow, iu))
                have hiPos : 0 < -A ilow.1 0 := by
                  linarith
                have hpairClean :
                    A i 0 * (Atail.mulVec z) ilow.1 - A ilow.1 0 * (Atail.mulVec z) i ≤
                      A i 0 * (r ilow.1 + (C.mulVec y) ilow.1) -
                        A ilow.1 0 * (r i + (C.mulVec y) i) := by
                  have hpairRaw := hpair
                  rw [show A_FM = fourierMotzkinStepMatrix A by rfl,
                    show r_FM = fourierMotzkinStepRhs A r by rfl,
                    show C_FM = fourierMotzkinStepParamMatrix A C by rfl,
                    fourierMotzkinStepMatrix_mulVec_pair,
                    fourierMotzkinStepParamMatrix_mulVec_pair] at hpairRaw
                  have hrhs :
                      fourierMotzkinStepRhs A r (Sum.inr (Sum.inr ilow, iu)) +
                          (A iu.1 0 * (C.mulVec y) ilow.1 - A ilow.1 0 * (C.mulVec y) iu.1) =
                        A i 0 * (r ilow.1 + (C.mulVec y) ilow.1) -
                          A ilow.1 0 * (r i + (C.mulVec y) i) := by
                    simp [iu, fourierMotzkinStepRhs]
                    ring
                  exact hrhs ▸ hpairRaw
                have hcross :
                    A i 0 *
                        (((Atail.mulVec z) ilow.1) - (r ilow.1 + (C.mulVec y) ilow.1)) ≤
                      (-A ilow.1 0) * (((r i + (C.mulVec y) i) - (Atail.mulVec z) i)) := by
                  nlinarith [hpairClean]
                have hlower :
                    lowerBound (Sum.inr ilow) ≤
                      ((r i + (C.mulVec y) i) - (Atail.mulVec z) i) / (A i 0) := by
                  dsimp [lowerBound]
                  apply (le_div_iff₀ hpos).2
                  rw [div_mul_eq_mul_div, mul_comm]
                  exact (div_le_iff₀ hiPos).2 (by
                    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross)
                exact hlower
            )
          have hmul :
              A i 0 * t ≤ (r i + (C.mulVec y) i) - (Atail.mulVec z) i := by
            simpa [mul_comm] using (le_div_iff₀ hpos).1 ht_le
          have hrow :
              A i 0 * t + (Atail.mulVec z) i ≤ r i + (C.mulVec y) i := by
            linarith
          simpa [Atail, mulVec_vecCons_eq_head_add_tail] using hrow
        · -- For a negative row, the chosen head coordinate dominates its lower bound.
          have hneg : A i 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzero
          let ilow : {i : rowIdx // A i 0 < 0} := ⟨i, hneg⟩
          have hlower :
              lowerBound (Sum.inr ilow) ≤ t := by
            exact Finset.le_sup' (s := (Finset.univ : Finset (Unit ⊕ {i : rowIdx // A i 0 < 0})))
              (f := lowerBound) (b := Sum.inr ilow) (by simp)
          have hiPos : 0 < -A i 0 := by
            linarith
          have hmul :
              ((Atail.mulVec z) i - (r i + (C.mulVec y) i)) ≤ (-A i 0) * t := by
            have hmul' :
                ((Atail.mulVec z) i - (r i + (C.mulVec y) i)) ≤ t * (-A i 0) := by
              exact (div_le_iff₀ hiPos).1 (by simpa [lowerBound] using hlower)
            simpa [mul_comm] using hmul'
          have hrow :
              A i 0 * t + (Atail.mulVec z) i ≤ r i + (C.mulVec y) i := by
            linarith
          simpa [Atail, mulVec_vecCons_eq_head_add_tail] using hrow

/-- Induction on `Fin n` gives a finite projected inequality description for every nonnegative
affine feasibility system. -/
private lemma exists_nonnegative_affine_inequality_solution_iff_projected_inequalities_fin
    {rowIdx paramIdx : Type*}
    [Fintype rowIdx] [Fintype paramIdx]
    [DecidableEq rowIdx] [DecidableEq paramIdx]
    (n : ℕ) (A : Matrix rowIdx (Fin n) ℝ) (r : rowIdx → ℝ) (C : Matrix rowIdx paramIdx ℝ) :
    ∃ p : ℕ, ∃ M : Matrix (Fin p) paramIdx ℝ, ∃ b : Fin p → ℝ,
      ∀ y : paramIdx → ℝ,
        (∃ x : Fin n → ℝ, (∀ a, 0 ≤ x a) ∧
          ∀ i : rowIdx, (A.mulVec x) i ≤ r i + (C.mulVec y) i) ↔
          ∀ i : Fin p, ∑ j : paramIdx, M i j * y j ≤ b i := by
  classical
  induction n generalizing rowIdx paramIdx with
  | zero =>
      -- The base case is exactly the already-proved empty-variable projection lemma.
      simpa using
        exists_nonnegative_affine_inequality_solution_iff_projected_inequalities_of_isEmpty
          (rowIdx := rowIdx) (varIdx := Fin 0) (paramIdx := paramIdx) (inferInstance : IsEmpty (Fin 0))
          A r C
  | succ n ih =>
      -- Eliminate the head variable once, then project the resulting tail system recursively.
      rcases exists_nonnegative_head_iff_fourierMotzkin_step (A := A) (r := r) (C := C) with
        ⟨A_FM, r_FM, C_FM, hFM⟩
      rcases ih A_FM r_FM C_FM with ⟨p, M, b, hproj⟩
      refine ⟨p, M, b, ?_⟩
      intro y
      rw [hFM y]
      exact hproj y

/-- Finite-dimensional projection of a nonnegative affine inequality feasibility system onto the
parameter coordinates. -/
private lemma exists_nonnegative_affine_inequality_solution_iff_projected_inequalities
    {rowIdx varIdx paramIdx : Type*}
    [Fintype rowIdx] [Fintype varIdx] [Fintype paramIdx]
    [DecidableEq rowIdx] [DecidableEq varIdx] [DecidableEq paramIdx]
    (A : Matrix rowIdx varIdx ℝ) (r : rowIdx → ℝ) (C : Matrix rowIdx paramIdx ℝ) :
    ∃ p : ℕ, ∃ M : Matrix (Fin p) paramIdx ℝ, ∃ b : Fin p → ℝ,
      ∀ y : paramIdx → ℝ,
        (∃ x : varIdx → ℝ, (∀ a, 0 ≤ x a) ∧
          ∀ i : rowIdx, (A.mulVec x) i ≤ r i + (C.mulVec y) i) ↔
          ∀ i : Fin p, ∑ j : paramIdx, M i j * y j ≤ b i := by
  classical
  let e : varIdx ≃ Fin (Fintype.card varIdx) := Fintype.equivFin varIdx
  let AFin : Matrix rowIdx (Fin (Fintype.card varIdx)) ℝ := A.submatrix id e.symm
  rcases exists_nonnegative_affine_inequality_solution_iff_projected_inequalities_fin
      (n := Fintype.card varIdx) (A := AFin) (r := r) (C := C) with
      ⟨p, M, b, hproj⟩
  refine ⟨p, M, b, ?_⟩
  intro y
  constructor
  · rintro ⟨x, hxnonneg, hxineq⟩
    have hmul :
        AFin.mulVec (x ∘ e.symm) = A.mulVec x := by
      -- Reindexing the variable coordinates by `equivFin` preserves the row evaluations.
      simpa [AFin, Function.comp_def] using
        (Matrix.submatrix_mulVec_equiv (M := A) (v := x ∘ e.symm) (e₁ := id) (e₂ := e.symm))
    have hineqFin :
        ∀ i : rowIdx, (AFin.mulVec (x ∘ e.symm)) i ≤ r i + (C.mulVec y) i := by
      intro i
      simpa [hmul] using hxineq i
    have hxnonnegFin : ∀ a : Fin (Fintype.card varIdx), 0 ≤ (x ∘ e.symm) a := by
      intro a
      exact hxnonneg (e.symm a)
    exact (hproj y).mp ⟨x ∘ e.symm, hxnonnegFin, hineqFin⟩
  · intro hy
    rcases (hproj y).mpr hy with ⟨xFin, hxnonnegFin, hxineqFin⟩
    refine ⟨xFin ∘ e, ?_, ?_⟩
    · -- Pull the nonnegativity witness back along the finite reindexing equivalence.
      intro a
      exact hxnonnegFin (e a)
    · have hmul :
          AFin.mulVec xFin = A.mulVec (xFin ∘ e) := by
        -- The same reindexing identity transports the projected witness back to `varIdx`.
        simpa [AFin, Function.comp_def] using
          (Matrix.submatrix_mulVec_equiv (M := A) (v := xFin) (e₁ := id) (e₂ := e.symm))
      intro i
      simpa [hmul] using hxineqFin i

/-- Finite-dimensional projection of a nonnegative affine feasibility system onto the parameter
coordinates. -/
private lemma exists_nonnegative_affine_solution_iff_projected_inequalities
    {eqIdx varIdx paramIdx : Type*}
    [Fintype eqIdx] [Fintype varIdx] [Fintype paramIdx]
    [DecidableEq eqIdx] [DecidableEq varIdx] [DecidableEq paramIdx]
    (B : Matrix eqIdx varIdx ℝ) (r : eqIdx → ℝ) (C : Matrix eqIdx paramIdx ℝ) :
    ∃ p : ℕ, ∃ M : Matrix (Fin p) paramIdx ℝ, ∃ b : Fin p → ℝ,
      ∀ y : paramIdx → ℝ,
        (∃ x : varIdx → ℝ, (∀ a, 0 ≤ x a) ∧ B.mulVec x = r + C.mulVec y) ↔
          ∀ i : Fin p, ∑ j : paramIdx, M i j * y j ≤ b i := by
  classical
  rcases exists_nonnegative_affine_inequality_solution_iff_projected_inequalities
      (A := signedRowMatrix B) (r := signedRowVector r) (C := signedRowMatrix C) with
      ⟨p, M, b, hprojected⟩
  refine ⟨p, M, b, ?_⟩
  intro y
  -- Route correction: first convert equalities to a doubled inequality system, then project that
  -- inequality system. This isolates the remaining blocker in the inequality-only theorem.
  rw [affine_equality_system_iff_signed_affine_inequalities (B := B) (r := r) (C := C) (y := y)]
  simpa using hprojected y

private lemma supportable_slack_iff_projected_inequalities
    {n m k : ℕ}
    (hk : k ≤ n)
    (A : Matrix (Fin n) (Fin m) ℝ)
    (edgeCapacity : Fin m → ℝ)
    (smax : Fin k → ℝ)
    (supportable : Set (Fin (n - k) → ℝ))
    (hsupportable_slack :
      ∀ c' : Fin (n - k) → ℝ,
        c' ∈ supportable ↔
          (∀ i, 0 ≤ c' i) ∧
          ∃ x : SupportSlackVar m k → ℝ,
            (∀ a, 0 ≤ x a) ∧
            ((supportSlackMatrix A hk).mulVec x =
              supportSlackRhs (n := n) edgeCapacity smax +
                (supportSlackConsumerMatrix (n := n) (m := m) (k := k)).mulVec c')) :
    ∃ p : ℕ, ∃ M : Matrix (Fin p) (Fin (n - k)) ℝ, ∃ b : Fin p → ℝ,
      ∀ c' : Fin (n - k) → ℝ,
        c' ∈ supportable ↔
          ∀ i : Fin p, ∑ j : Fin (n - k), M i j * c' j ≤ b i := by
  classical
  -- Route correction: isolate the genuinely missing projection theorem once, then fold the
  -- obvious coordinatewise nonnegativity block into the resulting inequality family.
  rcases exists_nonnegative_affine_solution_iff_projected_inequalities
      (B := supportSlackMatrix A hk)
      (r := supportSlackRhs (n := n) edgeCapacity smax)
      (C := supportSlackConsumerMatrix (n := n) (m := m) (k := k)) with
      ⟨pSlack, MSlack, bSlack, hprojected⟩
  let rowEquiv : Fin pSlack ⊕ Fin (n - k) ≃ Fin (pSlack + (n - k)) := finSumFinEquiv
  let M : Matrix (Fin (pSlack + (n - k))) (Fin (n - k)) ℝ :=
    fun i j =>
      match rowEquiv.symm i with
      | Sum.inl iSlack => MSlack iSlack j
      | Sum.inr iCoord => if iCoord = j then (-1 : ℝ) else 0
  let b : Fin (pSlack + (n - k)) → ℝ :=
    fun i =>
      match rowEquiv.symm i with
      | Sum.inl iSlack => bSlack iSlack
      | Sum.inr _ => 0
  refine ⟨pSlack + (n - k), M, b, ?_⟩
  intro c'
  rw [hsupportable_slack c']
  constructor
  · rintro ⟨hc_nonneg, hslack⟩ i
    -- Dispatch each combined row to either the projected slack system or a coordinate inequality.
    cases hrow : rowEquiv.symm i with
    | inl iSlack =>
        simpa [M, b, rowEquiv, hrow] using ((hprojected c').mp hslack iSlack)
    | inr iCoord =>
        have hcoord :
            ∑ j : Fin (n - k), (if iCoord = j then (-1 : ℝ) else 0) * c' j ≤ 0 :=
          (coordinatewise_nonneg_iff_standard_inequalities c').mp hc_nonneg iCoord
        simpa [M, b, rowEquiv, hrow] using hcoord
  · intro hcombined
    -- Split the combined inequalities back into the slack block and the coordinatewise block.
    have hslack :
        ∀ i : Fin pSlack, ∑ j : Fin (n - k), MSlack i j * c' j ≤ bSlack i := by
      intro i
      simpa [M, b, rowEquiv] using hcombined (rowEquiv (Sum.inl i))
    have hc_nonneg :
        ∀ i : Fin (n - k), 0 ≤ c' i := by
      intro i
      have hcoord :
          ∑ j : Fin (n - k), (if i = j then (-1 : ℝ) else 0) * c' j ≤ 0 := by
        simpa [M, b, rowEquiv] using hcombined (rowEquiv (Sum.inr i))
      have hsum : ∑ j : Fin (n - k), (if i = j then (-1 : ℝ) else 0) * c' j = -c' i := by
        classical
        simp
      rw [hsum] at hcoord
      linarith
    exact ⟨hc_nonneg, (hprojected c').mpr hslack⟩

/- [BLOCK Exercise 17.7-(a) | 15 | thm]
Consider a directed water-supply network with n nodes and m edges. Nodes 1,ldots,k are supply nodes
and nodes k+1,ldots,n are consumer nodes, where 1 ≤ k ≤ n. Let fⱼ ≥ 0 be the flow on edge j, let hᵢ
be the altitude of node i, let sᵢ ≥ 0 be the supply inflow at node i for i=1,ldots,k, and let cᵢ ≥ 0
be the consumption at node k+i for i=1,ldots,n-k. Thus s ∈ ℝ_+^k, c ∈ ℝ_+^{n-k}, and f ∈ ℝ_+^m. The
flow-conservation equations are Af=[-s; c], where A ∈ ℝ^{n × m} is the node-edge incidence matrix
given by A_{ij}=cases -1 & if edge j leaves node i,; +1 & if edge j enters node i,; 0 & otherwise.
cases Each edge is directed from a higher-altitude node to a lower-altitude node: if edge j goes
from node i to node l, then hᵢ>h_l. For each edge j from node i to node l, the flow satisfies
fⱼ=(α_0 θ_j Rⱼ^2 (hᵢ-h_l))/(Lⱼ), where α_0>0 is given, Lⱼ>0 is the pipe length, Rⱼ>0 is the fixed
known pipe radius, and θ_j ∈ [0,1] is the valve opening. The supply constraints are sᵢ ≤ sᵢ^{max},
i=1,ldots,k. A vector c ∈ ℝ_+^{n-k} is supportable if there exist f ∈ ℝ_+^m, s ∈ ℝ_+^k, and θ ∈ ℝ^m
with 0 ≤ θ_j ≤ 1 for all j, such that all the conditions above hold. Show that the set of
supportable consumption vectors is a polyhedron, and determine how to decide whether a given
consumption vector is supportable.
-/
theorem supportableConsumptionSet_isPolyhedron_and_characterization
    (n m k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : k ≤ n)
    (tail head : Fin m → Fin n)
    (h : Fin n → ℝ)
    (alpha0 : ℝ)
    (halpha0 : 0 < alpha0)
    (L R : Fin m → ℝ)
    (hL : ∀ j, 0 < L j)
    (hR : ∀ j, 0 < R j)
    (edge_descends : ∀ j, h (tail j) > h (head j))
    (smax : Fin k → ℝ)
    (hsmax : ∀ i, 0 ≤ smax i)
    (c : Fin (n - k) → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    let A := nodeEdgeIncidenceMatrix n m tail head
    let edgeCapacity : Fin m → ℝ := fun j => alpha0 * (R j)^2 * (h (tail j) - h (head j)) / (L j)
    let supportable : Set (Fin (n - k) → ℝ) := fun c' =>
      (∀ i, 0 ≤ c' i) ∧
      ∃ f : Fin m → ℝ, ∃ s : Fin k → ℝ, ∃ theta : Fin m → ℝ,
        (∀ j, 0 ≤ f j) ∧
        (∀ i, 0 ≤ s i ∧ s i ≤ smax i) ∧
        (∀ j, 0 ≤ theta j ∧ theta j ≤ 1) ∧
        (∀ i : Fin k,
          ∑ j : Fin m, A ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ j * f j = - s i) ∧
        (∀ i : Fin (n - k),
          ∑ j : Fin m, A ⟨k + i.1, by
            have hi : i.1 < n - k := i.2
            omega⟩ j * f j = c' i) ∧
        (∀ j, f j = edgeCapacity j * theta j)
    (∃ p q : ℕ,
      ∃ M : Matrix (Fin p) (Fin (n - k)) ℝ,
        ∃ N : Matrix (Fin q) (Fin (n - k)) ℝ,
          ∃ b : Fin p → ℝ,
            ∃ d : Fin q → ℝ,
              (∀ c' : Fin (n - k) → ℝ,
                c' ∈ supportable ↔
                  (∀ i : Fin p, ∑ j : Fin (n - k), M i j * c' j ≤ b i) ∧
                  (∀ i : Fin q, ∑ j : Fin (n - k), N i j * c' j = d i)) ∧
              (c ∈ supportable ↔
                (∀ i : Fin p, ∑ j : Fin (n - k), M i j * c j ≤ b i) ∧
                (∀ i : Fin q, ∑ j : Fin (n - k), N i j * c j = d i))) := by
  -- Route correction: first remove the valve variables using positivity of the edge capacities.
  -- That leaves a finite linear feasibility system, and only the projection step remains.
  let A : Matrix (Fin n) (Fin m) ℝ := nodeEdgeIncidenceMatrix n m tail head
  let edgeCapacity : Fin m → ℝ :=
    fun j => alpha0 * (R j)^2 * (h (tail j) - h (head j)) / L j
  let supplyEq : (Fin m → ℝ) → (Fin k → ℝ) → Prop :=
    fun f s =>
      ∀ i : Fin k, ∑ j : Fin m, A ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ j * f j = -s i
  let consumerEq : (Fin m → ℝ) → (Fin (n - k) → ℝ) → Prop :=
    fun f c' =>
      ∀ i : Fin (n - k), ∑ j : Fin m, A (consumerNode hk i) j * f j = c' i
  let supportable : Set (Fin (n - k) → ℝ) :=
    fun c' =>
      (∀ i, 0 ≤ c' i) ∧
      ∃ f : Fin m → ℝ, ∃ s : Fin k → ℝ, ∃ theta : Fin m → ℝ,
        (∀ j, 0 ≤ f j) ∧
        (∀ i, 0 ≤ s i ∧ s i ≤ smax i) ∧
        (∀ j, 0 ≤ theta j ∧ theta j ≤ 1) ∧
        supplyEq f s ∧
        consumerEq f c' ∧
        (∀ j, f j = edgeCapacity j * theta j)
  have hedgeCapacity_pos : ∀ j : Fin m, 0 < edgeCapacity j := by
    -- The edge-capacity helper discharges the only genuinely nonlinear scalar positivity fact.
    intro j
    simpa [edgeCapacity] using
      edgeCapacity_pos tail head h alpha0 halpha0 L R hL hR edge_descends j
  have hsupportable :
      ∀ c' : Fin (n - k) → ℝ,
        c' ∈ supportable ↔
          (∀ i, 0 ≤ c' i) ∧
          ∃ f : Fin m → ℝ, ∃ s : Fin k → ℝ,
            (∀ j, 0 ≤ f j ∧ f j ≤ edgeCapacity j) ∧
            (∀ i, 0 ≤ s i ∧ s i ≤ smax i) ∧
            supplyEq f s ∧
            consumerEq f c' := by
    intro c'
    -- Positive capacities make the valve equations equivalent to box constraints on each edge flow.
    change
      ((∀ i, 0 ≤ c' i) ∧
        ∃ f : Fin m → ℝ, ∃ s : Fin k → ℝ, ∃ theta : Fin m → ℝ,
          (∀ j, 0 ≤ f j) ∧
          (∀ i, 0 ≤ s i ∧ s i ≤ smax i) ∧
          (∀ j, 0 ≤ theta j ∧ theta j ≤ 1) ∧
          supplyEq f s ∧
          consumerEq f c' ∧
          (∀ j, f j = edgeCapacity j * theta j)) ↔
      ((∀ i, 0 ≤ c' i) ∧
        ∃ f : Fin m → ℝ, ∃ s : Fin k → ℝ,
          (∀ j, 0 ≤ f j ∧ f j ≤ edgeCapacity j) ∧
          (∀ i, 0 ≤ s i ∧ s i ≤ smax i) ∧
          supplyEq f s ∧
          consumerEq f c')
    exact
      supportable_iff_exists_boxed_flow_supply
        edgeCapacity hedgeCapacity_pos smax supplyEq consumerEq c'
  have hsupportable_slack :
      ∀ c' : Fin (n - k) → ℝ,
        c' ∈ supportable ↔
          (∀ i, 0 ≤ c' i) ∧
          ∃ x : SupportSlackVar m k → ℝ,
            (∀ a, 0 ≤ x a) ∧
            ((supportSlackMatrix A hk).mulVec x =
              supportSlackRhs (n := n) edgeCapacity smax +
                (supportSlackConsumerMatrix (n := n) (m := m) (k := k)).mulVec c') := by
    intro c'
    -- Route correction: the graph-specific work is now finished; supportability is exactly one
    -- explicit nonnegative affine feasibility problem in the consumer demand `c'`.
    rw [hsupportable c']
    exact boxed_supportable_iff_exists_nonnegative_slack_rhs hk A edgeCapacity smax c'
  -- Route correction: instead of the unfinished abstract Farkas route, project the explicit slack
  -- system by Fourier-Motzkin elimination and then take `q = 0`.
  rcases supportable_slack_iff_projected_inequalities hk A edgeCapacity smax supportable
      hsupportable_slack with ⟨p, M, b, hpoly⟩
  refine ⟨p, 0, M, fun i => Fin.elim0 i, b, fun i => Fin.elim0 i, ?_, ?_⟩
  · -- The universal characterization is purely by inequalities, so the equality block is vacuous.
    intro c'
    constructor
    · intro hc'
      refine ⟨(hpoly c').mp hc', ?_⟩
      intro i
      exact Fin.elim0 i
    · rintro ⟨hc'ineq, hc'eq⟩
      exact (hpoly c').mpr hc'ineq
  · -- The requested test for the specific consumption vector is the same specialization at `c`.
    constructor
    · intro hc_support
      refine ⟨(hpoly c).mp hc_support, ?_⟩
      intro i
      exact Fin.elim0 i
    · rintro ⟨hc_ineq, hc_eq⟩
      exact (hpoly c).mpr hc_ineq

end «problem-88»
