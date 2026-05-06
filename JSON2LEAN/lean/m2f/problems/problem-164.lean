import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-164»
/-
Consider the optimization problem maximize & sum_i = 1^n log(\frac{sum_j = 1^n B_ijpⱼ}{sum_j = 1^n
B_ijpⱼ - pᵢ}); subject to & sum_i = 1^n pᵢ = 1,; & pᵢ ≥ 0, i = 1, ..., n, with variable p ∈ ℝ^n.
Define
y = Bp.
-/
structure LogFractionMaximizationProblem (n : ℕ) where
  B : Matrix (Fin n) (Fin n) ℝ
  p : Fin n → ℝ
  yVec : Fin n → ℝ
  objective : ℝ
  h_y : yVec = fun i => ∑ j, B i j * p j
  h_objective : objective = ∑ i, Real.log ((yVec i) / (yVec i - p i))
  h_sum_one : ∑ i, p i = 1
  h_nonneg : ∀ i, 0 ≤ p i

def LogFractionMaximizationProblem.objectiveFn {n : ℕ} (P : LogFractionMaximizationProblem n)
    (p : Fin n → ℝ) : ℝ :=
  ∑ i, Real.log (((∑ j, P.B i j * p j)) / ((∑ j, P.B i j * p j) - p i))

def LogFractionMaximizationProblem.isFeasible {n : ℕ}
    (_P : LogFractionMaximizationProblem n) (p : Fin n → ℝ) : Prop :=
  (∑ i, p i = 1) ∧ ∀ i, 0 ≤ p i

def BMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i j + v i

def logFractionFeasible {n : ℕ} (p : Fin n → ℝ) : Prop :=
  (∑ i, p i = 1) ∧ ∀ i, 0 ≤ p i

def logFractionObjective {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) : ℝ :=
  ∑ i, Real.log (((B.mulVec p) i) / ((B.mulVec p) i - p i))

def transformedFeasible {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    Prop :=
  (∑ i, y i - ∑ i, (C.mulVec y) i = 1) ∧
    ∀ i, 0 ≤ y i - (C.mulVec y) i

def transformedObjective {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    ℝ :=
  ∑ i, Real.log (y i / (C.mulVec y) i)

/-- The gap vector `y - C y` is the `mulVec` action of `I - C` on `y`. -/
lemma gap_eq_sub_mulVec {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    (fun i => y i - (C.mulVec y) i) = (1 - C).mulVec y := by
  -- Rewrite the coordinatewise gap as the linear action of `1 - C`.
  ext i
  simp [Matrix.sub_mulVec]

/-- If `y = B p`, then the inverse change of variables recovers `p`. -/
lemma recover_p_from_mulVec {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hB_unit : IsUnit (BMatrix A v))
    (hB_inv : (BMatrix A v)⁻¹ = 1 - C)
    (p : Fin n → ℝ) :
    (fun i =>
      ((BMatrix A v).mulVec p) i - (C.mulVec ((BMatrix A v).mulVec p)) i) = p := by
  letI : Invertible (BMatrix A v) := hB_unit.unit.invertible
  calc
    (fun i =>
      ((BMatrix A v).mulVec p) i - (C.mulVec ((BMatrix A v).mulVec p)) i)
        = (1 - C).mulVec ((BMatrix A v).mulVec p) :=
          gap_eq_sub_mulVec C ((BMatrix A v).mulVec p)
    _ = (BMatrix A v)⁻¹.mulVec ((BMatrix A v).mulVec p) := by
      -- Replace `1 - C` with the assumed inverse of `B`.
      simp [hB_inv]
    _ = p := by
      -- Cancel `B` against its inverse on the vector `p`.
      exact
        Matrix.inv_mulVec_eq_vec
          (A := BMatrix A v) (u := (BMatrix A v).mulVec p) (v := p) rfl

/-- Applying `B` to the gap vector reconstructs `y`. -/
lemma reconstruct_y_from_gap {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hB_unit : IsUnit (BMatrix A v))
    (hB_inv : (BMatrix A v)⁻¹ = 1 - C)
    (y : Fin n → ℝ) :
    (BMatrix A v).mulVec (fun i => y i - (C.mulVec y) i) = y := by
  letI : Invertible (BMatrix A v) := hB_unit.unit.invertible
  calc
    (BMatrix A v).mulVec (fun i => y i - (C.mulVec y) i)
        = (BMatrix A v).mulVec ((1 - C).mulVec y) := by
          -- Repackage the gap vector as `(1 - C) *ᵥ y`.
          rw [gap_eq_sub_mulVec]
    _ = ((BMatrix A v) * (1 - C)).mulVec y := by
      -- Move the nested `mulVec` into matrix multiplication.
      rw [Matrix.mulVec_mulVec]
    _ = ((BMatrix A v) * (BMatrix A v)⁻¹).mulVec y := by
      -- Replace `1 - C` with the inverse matrix.
      simp [hB_inv]
    _ = y := by
      -- Cancel `B` with its inverse.
      simp [Matrix.mul_inv_of_invertible]

/-- The recovered gap identity rewrites the transformed balance constraint. -/
lemma balance_eq_sum_one {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (y p : Fin n → ℝ)
    (hgap : (fun i => y i - (C.mulVec y) i) = p) :
    ((∑ i, y i) - ∑ i, (C.mulVec y) i = 1) ↔ (∑ i, p i = 1) := by
  constructor <;> intro h
  · -- Sum the pointwise gap identity to pass from the transformed balance to `∑ p = 1`.
    calc
      ∑ i, p i = ∑ i, (y i - (C.mulVec y) i) := by
        simp [hgap]
      _ = (∑ i, y i) - ∑ i, (C.mulVec y) i := by
        rw [Finset.sum_sub_distrib]
      _ = 1 := h
  · -- Run the same summed identity in the reverse direction.
    calc
      (∑ i, y i) - ∑ i, (C.mulVec y) i = ∑ i, (y i - (C.mulVec y) i) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ i, p i := by
        simp [hgap]
      _ = 1 := h

/-- The recovered gap identity rewrites pointwise nonnegativity. -/
lemma gap_nonneg_iff_p_nonneg {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (y p : Fin n → ℝ)
    (hgap : (fun i => y i - (C.mulVec y) i) = p) :
    (∀ i, 0 ≤ y i - (C.mulVec y) i) ↔ ∀ i, 0 ≤ p i := by
  constructor <;> intro h i
  · -- Read the pointwise equality at index `i` and rewrite the target.
    have hi : y i - (C.mulVec y) i = p i := by
      simpa using congrArg (fun f => f i) hgap
    rw [← hi]
    exact h i
  · -- Use the same pointwise equality to move back to the transformed gap.
    have hi : y i - (C.mulVec y) i = p i := by
      simpa using congrArg (fun f => f i) hgap
    rw [hi]
    exact h i

/-- The recovered gap identity rewrites the logarithmic denominator. -/
lemma objective_denominator_rewrite {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (y p : Fin n → ℝ)
    (hgap : (fun i => y i - (C.mulVec y) i) = p)
    (i : Fin n) :
    y i - p i = (C.mulVec y) i := by
  -- Evaluate the gap identity at index `i` and solve the scalar equality.
  have hi : y i - (C.mulVec y) i = p i := by
    simpa using congrArg (fun f => f i) hgap
  linarith

/-
Consider the transformed optimization problem obtained from the change of variables y = Bp and
p = (I - C)y. Its feasibility constraints are
\sum_i y_i - \sum_i (Cy)_i = 1 and y_i - (Cy)_i ≥ 0, and its objective is
\sum_i log (y_i / (Cy)_i).
-/
structure EquivalentTransformedOptimizationProblem (n : ℕ) where
  C : Matrix (Fin n) (Fin n) ℝ
  y : Fin n → ℝ
  objective : ℝ
  h_objective : objective = transformedObjective C y
  h_balance : (∑ i, y i) - ∑ i, ∑ j, C i j * y j = 1
  h_nonneg_gap : ∀ i, 0 ≤ y i - ∑ j, C i j * y j

def EquivalentTransformedOptimizationProblem.Cy {n : ℕ}
    (P : EquivalentTransformedOptimizationProblem n) :
    Fin n → ℝ :=
  fun i => ∑ j, P.C i j * P.y j

def EquivalentTransformedOptimizationProblem.isFeasible {n : ℕ}
    (P : EquivalentTransformedOptimizationProblem n) : Prop :=
  ((∑ i, P.y i) - ∑ i, P.Cy i = 1) ∧ ∀ i, 0 ≤ P.y i - P.Cy i

/-
Exercise 12.3 | 14 | thm

Let n ∈ ℕ. Let A ∈ ℝ^{n×n} and v ∈ ℝⁿ satisfy A_{ij} ≥ 0, vᵢ ≥ 0, and A_{ii} = 1 for all i, j = 1,
…, n. Let 1 ∈ ℝⁿ be the all - ones vector, define B = A + v1ᵀ, and assume that B is nonsingular with

B⁻¹ = I - C,

where C ∈ ℝ^{n×n}. Consider the log-fraction maximization problem. Prove that the change of variables
y = Bp, equivalently p = (I - C)y, gives an equivalent transformed problem: feasibility is preserved
in both directions and the objectives agree.
-/
theorem logFractionProblem_equivalent_to_transformedProblem
    (n : ℕ)
    (A C : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ)
    (hB_unit : IsUnit (BMatrix A v))
    (hB_inv : (BMatrix A v)⁻¹ = 1 - C) :
    (∀ p : Fin n → ℝ,
      let y := (BMatrix A v).mulVec p
      (∀ i, 0 < y i ∧ 0 < (C.mulVec y) i) →
        (logFractionFeasible p ↔ transformedFeasible C y) ∧
          logFractionObjective (BMatrix A v) p = transformedObjective C y) ∧
    (∀ y : Fin n → ℝ,
      let p : Fin n → ℝ := fun i => y i - (C.mulVec y) i
      (∀ i, 0 < y i ∧ 0 < (C.mulVec y) i) →
        (BMatrix A v).mulVec p = y ∧
          (transformedFeasible C y ↔ logFractionFeasible p) ∧
          transformedObjective C y = logFractionObjective (BMatrix A v) p) := by
  constructor
  · intro p
    dsimp
    intro _hy_pos
    have hgap :
        (fun i =>
          ((BMatrix A v).mulVec p) i - (C.mulVec ((BMatrix A v).mulVec p)) i) = p :=
      recover_p_from_mulVec A C v hB_unit hB_inv p
    constructor
    · constructor <;> intro h
      · rcases h with ⟨hsum, hnonneg⟩
        constructor
        · -- Rewrite the transformed balance constraint through the recovered gap identity.
          exact (balance_eq_sum_one C ((BMatrix A v).mulVec p) p hgap).2 hsum
        · -- Rewrite transformed nonnegativity pointwise through the same identity.
          exact (gap_nonneg_iff_p_nonneg C ((BMatrix A v).mulVec p) p hgap).2 hnonneg
      · rcases h with ⟨hsum, hnonneg⟩
        constructor
        · -- Sum the recovered gap identity to return to the original balance constraint.
          exact (balance_eq_sum_one C ((BMatrix A v).mulVec p) p hgap).1 hsum
        · -- Read the recovered gap identity coordinatewise to return to `p ≥ 0`.
          exact (gap_nonneg_iff_p_nonneg C ((BMatrix A v).mulVec p) p hgap).1 hnonneg
    · -- Rewrite each logarithmic denominator as `(C *ᵥ y) i`.
      unfold logFractionObjective transformedObjective
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [objective_denominator_rewrite C ((BMatrix A v).mulVec p) p hgap i]
  · intro y
    dsimp
    intro _hy_pos
    have hreconstruct :
        (BMatrix A v).mulVec (fun i => y i - (C.mulVec y) i) = y :=
      reconstruct_y_from_gap A C v hB_unit hB_inv y
    constructor
    · -- Apply `B` to the explicit gap vector and use the inverse relation.
      exact hreconstruct
    constructor
    · constructor <;> intro h
      · rcases h with ⟨hsum, hnonneg⟩
        constructor
        · -- The literal definition of `p` makes the balance rewrite immediate.
          exact
            (balance_eq_sum_one C y (fun i => y i - (C.mulVec y) i) rfl).1 hsum
        · -- The same literal definition rewrites nonnegativity without extra algebra.
          exact
            (gap_nonneg_iff_p_nonneg C y (fun i => y i - (C.mulVec y) i) rfl).1
              hnonneg
      · rcases h with ⟨hsum, hnonneg⟩
        constructor
        · -- Convert the original balance constraint back to the transformed one.
          exact
            (balance_eq_sum_one C y (fun i => y i - (C.mulVec y) i) rfl).2 hsum
        · -- Convert pointwise nonnegativity back to the transformed gap form.
          exact
            (gap_nonneg_iff_p_nonneg C y (fun i => y i - (C.mulVec y) i) rfl).2
              hnonneg
    · -- Rewrite the original objective using the reconstructed numerator and the explicit gap.
      unfold transformedObjective logFractionObjective
      refine Finset.sum_congr rfl ?_
      intro i _
      have hnum : ((BMatrix A v).mulVec (fun j => y j - (C.mulVec y) j)) i = y i := by
        simpa using congrArg (fun f => f i) hreconstruct
      rw [hnum]
      rw [objective_denominator_rewrite C y (fun i => y i - (C.mulVec y) i) rfl i]

end «problem-164»
