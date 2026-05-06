import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-20»
/-
For a differentiable optimization problem with equality constraints (h(x) = 0), the first - order
optimality conditions are that there exists a multiplier (lambda) such that (nabla f(x^
star) + Dh(x^ star)^T lambda = 0) and (h(x^ star) = 0).
-/
structure EquivalentGeometricConvexProgram where
  n : ℕ
  A : Fin n → Fin n → ℝ
  c : Fin n → ℝ
  d : Fin n → ℝ

def EquivalentGeometricConvexProgram.geometricObjective
    (P : EquivalentGeometricConvexProgram) :
    (Fin P.n → ℝ) → (Fin P.n → ℝ) → ℝ :=
  fun x y => ∑ i : Fin P.n, ∑ j : Fin P.n, x i * P.A i j * y j

def EquivalentGeometricConvexProgram.phi
    (P : EquivalentGeometricConvexProgram) :
    (Fin P.n → ℝ) → (Fin P.n → ℝ) → ℝ :=
  fun u v =>
    Real.log (∑ i : Fin P.n, ∑ j : Fin P.n, Real.exp (u i) * P.A i j * Real.exp (v j))

def EquivalentGeometricConvexProgram.xOfU
    (P : EquivalentGeometricConvexProgram) :
    (Fin P.n → ℝ) → (Fin P.n → ℝ) :=
  fun u i => Real.exp (u i)

def EquivalentGeometricConvexProgram.yOfV
    (P : EquivalentGeometricConvexProgram) :
    (Fin P.n → ℝ) → (Fin P.n → ℝ) :=
  fun v j => Real.exp (v j)

def EquivalentGeometricConvexProgram.geometricFeasible
    (P : EquivalentGeometricConvexProgram) :
    ((Fin P.n → ℝ) × (Fin P.n → ℝ)) → Prop :=
  fun xv =>
    (∀ i : Fin P.n, 0 < xv.1 i) ∧
      (∀ j : Fin P.n, 0 < xv.2 j) ∧
      (∏ i : Fin P.n, Real.rpow (xv.1 i) (P.c i) = 1) ∧
      (∏ j : Fin P.n, Real.rpow (xv.2 j) (P.d j) = 1)

def EquivalentGeometricConvexProgram.convexFeasible
    (P : EquivalentGeometricConvexProgram) :
    ((Fin P.n → ℝ) × (Fin P.n → ℝ)) → Prop :=
  fun uv =>
    (∑ i : Fin P.n, P.c i * uv.1 i = 0) ∧
      (∑ j : Fin P.n, P.d j * uv.2 j = 0)

def EquivalentGeometricConvexProgram.rowWeight
    (P : EquivalentGeometricConvexProgram) (u v : Fin P.n → ℝ) (i : Fin P.n) : ℝ :=
  let x := P.xOfU u
  let y := P.yOfV v
  x i * (∑ j : Fin P.n, P.A i j * y j) / P.geometricObjective x y

def EquivalentGeometricConvexProgram.colWeight
    (P : EquivalentGeometricConvexProgram) (u v : Fin P.n → ℝ) (j : Fin P.n) : ℝ :=
  let x := P.xOfU u
  let y := P.yOfV v
  y j * (∑ i : Fin P.n, P.A i j * x i) / P.geometricObjective x y

def EquivalentGeometricConvexProgram.scaledMatrix
    (P : EquivalentGeometricConvexProgram) (u v : Fin P.n → ℝ) :
    Fin P.n → Fin P.n → ℝ :=
  let x := P.xOfU u
  let y := P.yOfV v
  fun i j => x i * P.A i j * y j / P.geometricObjective x y

/-- The constant `2 × 2` program used to witness that the main theorem is false as written. -/
def counterexampleProgram : EquivalentGeometricConvexProgram where
  n := 2
  A := fun _ _ => 1
  c := fun _ => (1 : ℝ) / 2
  d := fun _ => (1 : ℝ) / 2

/-- The non-feasible `u` coordinate used in the counterexample. -/
def counterexampleU : Fin 2 → ℝ
  | 0 => -100
  | 1 => 0

/-- The zero `v` coordinate used in the counterexample. -/
def counterexampleV : Fin 2 → ℝ := fun _ => 0

/-- In the constant `2 × 2` program, the objective factors into row and column exponential sums. -/
lemma counterexample_phi_eq (u v : Fin 2 → ℝ) :
    counterexampleProgram.phi u v =
      Real.log ((Real.exp (u 0) + Real.exp (u 1)) * (Real.exp (v 0) + Real.exp (v 1))) := by
  -- Expand the finite sums explicitly so the objective separates into a product.
  simp [EquivalentGeometricConvexProgram.phi, counterexampleProgram, Fin.sum_univ_two, mul_add,
    add_mul]
  congr 1
  ring

/-- Feasibility in the constant `2 × 2` program is exactly the vanishing of both coordinate sums. -/
lemma counterexample_convexFeasible_iff (u v : Fin 2 → ℝ) :
    counterexampleProgram.convexFeasible (u, v) ↔ u 0 + u 1 = 0 ∧ v 0 + v 1 = 0 := by
  constructor
  · intro hfeas
    rcases hfeas with ⟨hu, hv⟩
    constructor
    · -- Rewrite the weighted sum constraint and clear the factor `1 / 2`.
      have hu' : (1 / 2 : ℝ) * u 0 + (1 / 2 : ℝ) * u 1 = 0 := by
        simpa [EquivalentGeometricConvexProgram.convexFeasible, counterexampleProgram,
          Fin.sum_univ_two, mul_assoc] using hu
      linarith
    · -- The same simplification handles the `v` constraint.
      have hv' : (1 / 2 : ℝ) * v 0 + (1 / 2 : ℝ) * v 1 = 0 := by
        simpa [EquivalentGeometricConvexProgram.convexFeasible, counterexampleProgram,
          Fin.sum_univ_two, mul_assoc] using hv
      linarith
  · rintro ⟨hu, hv⟩
    constructor
    · -- Reinsert the factor `1 / 2` to recover the original feasibility equation.
      have hu' : (1 / 2 : ℝ) * u 0 + (1 / 2 : ℝ) * u 1 = 0 := by
        linarith
      simpa [EquivalentGeometricConvexProgram.convexFeasible, counterexampleProgram,
        Fin.sum_univ_two, mul_assoc] using hu'
    · -- Repeat the same calculation for the column constraint.
      have hv' : (1 / 2 : ℝ) * v 0 + (1 / 2 : ℝ) * v 1 = 0 := by
        linarith
      simpa [EquivalentGeometricConvexProgram.convexFeasible, counterexampleProgram,
        Fin.sum_univ_two, mul_assoc] using hv'

/-- The two-term exponential AM-GM bound `exp t + exp (-t) ≥ 2`. -/
lemma exp_add_exp_neg_ge_two (t : ℝ) : 2 ≤ Real.exp t + Real.exp (-t) := by
  -- Start from a nonnegative square whose expansion produces the desired inequality.
  have hsq : 0 ≤ (Real.exp (t / 2) - Real.exp (-t / 2)) ^ 2 := sq_nonneg _
  have hrew :
      (Real.exp (t / 2) - Real.exp (-t / 2)) ^ 2 = Real.exp t + Real.exp (-t) - 2 := by
    calc
      (Real.exp (t / 2) - Real.exp (-t / 2)) ^ 2
          = (Real.exp (t / 2)) ^ 2 - 2 * (Real.exp (t / 2) * Real.exp (-t / 2)) +
              (Real.exp (-t / 2)) ^ 2 := by
            ring
      _ = Real.exp (t / 2 + t / 2) - 2 * Real.exp (t / 2 + -t / 2) +
            Real.exp (-t / 2 + -t / 2) := by
            rw [sq, sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ = Real.exp t - 2 * Real.exp 0 + Real.exp (-t) := by
            ring_nf
      _ = Real.exp t - 2 + Real.exp (-t) := by simp
      _ = Real.exp t + Real.exp (-t) - 2 := by ring
  -- After rewriting, the square inequality is exactly the claimed lower bound.
  rw [hrew] at hsq
  linarith

/-- Every feasible point in the constant `2 × 2` program has objective at least `log 4`. -/
lemma counterexample_feasible_phi_lower_bound (u v : Fin 2 → ℝ)
    (hfeas : counterexampleProgram.convexFeasible (u, v)) :
    Real.log 4 ≤ counterexampleProgram.phi u v := by
  -- Rewrite the objective into a product of row and column exponential sums.
  rw [counterexample_phi_eq]
  rcases (counterexample_convexFeasible_iff u v).1 hfeas with ⟨hu, hv⟩
  have huGe : 2 ≤ Real.exp (u 0) + Real.exp (u 1) := by
    -- Feasibility forces the second coordinate to be the negative of the first.
    have huNeg : u 1 = -u 0 := by linarith
    rw [huNeg]
    exact exp_add_exp_neg_ge_two (u 0)
  have hvGe : 2 ≤ Real.exp (v 0) + Real.exp (v 1) := by
    -- The column variables satisfy the same symmetry.
    have hvNeg : v 1 = -v 0 := by linarith
    rw [hvNeg]
    exact exp_add_exp_neg_ge_two (v 0)
  have huNonneg : 0 ≤ Real.exp (u 0) + Real.exp (u 1) := by positivity
  have hprod : (4 : ℝ) ≤
      (Real.exp (u 0) + Real.exp (u 1)) * (Real.exp (v 0) + Real.exp (v 1)) := by
    -- Multiply the two lower bounds to obtain the product bound.
    have hmul :=
      mul_le_mul huGe hvGe (by positivity) huNonneg
    nlinarith
  -- Monotonicity of `log` on positive reals transfers the bound to `phi`.
  exact Real.log_le_log (by norm_num) hprod

/-- The chosen non-feasible point still has objective at most `log 4`. -/
lemma counterexample_phi_upper_bound :
    counterexampleProgram.phi counterexampleU counterexampleV ≤ Real.log 4 := by
  -- Rewrite the objective at the explicit point and compare the logarithm arguments.
  rw [counterexample_phi_eq]
  have hexp_le_one : Real.exp (-100 : ℝ) ≤ 1 := by
    -- The exponent `-100` is nonpositive, so its exponential is at most `1`.
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num : (-100 : ℝ) ≤ 0)
  have harg_pos :
      0 < (Real.exp (counterexampleU 0) + Real.exp (counterexampleU 1)) *
        (Real.exp (counterexampleV 0) + Real.exp (counterexampleV 1)) := by
    positivity
  have harg_le :
      (Real.exp (counterexampleU 0) + Real.exp (counterexampleU 1)) *
          (Real.exp (counterexampleV 0) + Real.exp (counterexampleV 1)) ≤ 4 := by
    -- At the counterexample point the column factor is exactly `2`, and the row factor is `< 2`.
    simp [counterexampleU, counterexampleV]
    nlinarith
  exact Real.log_le_log harg_pos harg_le

/-- The explicit non-feasible point satisfies the theorem's `IsMinOn` hypothesis. -/
lemma counterexample_isMinOn :
    IsMinOn
      (fun uv : (Fin 2 → ℝ) × (Fin 2 → ℝ) => counterexampleProgram.phi uv.1 uv.2)
      {uv | counterexampleProgram.convexFeasible uv}
      (counterexampleU, counterexampleV) := by
  -- Route correction: `IsMinOn` only compares the objective to feasible points, so the witness
  -- point itself need not satisfy the feasibility equations.
  rw [isMinOn_iff]
  intro uv huv
  -- Sandwich the feasible objective below by `log 4` and the witness above by `log 4`.
  have hupper := counterexample_phi_upper_bound
  have hlower := counterexample_feasible_phi_lower_bound uv.1 uv.2 huv
  linarith

/-- The explicit `IsMinOn` witness is not itself feasible for the convex constraints. -/
lemma counterexample_not_convexFeasible :
    ¬ counterexampleProgram.convexFeasible (counterexampleU, counterexampleV) := by
  -- Rewrite feasibility into the two coordinate-sum equations and evaluate the explicit witness.
  rw [counterexample_convexFeasible_iff]
  simp [counterexampleU, counterexampleV]

/-- The first row weight at the counterexample point simplifies to a one-variable fraction. -/
lemma counterexample_rowWeight_zero :
    counterexampleProgram.rowWeight counterexampleU counterexampleV (0 : Fin 2) =
      Real.exp (-100) / (Real.exp (-100) + 1) := by
  -- Unfold the explicit `2 × 2` data and cancel the common factor `2`.
  simp [EquivalentGeometricConvexProgram.rowWeight,
    EquivalentGeometricConvexProgram.geometricObjective, EquivalentGeometricConvexProgram.xOfU,
    EquivalentGeometricConvexProgram.yOfV, counterexampleProgram, counterexampleU, counterexampleV,
    Fin.sum_univ_two]
  field_simp [Real.exp_ne_zero]

/-- The counterexample point violates the row-weight conclusion of the main theorem. -/
lemma counterexample_rowWeight_zero_ne_c :
    counterexampleProgram.rowWeight counterexampleU counterexampleV (0 : Fin 2) ≠
      counterexampleProgram.c (0 : Fin 2) := by
  -- Rewrite the row weight explicitly and show the resulting fraction is strictly below `1 / 2`.
  rw [counterexample_rowWeight_zero]
  simp [counterexampleProgram]
  intro hEq
  have hexp_lt_one : Real.exp (-100 : ℝ) < 1 := by
    -- A strictly negative exponent yields a strict inequality against `1`.
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num : (-100 : ℝ) < 0)
  have hpos : 0 < Real.exp (-100 : ℝ) + 1 := by positivity
  have hmul : 2 * Real.exp (-100 : ℝ) = Real.exp (-100 : ℝ) + 1 := by
    -- Clear denominators to isolate the impossible identity `exp (-100) = 1`.
    have hEq' := congrArg (fun t : ℝ => t * (2 * (Real.exp (-100 : ℝ) + 1))) hEq
    field_simp [hpos.ne'] at hEq'
    linarith
  have hexp_eq_one : Real.exp (-100 : ℝ) = 1 := by linarith
  exact (lt_irrefl (Real.exp (-100 : ℝ))) (hexp_eq_one ▸ hexp_lt_one)

/-- The target theorem's conclusion already fails on the explicit counterexample point. -/
lemma counterexample_conclusion_fails :
    ¬ ((∀ i : Fin 2,
          counterexampleProgram.rowWeight counterexampleU counterexampleV i =
            counterexampleProgram.c i) ∧
        (∀ j : Fin 2,
          counterexampleProgram.colWeight counterexampleU counterexampleV j =
            counterexampleProgram.d j) ∧
        (∀ i : Fin 2,
          ∑ j : Fin 2, counterexampleProgram.scaledMatrix counterexampleU counterexampleV i j =
            counterexampleProgram.c i) ∧
        (∀ j : Fin 2,
          ∑ i : Fin 2, counterexampleProgram.scaledMatrix counterexampleU counterexampleV i j =
            counterexampleProgram.d j)) := by
  -- The first conjunct already contradicts the explicit row-weight computation at `i = 0`.
  intro hConclusion
  exact counterexample_rowWeight_zero_ne_c (hConclusion.1 (0 : Fin 2))

/-- The full universal theorem statement is refuted by the explicit counterexample above. -/
private lemma optimality_conditions_statement_false :
    ¬
      (∀ (P : EquivalentGeometricConvexProgram)
        (_hn : 0 < P.n)
        (_hApos : ∀ i j : Fin P.n, 0 < P.A i j)
        (_hcpos : ∀ i : Fin P.n, 0 < P.c i)
        (_hdpos : ∀ j : Fin P.n, 0 < P.d j)
        (_hcsum : ∑ i : Fin P.n, P.c i = 1)
        (_hdsum : ∑ j : Fin P.n, P.d j = 1)
        (u v : Fin P.n → ℝ)
        (_hopt :
          IsMinOn
            (fun uv : (Fin P.n → ℝ) × (Fin P.n → ℝ) => P.phi uv.1 uv.2)
            {uv | P.convexFeasible uv}
            (u, v)),
        (∀ i : Fin P.n, P.rowWeight u v i = P.c i) ∧
        (∀ j : Fin P.n, P.colWeight u v j = P.d j) ∧
        (∀ i : Fin P.n, ∑ j : Fin P.n, P.scaledMatrix u v i j = P.c i) ∧
        (∀ j : Fin P.n, ∑ i : Fin P.n, P.scaledMatrix u v i j = P.d j)) := by
  intro hAll
  -- Specialize the claimed universal statement to the concrete `2 × 2` program.
  have hn : 0 < counterexampleProgram.n := by
    simp [counterexampleProgram]
  have hApos : ∀ i j : Fin counterexampleProgram.n, 0 < counterexampleProgram.A i j := by
    intro i j
    simp [counterexampleProgram]
  have hcpos : ∀ i : Fin counterexampleProgram.n, 0 < counterexampleProgram.c i := by
    intro i
    simp [counterexampleProgram]
  have hdpos : ∀ j : Fin counterexampleProgram.n, 0 < counterexampleProgram.d j := by
    intro j
    simp [counterexampleProgram]
  have hcsum : ∑ i : Fin counterexampleProgram.n, counterexampleProgram.c i = 1 := by
    simp [counterexampleProgram]
  have hdsum : ∑ j : Fin counterexampleProgram.n, counterexampleProgram.d j = 1 := by
    simp [counterexampleProgram]
  have hConclusion :=
    hAll counterexampleProgram hn hApos hcpos hdpos hcsum hdsum
      counterexampleU counterexampleV counterexample_isMinOn
  -- The specialized conclusion contradicts the explicit row-weight computation at `i = 0`.
  exact counterexample_conclusion_fails hConclusion

/-
Let (A in mathbf{R}^{n \times n}) have strictly positive entries, and let (c, d in mathbf{R}^n) be
strictly positive vectors such that (mathbf{1}^T c = 1) and (mathbf{1}^T d = 1), where (
mathbf{1} in mathbf{R}^n) is the all - ones vector. For (z in mathbf{R}^n), let (
operatorname{diag}(z)) denote the diagonal matrix with diagonal entries (z_1, ..., z_n). For (u, v
in mathbf{R}^n), define [ phi(u, v) = log !(\sum_{i = 1}^n\sum_{j = 1}^n A_{ij} e^{u_i + v_j}). ]
Consider the convexified problem of minimizing phi subject to
\sum_i c_i u_i = 0 and \sum_j d_j v_j = 0. If ((u, v)) is optimal and
x_i = e^{u_i}, y_j = e^{v_j}, then the first-order optimality conditions imply
[
  \frac{x_i (Ay)_i}{x^T A y} = c_i,\qquad
  \frac{y_j (A^T x)_j}{x^T A y} = d_j.
]
Equivalently, for B = diag(x) A diag(y) / (x^T A y), one has
B 1 = c and B^T 1 = d.
-/
theorem optimality_conditions_for_equivalent_geometric_convex_program
    (P : EquivalentGeometricConvexProgram)
    (hn : 0 < P.n)
    (hApos : ∀ i j : Fin P.n, 0 < P.A i j)
    (hcpos : ∀ i : Fin P.n, 0 < P.c i)
    (hdpos : ∀ j : Fin P.n, 0 < P.d j)
    (hcsum : ∑ i : Fin P.n, P.c i = 1)
    (hdsum : ∑ j : Fin P.n, P.d j = 1)
    (u v : Fin P.n → ℝ)
    (hopt :
      IsMinOn
        (fun uv : (Fin P.n → ℝ) × (Fin P.n → ℝ) => P.phi uv.1 uv.2)
        {uv | P.convexFeasible uv}
        (u, v)) :
    (∀ i : Fin P.n, P.rowWeight u v i = P.c i) ∧
    (∀ j : Fin P.n, P.colWeight u v j = P.d j) ∧
    (∀ i : Fin P.n, ∑ j : Fin P.n, P.scaledMatrix u v i j = P.c i) ∧
    (∀ j : Fin P.n, ∑ i : Fin P.n, P.scaledMatrix u v i j = P.d j) := by
  -- Route correction: `IsMinOn` over `{uv | P.convexFeasible uv}` does not imply
  -- `P.convexFeasible (u, v)`, so the old route incorrectly tried to read feasibility equations
  -- off the minimizer witness itself.
  -- The statement-level obstruction is already formalized by
  -- `optimality_conditions_statement_false`, obtained by specializing to
  -- `counterexampleProgram`, `counterexampleU`, and `counterexampleV`.
  -- That private lemma packages the contradiction for the exact universal theorem shape stated
  -- here, so the issue is not a local missing tactic or missing rewrite inside this proof block.
  -- In other words, the exact universal shape of this theorem has already been refuted in-file.
  -- At that witness, `counterexample_isMinOn` supplies the stated optimization hypothesis,
  -- `counterexample_not_convexFeasible` shows the witness is not feasible, and
  -- `counterexample_conclusion_fails` contradicts the desired conclusion at `i = 0` via the
  -- Lean-checkable conflict `counterexample_rowWeight_zero_ne_c (hConclusion.1 0)`.
  -- A proof term here would therefore manufacture a witness contradicting
  -- `optimality_conditions_statement_false`.
  -- The missing assumption is that the minimizer witness itself satisfies
  -- `P.convexFeasible (u, v)`.
  -- Terminal diagnosis: the obstruction is statement-level, not a local proof-search gap.
  -- So no proof term can close this goal without changing the theorem statement.
  -- TODO: Repair the statement upstream by requiring `P.convexFeasible (u, v)` before attempting
  -- any KKT-style first-order optimality argument.
  -- No proof term can close this goal for the current statement.
  sorry

end «problem-20»
