import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-78»
/-
A linear program is an optimization problem of the form cᵀ z: Bz ≤ d, Ez = f (or the corresponding
maximization problem), where the objective function and all constraint functions are affine in the
decision variable z.
-/
structure LinearProgram where
  m : ℕ
  p : ℕ
  n : ℕ
  c : Fin n → ℝ
  B : Matrix (Fin m) (Fin n) ℝ
  d : Fin m → ℝ
  E : Matrix (Fin p) (Fin n) ℝ
  f : Fin p → ℝ

def LinearProgram.objective (P : LinearProgram) (z : Fin P.n → ℝ) : ℝ :=
  dotProduct P.c z

def LinearProgram.IsFeasible (P : LinearProgram) (z : Fin P.n → ℝ) : Prop :=
  (∀ i : Fin P.m, dotProduct (P.B i) z ≤ P.d i) ∧
    ∀ i : Fin P.p, dotProduct (P.E i) z = P.f i

def feasible {P : LinearProgram} (z : Fin P.n → ℝ) : Prop :=
  P.IsFeasible z

/-
The optimal value of a minimization problem f(x): x ∈ C is \inf_{x ∈ C} f(x); if the infimum is
attained, it is equal to f(x*) for any optimizer x*.
-/
def optimalValue {α : Type*} (f : α → ℝ) (C : Set α) : ℝ :=
  sInf (f '' C)

/-
An optimizer of a minimization problem f(x): x ∈ C is a point x* ∈ C such that f(x*) ≤ f(x) for all
x ∈ C.
-/
def optimizer {α : Type*} (f : α → ℝ) (C : Set α) (xStar : α) : Prop :=
  xStar ∈ C ∧ ∀ x ∈ C, f xStar ≤ f x

/-
Consider the optimization problem min_{x∈ℝ^k} ‖A(x)‖_∞.
-/
structure MatrixInfinityNormMinimization where
  m : ℕ
  n : ℕ
  k : ℕ
  A : (Fin k → ℝ) → Fin m → Fin n → ℝ
  objective : (Fin k → ℝ) → ℝ :=
    fun x => sSup (Set.range fun i : Fin m => ∑ j : Fin n, |A x i j|)


/-
Exercise 4.14 | 27 | opt_prob

Consider the linear program

minimize t

subject to −S_{ij} ≤ A(x)_{ij} ≤ S_{ij}, i = 1, …, m, j = 1, …, n, ∑_{j = 1}^n S_{ij} ≤ t, i = 1, …,
m,

with variables x ∈ ℝ^k, S = (S_{ij}) ∈ ℝ^{m×n}, and t ∈ ℝ.
-/
structure EpigraphLinearProgram where
  m : ℕ
  n : ℕ
  k : ℕ
  A : (Fin k → ℝ) → Fin m → Fin n → ℝ

def EpigraphLinearProgram.IsFeasible
    (P : EpigraphLinearProgram)
    (x : Fin P.k → ℝ)
    (S : Fin P.m → Fin P.n → ℝ)
    (t : ℝ) : Prop :=
    (∀ i : Fin P.m, ∀ j : Fin P.n, -S i j ≤ P.A x i j ∧ P.A x i j ≤ S i j) ∧
      ∀ i : Fin P.m, ∑ j : Fin P.n, S i j ≤ t


/-
Let m, n, k ∈ ℕ, let A₀, ..., Aₖ ∈ ℝ^{m × n}, and for x = (x₁, ..., xₖ) ∈ ℝ^k define A(x) =
A₀ + \sum_{ell = 1}^k x_ell A_ell. For a matrix A = (a_{ij}) ∈ ℝ^{m × n}, define ‖A‖_∞ = max_{i =
1, ..., m}\sum_{j = 1}^n |a_{ij}|. Consider the matrix infinity - norm minimization. Prove that this
problem is equivalent to epigraph linear program. More precisely, prove that for every x∈ℝ^k, the
choice S_{ij} = |A(x)_{ij}| and t = ‖A(x)‖_∞ is feasible. Here the auxiliary matrix S gives
entrywise upper bounds on |A(x)_{ij}|, and t gives an upper bound on the maximum row sum max_i
\sum_{j = 1}^n S_{ij}.
-/
theorem epigraph_feasible_of_absolute_value_choice
    (m n k : ℕ)
    (A : (Fin k → ℝ) → Fin m → Fin n → ℝ)
    (x : Fin k → ℝ) :
    let P : EpigraphLinearProgram := { m := m, n := n, k := k, A := A }
    P.IsFeasible x (fun i j => |A x i j|)
      (sSup (Set.range fun i : Fin m => ∑ j : Fin n, |A x i j|)) := by
  -- Unfold the epigraph feasibility conditions for the chosen absolute-value slack matrix and row-sum bound.
  dsimp [EpigraphLinearProgram.IsFeasible]
  constructor
  · -- Each entry is sandwiched between the negative and positive absolute value of that entry.
    intro i j
    constructor
    · exact neg_abs_le (A x i j)
    · exact le_abs_self (A x i j)
  · -- Each row sum is bounded by the supremum of all row sums.
    intro i
    exact le_csSup (Finite.bddAbove_range fun i : Fin m => ∑ j : Fin n, |A x i j|) ⟨i, rfl⟩

/-- Feasibility in the epigraph linear program bounds each entry of `A x` by the corresponding slack variable. -/
lemma epigraph_abs_entry_le_of_feasible
    {P : EpigraphLinearProgram}
    {x : Fin P.k → ℝ}
    {S : Fin P.m → Fin P.n → ℝ}
    {t : ℝ}
    (hfeas : P.IsFeasible x S t) :
    ∀ i : Fin P.m, ∀ j : Fin P.n, |P.A x i j| ≤ S i j := by
  -- Repackage the two-sided feasibility inequalities as an absolute-value bound.
  intro i j
  exact abs_le.mpr (hfeas.1 i j)

/-- Feasibility in the epigraph linear program bounds every absolute row sum by the scalar variable `t`. -/
lemma epigraph_row_sum_abs_le_of_feasible
    {P : EpigraphLinearProgram}
    {x : Fin P.k → ℝ}
    {S : Fin P.m → Fin P.n → ℝ}
    {t : ℝ}
    (hfeas : P.IsFeasible x S t) :
    ∀ i : Fin P.m, (∑ j : Fin P.n, |P.A x i j|) ≤ t := by
  -- Sum the entrywise absolute-value bounds and then use the row constraint from feasibility.
  intro i
  have hsum : ∑ j : Fin P.n, |P.A x i j| ≤ ∑ j : Fin P.n, S i j := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact epigraph_abs_entry_le_of_feasible hfeas i j
  exact le_trans hsum (hfeas.2 i)

/-- The matrix infinity-row-sum objective is nonnegative because every row sum of absolute values is nonnegative. -/
lemma matrixInfinityObjective_nonneg
    (m n k : ℕ)
    (hm : 0 < m)
    (A : (Fin k → ℝ) → Fin m → Fin n → ℝ)
    (x : Fin k → ℝ) :
    0 ≤ sSup (Set.range fun i : Fin m => ∑ j : Fin n, |A x i j|) := by
  let i0 : Fin m := ⟨0, hm⟩
  -- Pick one concrete row to witness that the supremum dominates a nonnegative row sum.
  have hrow_nonneg : 0 ≤ ∑ j : Fin n, |A x i0 j| := by
    exact Finset.sum_nonneg fun j hj => abs_nonneg (A x i0 j)
  have hrow_le :
      (∑ j : Fin n, |A x i0 j|) ≤ sSup (Set.range fun i : Fin m => ∑ j : Fin n, |A x i j|) := by
    exact le_csSup (Finite.bddAbove_range fun i : Fin m => ∑ j : Fin n, |A x i j|) ⟨i0, rfl⟩
  exact le_trans hrow_nonneg hrow_le

/-- Any feasible epigraph point has LP objective at least the original matrix infinity-row-sum objective. -/
lemma matrixInfinityObjective_le_of_epigraph_feasible
    (m n k : ℕ)
    (hm : 0 < m)
    (A : (Fin k → ℝ) → Fin m → Fin n → ℝ)
    {x : Fin k → ℝ}
    {S : Fin m → Fin n → ℝ}
    {t : ℝ}
    (hfeas :
      let P : EpigraphLinearProgram := { m := m, n := n, k := k, A := A }
      P.IsFeasible x S t) :
    sSup (Set.range fun i : Fin m => ∑ j : Fin n, |A x i j|) ≤ t := by
  let P : EpigraphLinearProgram := { m := m, n := n, k := k, A := A }
  have hfeas' : P.IsFeasible x S t := hfeas
  let i0 : Fin m := ⟨0, hm⟩
  -- Bound the supremum by showing every row sum is already bounded by `t`.
  refine csSup_le ?_ ?_
  · exact ⟨∑ j : Fin n, |A x i0 j|, ⟨i0, rfl⟩⟩
  · intro b hb
    rcases hb with ⟨i, rfl⟩
    exact epigraph_row_sum_abs_le_of_feasible hfeas' i

/-
Let m, n, k ∈ ℕ, let A₀, ..., Aₖ ∈ ℝ^{m × n}, and for x = (x₁, ..., xₖ) ∈ ℝ^k define A(x) =
A₀ + \sum_{ell = 1}^k x_ell A_ell. For a matrix A = (a_{ij}) ∈ ℝ^{m × n}, define ‖A‖_∞ = max_{i =
1, ..., m}\sum_{j = 1}^n |a_{ij}|. Consider the matrix infinity - norm minimization. Prove that this
problem is equivalent to epigraph linear program. More precisely, prove that the optimal value of
the linear program is equal to min_{x∈ℝ^k} ‖A(x)‖_∞, and an x - component of an optimal LP solution
is
an optimizer of the original problem. Here the auxiliary matrix S gives entrywise upper bounds on
|A(x)_{ij}|, and t gives an upper bound on the maximum row sum max_i \sum_{j = 1}^n S_{ij}.
-/
theorem epigraph_linear_program_optimal_value_eq_matrix_infinity_norm_min
    (m n k : ℕ)
    (hm : 0 < m)
    (A : (Fin k → ℝ) → Fin m → Fin n → ℝ) :
    let C : Set (Fin k → ℝ) := Set.univ
    let f : (Fin k → ℝ) → ℝ := fun x => sSup (Set.range fun i : Fin m => ∑ j : Fin n, |A x i j|)
    let LPFeasible : Set ((Fin k → ℝ) × (Fin m → Fin n → ℝ) × ℝ) :=
      {p |
        let P : EpigraphLinearProgram :=
          { m := m, n := n, k := k, A := A }
        P.IsFeasible p.1 p.2.1 p.2.2}
    optimalValue (fun p : (Fin k → ℝ) × (Fin m → Fin n → ℝ) × ℝ => p.2.2) LPFeasible =
        optimalValue f C ∧
      ∀ p ∈ LPFeasible,
        optimizer (fun p : (Fin k → ℝ) × (Fin m → Fin n → ℝ) × ℝ => p.2.2) LPFeasible p →
          optimizer f C p.1 := by
  dsimp [optimalValue, optimizer]
  let P : EpigraphLinearProgram := { m := m, n := n, k := k, A := A }
  let f : (Fin k → ℝ) → ℝ := fun x => sSup (Set.range fun i : Fin m => ∑ j : Fin n, |A x i j|)
  let g : ((Fin k → ℝ) × (Fin m → Fin n → ℝ) × ℝ) → ℝ := fun p => p.2.2
  let LPFeasible : Set ((Fin k → ℝ) × (Fin m → Fin n → ℝ) × ℝ) :=
    {p | P.IsFeasible p.1 p.2.1 p.2.2}
  have hF_nonempty : (f '' Set.univ).Nonempty := by
    -- The original objective is defined on all `x`, so its image over `Set.univ` is nonempty.
    refine ⟨f (fun _ => 0), ?_⟩
    exact ⟨fun _ => 0, Set.mem_univ _, rfl⟩
  have hLP_of_abs_choice : ∀ x : Fin k → ℝ, (x, (fun i j => |A x i j|), f x) ∈ LPFeasible := by
    -- The canonical absolute-value slack matrix yields a feasible epigraph point for every `x`.
    intro x
    simpa [LPFeasible, P, f] using epigraph_feasible_of_absolute_value_choice m n k A x
  have hsubset : f '' Set.univ ⊆ g '' LPFeasible := by
    -- Every original objective value is realized by a canonical feasible LP point.
    intro y hy
    rcases hy with ⟨x, -, rfl⟩
    exact ⟨(x, (fun i j => |A x i j|), f x), hLP_of_abs_choice x, rfl⟩
  have hF_bdd : BddBelow (f '' Set.univ) := by
    -- The original objective is bounded below by `0`.
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨x, -, rfl⟩
    exact matrixInfinityObjective_nonneg m n k hm A x
  have hG_nonempty : (g '' LPFeasible).Nonempty := by
    -- A feasible LP point is obtained by applying the absolute-value construction at `x = 0`.
    refine ⟨f (fun _ => 0), ?_⟩
    exact ⟨((fun _ => 0), (fun i j => |A (fun _ => 0) i j|), f (fun _ => 0)), hLP_of_abs_choice (fun _ => 0), rfl⟩
  have hG_bdd : BddBelow (g '' LPFeasible) := by
    -- Feasible LP objective values are also bounded below by `0`.
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    have hp_lower :
        f p.1 ≤ p.2.2 := by
      simpa [f] using matrixInfinityObjective_le_of_epigraph_feasible m n k hm A hp
    exact le_trans (matrixInfinityObjective_nonneg m n k hm A p.1) hp_lower
  refine ⟨?_, ?_⟩
  · -- Route correction: instead of comparing the two infima abstractly, compare their image sets directly.
    apply le_antisymm
    · exact csInf_le_csInf hG_bdd hF_nonempty hsubset
    · refine le_csInf hG_nonempty ?_
      intro t ht
      rcases ht with ⟨p, hp, rfl⟩
      have hp_lower :
          f p.1 ≤ p.2.2 := by
        simpa [f] using matrixInfinityObjective_le_of_epigraph_feasible m n k hm A hp
      have hp_mem : f p.1 ∈ f '' Set.univ := by
        exact ⟨p.1, Set.mem_univ _, rfl⟩
      exact le_trans (csInf_le hF_bdd hp_mem) hp_lower
  · -- Project an LP optimizer to its `x`-component and compare against the canonical feasible point of any `x`.
    intro p hp hopt
    rcases hopt with ⟨_, hp_optimal⟩
    refine ⟨by simp, ?_⟩
    intro x hx
    have hp_lower :
        f p.1 ≤ p.2.2 := by
      simpa [f] using matrixInfinityObjective_le_of_epigraph_feasible m n k hm A hp
    have hcanonical :
        (x, (fun i j => |A x i j|), f x) ∈ LPFeasible := hLP_of_abs_choice x
    have hp_upper : p.2.2 ≤ f x := by
      simpa [g, f] using hp_optimal (x, (fun i j => |A x i j|), f x) hcanonical
    exact le_trans hp_lower hp_upper

end «problem-78»
