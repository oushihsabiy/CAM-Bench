import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-154»

/- [BLOCK Exercise 16.4 | 5 | defn]
For a feasible point x with equality-index set E and inequality-index set I, the active set is
A(x)=Ecup{i∈I:a_iᵀ x=bᵢ}.
It consists of all equality constraints and all inequality constraints that are active at x.
-/
def activeSet {ι : Type*} (equalities inequalities : Set ι) (a : ι → Fin n → ℝ) (b : ι → ℝ)
    (x : Fin n → ℝ) : Set ι :=
  equalities ∪ {i | i ∈ inequalities ∧ ∑ j, a i j * x j = b i}

/- [BLOCK Exercise 16.4 | 6 | defn]
A point x is feasible if it satisfies all constraints of the problem, that is, a_iᵀ x=bᵢ for all i∈E
and a_iᵀ x≥ bᵢ for all i∈I.
-/
def feasiblePoint {n : ℕ} {ι : Type*} (equalities inequalities : Set ι) (a : ι → Fin n → ℝ)
    (b : ι → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i, i ∈ equalities → ∑ j, a i j * x j = b i) ∧
    ∀ i, i ∈ inequalities → ∑ j, a i j * x j ≥ b i

/- [BLOCK Exercise 16.4 | 7 | defn]
A multiplier for a constraint system is a scalar coefficient λ_i associated with constraint i. A
vector of multipliers appears in first-order optimality conditions through a linear combination of
the constraint normals, for example,
∇ f(x)-sum_i λ_i aᵢ=0.
-/
def multiplier (ι : Type*) := ι → ℝ

/- [BLOCK Exercise 16.4 | 8 | defn]
A feasible point x* is a global solution if f(x*)≤ f(x) for every feasible x. It is unique if,
moreover, f(x*)< f(x) for every feasible xne x*.
-/
def isGlobalSolution {n : ℕ} {ι : Type*} (f : (Fin n → ℝ) → ℝ) (equalities inequalities : Set ι)
    (a : ι → Fin n → ℝ) (b : ι → ℝ) (xStar : Fin n → ℝ) : Prop :=
  feasiblePoint equalities inequalities a b xStar ∧
    ∀ x, feasiblePoint equalities inequalities a b x → f xStar ≤ f x

def isUniqueGlobalSolution {n : ℕ} {ι : Type*} (f : (Fin n → ℝ) → ℝ) (equalities inequalities : Set ι)
    (a : ι → Fin n → ℝ) (b : ι → ℝ) (xStar : Fin n → ℝ) : Prop :=
  feasiblePoint equalities inequalities a b xStar ∧
    ∀ x, feasiblePoint equalities inequalities a b x → x ≠ xStar → f xStar < f x

/- [BLOCK Exercise 16.4 | 9 | opt_prob]
Consider the quadratic program
aligned
min_{x ∈ ℝ^n} quad & q(x)=(1)/(2)xᵀ G x + cᵀ x ;
subject to quad & a_iᵀ x = bᵢ, quad i ∈ E, ;
& a_iᵀ x ≥ bᵢ, quad i ∈ I,
aligned
where G ∈ ℝ^{n×n} is symmetric positive semidefinite, c ∈ ℝ^n, and aᵢ ∈ ℝ^n, bᵢ ∈ ℝ for each i ∈ E
cup I.
-/
structure ConvexQuadraticProgram (n : ℕ) (ι : Type*) where
  G : Matrix (Fin n) (Fin n) ℝ
  c : Fin n → ℝ
  equalities : Set ι
  inequalities : Set ι
  a : ι → Fin n → ℝ
  b : ι → ℝ
  G_symmetric : G.IsSymm
  G_posSemidef : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, x i * G i j * x j

def ConvexQuadraticProgram.objective {n : ℕ} {ι : Type*} (P : ConvexQuadraticProgram n ι)
    (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, x i * P.G i j * x j + ∑ i, P.c i * x i

def ConvexQuadraticProgram.isFeasible {n : ℕ} {ι : Type*} (P : ConvexQuadraticProgram n ι)
    (x : Fin n → ℝ) : Prop :=
  feasiblePoint P.equalities P.inequalities P.a P.b x

def ConvexQuadraticProgram.activeSet {n : ℕ} {ι : Type*} (P : ConvexQuadraticProgram n ι)
    (x : Fin n → ℝ) : Set ι :=
  {i | i ∈ P.inequalities ∧ ∑ j, P.a i j * x j = P.b i}

variable {n : ℕ} {ι κ : Type*}

/-- Rewriting the stationarity contribution in terms of the objective-gap direction. -/
lemma stationary_weighted_direction
    [Fintype ι] [DecidableEq ι]
    (P : ConvexQuadraticProgram n ι) (xStar x : Fin n → ℝ) (lam : multiplier ι)
    (hstationary :
      ∀ j, ∑ i, lam i * P.a i j = ∑ k, P.G j k * xStar k + P.c j) :
    let d : Fin n → ℝ := fun j => x j - xStar j
    d ⬝ᵥ (P.G *ᵥ xStar) + P.c ⬝ᵥ d = ∑ i, lam i * ∑ j, P.a i j * d j := by
  let d : Fin n → ℝ := fun j => x j - xStar j
  -- Rewrite the linear term using stationarity, then swap the finite sums.
  calc
    d ⬝ᵥ (P.G *ᵥ xStar) + P.c ⬝ᵥ d
        = ∑ j, d j * ((∑ k, P.G j k * xStar k) + P.c j) := by
            rw [dotProduct_comm P.c d]
            simp [d, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_add_distrib,
              left_distrib]
    _ = ∑ j, d j * (∑ i, lam i * P.a i j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [← hstationary j]
    _ = ∑ i, lam i * ∑ j, P.a i j * d j := by
          calc
            ∑ j, d j * (∑ i, lam i * P.a i j)
                = ∑ j, ∑ i, d j * (lam i * P.a i j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    rw [Finset.mul_sum]
            _ = ∑ j, ∑ i, d j * (lam i * P.a i j)
                := rfl
            _ = ∑ i, ∑ j, d j * (lam i * P.a i j) := by
                    rw [Finset.sum_comm]
            _ = ∑ i, ∑ j, lam i * (P.a i j * d j) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
            _ = ∑ i, lam i * ∑ j, P.a i j * d j := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  rw [← Finset.mul_sum]

/-- The mixed quadratic terms coincide because the Hessian matrix is symmetric. -/
lemma symmetric_cross_term
    (P : ConvexQuadraticProgram n ι) (xStar d : Fin n → ℝ) :
    xStar ⬝ᵥ (P.G *ᵥ d) = d ⬝ᵥ (P.G *ᵥ xStar) := by
  -- Expand both sides as double sums and swap the indices using symmetry of `G`.
  calc
    xStar ⬝ᵥ (P.G *ᵥ d) = ∑ i, ∑ j, xStar i * P.G i j * d j := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    _ = ∑ j, ∑ i, d j * P.G j i * xStar i := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [P.G_symmetric.apply i j]
          ring
    _ = d ⬝ᵥ (P.G *ᵥ xStar) := by
          simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- The objective gap splits into a weighted slack term plus the quadratic remainder in the
displacement from `xStar`. -/
lemma objective_gap_as_weighted_slack_plus_quadratic
    [Fintype ι] [DecidableEq ι]
    (P : ConvexQuadraticProgram n ι) (xStar x : Fin n → ℝ) (lam : multiplier ι)
    (hlam_support : ∀ i, i ∉ activeSet P.equalities P.inequalities P.a P.b xStar → lam i = 0)
    (hstationary :
      ∀ j, ∑ i, lam i * P.a i j = ∑ k, P.G j k * xStar k + P.c j)
    (hactive_eq :
      ∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar → ∑ j, P.a i j * xStar j = P.b i) :
    P.objective x - P.objective xStar =
      (∑ i, lam i * (∑ j, P.a i j * x j - P.b i)) +
        (1 / 2 : ℝ) * ∑ j, ∑ k, (x j - xStar j) * P.G j k * (x k - xStar k) := by
  let d : Fin n → ℝ := fun j => x j - xStar j
  have hxdecomp : x = xStar + d := by
    -- Express `x` as the base point plus its displacement.
    funext j
    simp [d]
  have hObjective (y : Fin n → ℝ) :
      P.objective y = (1 / 2 : ℝ) * (y ⬝ᵥ (P.G *ᵥ y)) + P.c ⬝ᵥ y := by
    -- Rewrite the objective using dot products so additivity can expand it cleanly.
    simp [ConvexQuadraticProgram.objective, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hstationaryDir :
      d ⬝ᵥ (P.G *ᵥ xStar) + P.c ⬝ᵥ d = ∑ i, lam i * ∑ j, P.a i j * d j := by
    simpa [d] using stationary_weighted_direction P xStar x lam hstationary
  have hweighted :
      ∑ i, lam i * ∑ j, P.a i j * d j =
        ∑ i, lam i * (∑ j, P.a i j * x j - P.b i) := by
    -- Active constraints use the equality at `xStar`; inactive ones have zero multiplier.
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hiActive : i ∈ activeSet P.equalities P.inequalities P.a P.b xStar
    · have hdiff :
          ∑ j, P.a i j * d j = ∑ j, P.a i j * x j - P.b i := by
        calc
          ∑ j, P.a i j * d j = ∑ j, (P.a i j * x j - P.a i j * xStar j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [d, mul_sub]
          _ = (∑ j, P.a i j * x j) - ∑ j, P.a i j * xStar j := by
            rw [Finset.sum_sub_distrib]
          _ = ∑ j, P.a i j * x j - P.b i := by
            rw [hactive_eq i hiActive]
      rw [hdiff]
    · rw [hlam_support i hiActive, zero_mul, zero_mul]
  -- Expand the quadratic term around `xStar`, merge the mixed terms, and then invoke stationarity.
  calc
    P.objective x - P.objective xStar
        = ((1 / 2 : ℝ) * ((xStar + d) ⬝ᵥ (P.G *ᵥ (xStar + d))) + P.c ⬝ᵥ (xStar + d)) -
            ((1 / 2 : ℝ) * (xStar ⬝ᵥ (P.G *ᵥ xStar)) + P.c ⬝ᵥ xStar) := by
              rw [hObjective x, hObjective xStar, hxdecomp]
    _ = ((1 / 2 : ℝ) *
          (xStar ⬝ᵥ (P.G *ᵥ xStar) + d ⬝ᵥ (P.G *ᵥ xStar) +
            (xStar ⬝ᵥ (P.G *ᵥ d) + d ⬝ᵥ (P.G *ᵥ d))) +
          (P.c ⬝ᵥ xStar + P.c ⬝ᵥ d)) -
          ((1 / 2 : ℝ) * (xStar ⬝ᵥ (P.G *ᵥ xStar)) + P.c ⬝ᵥ xStar) := by
            rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, dotProduct_add, add_dotProduct]
    _ = d ⬝ᵥ (P.G *ᵥ xStar) + P.c ⬝ᵥ d +
          (1 / 2 : ℝ) * (d ⬝ᵥ (P.G *ᵥ d)) := by
            rw [symmetric_cross_term P xStar d]
            ring_nf
    _ = ∑ i, lam i * ∑ j, P.a i j * d j +
          (1 / 2 : ℝ) * (∑ j, ∑ k, d j * P.G j k * d k) := by
            rw [hstationaryDir]
            simp [d, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    _ = (∑ i, lam i * (∑ j, P.a i j * x j - P.b i)) +
          (1 / 2 : ℝ) * ∑ j, ∑ k, d j * P.G j k * d k := by
            rw [hweighted]
    _ = (∑ i, lam i * (∑ j, P.a i j * x j - P.b i)) +
          (1 / 2 : ℝ) * ∑ j, ∑ k, (x j - xStar j) * P.G j k * (x k - xStar k) := by
            simp [d]

/-- Each weighted slack term is nonnegative for a feasible point. -/
lemma weighted_slack_term_nonnegative
    [Fintype ι] [DecidableEq ι]
    (P : ConvexQuadraticProgram n ι) (xStar x : Fin n → ℝ) (lam : multiplier ι)
    (hx : P.isFeasible x)
    (hlam_support : ∀ i, i ∉ activeSet P.equalities P.inequalities P.a P.b xStar → lam i = 0)
    (hlam_active_ineq_pos :
      ∀ i, i ∈ P.inequalities →
        i ∈ activeSet P.equalities P.inequalities P.a P.b xStar →
          0 < lam i)
    (i : ι) :
    0 ≤ lam i * (∑ j, P.a i j * x j - P.b i) := by
  -- Split by whether the constraint is active at `xStar`; inactive terms vanish.
  by_cases hiActive : i ∈ activeSet P.equalities P.inequalities P.a P.b xStar
  · by_cases hiEq : i ∈ P.equalities
    · have hxEq : ∑ j, P.a i j * x j = P.b i := hx.1 i hiEq
      rw [hxEq]
      simp
    · have hiIneq : i ∈ P.inequalities := by
        rcases (by simpa [activeSet] using hiActive) with hEq | hIneq
        · exact False.elim (hiEq hEq)
        · exact hIneq.1
      have hSlackNonneg : 0 ≤ ∑ j, P.a i j * x j - P.b i := by
        exact sub_nonneg.mpr (hx.2 i hiIneq)
      exact mul_nonneg (le_of_lt (hlam_active_ineq_pos i hiIneq hiActive)) hSlackNonneg
  · rw [hlam_support i hiActive]
    simp

/-- The total weighted slack is nonnegative at any feasible point. -/
lemma weighted_slack_sum_nonnegative
    [Fintype ι] [DecidableEq ι]
    (P : ConvexQuadraticProgram n ι) (xStar x : Fin n → ℝ) (lam : multiplier ι)
    (hx : P.isFeasible x)
    (hlam_support : ∀ i, i ∉ activeSet P.equalities P.inequalities P.a P.b xStar → lam i = 0)
    (hlam_active_ineq_pos :
      ∀ i, i ∈ P.inequalities →
        i ∈ activeSet P.equalities P.inequalities P.a P.b xStar →
          0 < lam i) :
    0 ≤ ∑ i, lam i * (∑ j, P.a i j * x j - P.b i) := by
  -- Sum the pointwise nonnegative weighted slack terms.
  refine Finset.sum_nonneg ?_
  intro i hi
  exact weighted_slack_term_nonnegative P xStar x lam hx hlam_support hlam_active_ineq_pos i

/-- A strictly positive slack on an active inequality forces the weighted slack sum to be strictly
positive. -/
lemma strict_active_slack_forces_positive_weighted_sum
    [Fintype ι] [DecidableEq ι]
    (P : ConvexQuadraticProgram n ι) (xStar x : Fin n → ℝ) (lam : multiplier ι)
    (hx : P.isFeasible x)
    (hlam_support : ∀ i, i ∉ activeSet P.equalities P.inequalities P.a P.b xStar → lam i = 0)
    (hlam_active_ineq_pos :
      ∀ i, i ∈ P.inequalities →
        i ∈ activeSet P.equalities P.inequalities P.a P.b xStar →
          0 < lam i)
    (hstrict :
      ∃ i, i ∈ P.inequalities ∧
        i ∈ activeSet P.equalities P.inequalities P.a P.b xStar ∧
          0 < ∑ j, P.a i j * x j - P.b i) :
    0 < ∑ i, lam i * (∑ j, P.a i j * x j - P.b i) := by
  rcases hstrict with ⟨i0, hi0Ineq, hi0Active, hi0Slack⟩
  -- One strictly positive term plus nonnegative remainder makes the total sum positive.
  refine Finset.sum_pos' ?_ ?_
  · intro i hi
    exact weighted_slack_term_nonnegative P xStar x lam hx hlam_support hlam_active_ineq_pos i
  · refine ⟨i0, Finset.mem_univ i0, ?_⟩
    exact mul_pos (hlam_active_ineq_pos i0 hi0Ineq hi0Active) hi0Slack

/-- If every active inequality keeps zero slack, then the displacement from `xStar` has a nonzero
representation in the active-set nullspace basis. -/
lemma zero_active_slack_yields_nonzero_Z_coordinates
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : ConvexQuadraticProgram n ι) (xStar x : Fin n → ℝ) (Z : κ → Fin n → ℝ)
    (hx : P.isFeasible x) (hxNe : x ≠ xStar)
    (hactive_eq :
      ∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar → ∑ j, P.a i j * xStar j = P.b i)
    (hZbasis :
      ∀ d : Fin n → ℝ,
        (∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar → ∑ j, P.a i j * d j = 0) →
        ∃ mu : κ → ℝ, d = fun j => ∑ i, Z i j * mu i)
    (hzero :
      ∀ i, i ∈ P.inequalities →
        i ∈ activeSet P.equalities P.inequalities P.a P.b xStar →
          ∑ j, P.a i j * x j - P.b i = 0) :
    ∃ mu : κ → ℝ, mu ≠ 0 ∧ (fun j => x j - xStar j) = fun j => ∑ i, Z i j * mu i := by
  let d : Fin n → ℝ := fun j => x j - xStar j
  have hdActive :
      ∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar → ∑ j, P.a i j * d j = 0 := by
    intro i hi
    -- Active equalities vanish by feasibility; active inequalities vanish by the branch hypothesis.
    by_cases hiEq : i ∈ P.equalities
    · calc
        ∑ j, P.a i j * d j = ∑ j, (P.a i j * x j - P.a i j * xStar j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [d, mul_sub]
        _ = (∑ j, P.a i j * x j) - ∑ j, P.a i j * xStar j := by
          rw [Finset.sum_sub_distrib]
        _ = P.b i - P.b i := by
          rw [hx.1 i hiEq, hactive_eq i hi]
        _ = 0 := by ring
    · have hiIneq : i ∈ P.inequalities := by
        rcases (by simpa [activeSet] using hi) with hEq | hIneq
        · exact False.elim (hiEq hEq)
        · exact hIneq.1
      calc
        ∑ j, P.a i j * d j = ∑ j, (P.a i j * x j - P.a i j * xStar j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [d, mul_sub]
        _ = (∑ j, P.a i j * x j) - ∑ j, P.a i j * xStar j := by
          rw [Finset.sum_sub_distrib]
        _ = P.b i - P.b i := by
          have hxEq : ∑ j, P.a i j * x j = P.b i := by
            linarith [hzero i hiIneq hi]
          rw [hxEq, hactive_eq i hi]
        _ = 0 := by ring
  obtain ⟨mu, hmu⟩ := hZbasis d hdActive
  refine ⟨mu, ?_, hmu⟩
  intro hmuZero
  apply hxNe
  -- A zero coefficient vector would force the displacement itself to vanish.
  funext j
  have hrepr := congrArg (fun f => f j) hmu
  simp [d, hmuZero] at hrepr
  linarith

/- [BLOCK Exercise 16.4 | 10 | thm]
Consider the convex quadratic program. Let x* be a feasible point, and define its active set by
A(x*) = E cup { i ∈ I : a_iᵀ x* = bᵢ }. Assume there exist multipliers λ_i* ∈ ℝ for i ∈ A(x*) such
that
Gx* + c - sum_{i ∈ A(x*)} λ_i* aᵢ = 0,
a_iᵀ x* = bᵢ quad for all i ∈ A(x*).
Let A_{A(x*)} be the matrix whose rows are a_iᵀ for i ∈ A(x*), and let the columns of Z form a basis
of
{ d ∈ ℝ^n : A_{A(x*)} d = 0 }.
Assume that Zᵀ G Z is positive definite. Show that x* is the unique global solution of the quadratic
program, namely,
q(x) > q(x*) quad for every feasible x ≠ x*.
-/
theorem unique_global_solution_of_kkt_activeSet_posDef
    {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : ConvexQuadraticProgram n ι) (xStar : Fin n → ℝ) (Z : κ → Fin n → ℝ)
    (lam : multiplier ι)
    (hxFeas : P.isFeasible xStar)
    (hlam_support : ∀ i, i ∉ activeSet P.equalities P.inequalities P.a P.b xStar → lam i = 0)
    (hlam_active_ineq_pos :
      ∀ i, i ∈ P.inequalities →
        i ∈ activeSet P.equalities P.inequalities P.a P.b xStar →
          0 < lam i)
    (hstationary :
      ∀ j, ∑ i, lam i * P.a i j = ∑ k, P.G j k * xStar k + P.c j)
    (hactive_eq :
      ∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar → ∑ j, P.a i j * xStar j = P.b i)
    (hZbasis :
      (∀ d : Fin n → ℝ,
        (∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar → ∑ j, P.a i j * d j = 0) →
        ∃ mu : κ → ℝ, d = fun j => ∑ i, Z i j * mu i) ∧
      (∀ mu : κ → ℝ,
        ∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar →
          ∑ j, P.a i j * (∑ k, Z k j * mu k) = 0) ∧
      (∀ mu : κ → ℝ,
        (∀ j, (∑ i, Z i j * mu i) = 0) →
        mu = 0))
    (hposdef :
      ∀ mu : κ → ℝ, mu ≠ 0 →
        0 < ∑ j, ∑ k, (∑ i, Z i j * mu i) * P.G j k * (∑ i, Z i k * mu i)) :
    isUniqueGlobalSolution P.objective P.equalities P.inequalities P.a P.b xStar := by
  constructor
  · exact hxFeas
  · intro x hx hxNe
    have hgap :
        P.objective x - P.objective xStar =
          (∑ i, lam i * (∑ j, P.a i j * x j - P.b i)) +
            (1 / 2 : ℝ) * ∑ j, ∑ k, (x j - xStar j) * P.G j k * (x k - xStar k) := by
      -- First rewrite the objective difference into the KKT-weighted slack form.
      exact objective_gap_as_weighted_slack_plus_quadratic P xStar x lam hlam_support
        hstationary hactive_eq
    by_cases hstrict :
        ∃ i, i ∈ P.inequalities ∧
          i ∈ activeSet P.equalities P.inequalities P.a P.b xStar ∧
            0 < ∑ j, P.a i j * x j - P.b i
    · have hlinPos :
          0 < ∑ i, lam i * (∑ j, P.a i j * x j - P.b i) := by
        -- A positive active slack gives strict positivity of the linear contribution.
        exact strict_active_slack_forces_positive_weighted_sum P xStar x lam hx hlam_support
          hlam_active_ineq_pos hstrict
      have hquadNonneg :
          0 ≤ (1 / 2 : ℝ) * ∑ j, ∑ k, (x j - xStar j) * P.G j k * (x k - xStar k) := by
        -- The quadratic remainder is nonnegative by positive semidefiniteness of `G`.
        have hpsd := P.G_posSemidef (fun j => x j - xStar j)
        nlinarith
      have hdiffPos : 0 < P.objective x - P.objective xStar := by
        linarith [hgap, hlinPos, hquadNonneg]
      linarith
    · have hzeroActive :
          ∀ i, i ∈ P.inequalities →
            i ∈ activeSet P.equalities P.inequalities P.a P.b xStar →
              ∑ j, P.a i j * x j - P.b i = 0 := by
        intro i hiIneq hiActive
        -- In the complementary branch, active inequalities cannot have positive slack.
        have hSlackNonneg : 0 ≤ ∑ j, P.a i j * x j - P.b i := by
          exact sub_nonneg.mpr (hx.2 i hiIneq)
        have hNotPos : ¬ 0 < ∑ j, P.a i j * x j - P.b i := by
          intro hpos
          exact hstrict ⟨i, hiIneq, hiActive, hpos⟩
        linarith
      obtain ⟨mu, hmuNe, hrepr⟩ :=
        zero_active_slack_yields_nonzero_Z_coordinates P xStar x Z hx hxNe hactive_eq hZbasis.1
          hzeroActive
      have hlinZero :
          ∑ i, lam i * (∑ j, P.a i j * x j - P.b i) = 0 := by
        -- Every summand vanishes: active constraints have zero slack, inactive ones zero multiplier.
        refine Finset.sum_eq_zero ?_
        intro i hi
        by_cases hiActive : i ∈ activeSet P.equalities P.inequalities P.a P.b xStar
        · by_cases hiEq : i ∈ P.equalities
          · have hxEq : ∑ j, P.a i j * x j = P.b i := hx.1 i hiEq
            rw [hxEq]
            simp
          · have hiIneq : i ∈ P.inequalities := by
              rcases (by simpa [activeSet] using hiActive) with hEq | hIneq
              · exact False.elim (hiEq hEq)
              · exact hIneq.1
            rw [hzeroActive i hiIneq hiActive]
            simp
        · rw [hlam_support i hiActive]
          simp
      have hquadStrict :
          0 < (1 / 2 : ℝ) * ∑ j, ∑ k, (x j - xStar j) * P.G j k * (x k - xStar k) := by
        -- The nullspace representation turns the quadratic remainder into a positive-definite form.
        have hraw :
            0 < ∑ j, ∑ k, (∑ i, Z i j * mu i) * P.G j k * (∑ i, Z i k * mu i) :=
          hposdef mu hmuNe
        have hrepr_point : ∀ j, x j - xStar j = ∑ i, Z i j * mu i := by
          intro j
          exact congrArg (fun f => f j) hrepr
        have hquad :
            0 < ∑ j, ∑ k, (x j - xStar j) * P.G j k * (x k - xStar k) := by
          simpa [hrepr_point] using hraw
        nlinarith
      have hdiffPos : 0 < P.objective x - P.objective xStar := by
        rw [hgap, hlinZero]
        nlinarith [hquadStrict]
      linarith

end «problem-154»
