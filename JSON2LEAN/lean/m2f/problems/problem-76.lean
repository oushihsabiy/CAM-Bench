import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-76»
/-
For the mean-variance reduction below, full Gaussianity is stronger than necessary. What is needed
is the second-moment identity for every scalar projection: aᵀc has mean aᵀμ and variance aᵀΣa.
This avoids pretending that a first/second-moment condition is a complete definition of a normal law.
-/
def HasMeanVariance {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : Ω → ℝ) (μ var : ℝ) : Prop :=
  MeasureTheory.Integrable X P ∧
  MeasureTheory.Integrable (fun ω => (X ω) ^ 2) P ∧
  (∫ ω, X ω ∂P) = μ ∧
  (∫ ω, (X ω) ^ 2 ∂P) - ((∫ ω, X ω ∂P) ^ 2) = var

-- Every scalar projection has the prescribed mean and variance.
def HasLinearMeanVariance {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) {n : ℕ}
    (c : Ω → Fin n → ℝ) (μ : Fin n → ℝ) (Sigma : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ a : Fin n → ℝ,
    HasMeanVariance P
      (fun ω => ∑ i, a i * c ω i)
      (∑ i, a i * μ i)
      (∑ i, a i * ∑ j, Sigma i j * a j)

/-
For a random vector c ∈ ℝ^n with finite second moments and mean μ = Ec, its covariance matrix is
Cov(c) = Ebig[(c - μ)(c - μ)ᵀbig].
-/
-- Cov(c)_{ij} = E[(c_i - μ_i)(c_j - μ_j)] via Bochner integral
def CovarianceMatrix {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) {n : ℕ}
    (c : Ω → Fin n → ℝ) (μ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ ω, (c ω i - μ i) * (c ω j - μ j) ∂P

/-
A quadratic program is an optimization problem of the form min_x (1)/(2)xᵀQx + qᵀ x + r subject to
affine equality and/or inequality constraints, where Q ∈ ℝ^{n×n}, q ∈ ℝ^n, and r ∈ ℝ.
-/
structure QuadraticProgram (n mEq mIneq : ℕ) where
  Q : Matrix (Fin n) (Fin n) ℝ
  Q_symm : Q.IsSymm
  q : Fin n → ℝ
  r : ℝ
  Aeq : Matrix (Fin mEq) (Fin n) ℝ
  beq : Fin mEq → ℝ
  Aineq : Matrix (Fin mIneq) (Fin n) ℝ
  bineq : Fin mIneq → ℝ

def QuadraticProgram.objective {n mEq mIneq : ℕ} (p : QuadraticProgram n mEq mIneq) (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, x i * ∑ j, p.Q i j * x j) + ∑ i, p.q i * x i + p.r

def QuadraticProgram.feasible {n mEq mIneq : ℕ}
    (p : QuadraticProgram n mEq mIneq) (x : Fin n → ℝ) : Prop :=
  (∀ i : Fin mEq, ∑ j, p.Aeq i j * x j = p.beq i) ∧
    (∀ i : Fin mIneq, ∑ j, p.Aineq i j * x j ≤ p.bineq i)

/-
The optimization problem minimize & E cᵀ x + γ var(cᵀ x); subject to & Ax preceq b is equivalent to
the quadratic program minimize & c_0ᵀ x + γ xᵀ σ x; subject to & Ax preceq b.
-/
structure MeanVarianceLinearCostProgram (n mIneq : ℕ) where
  -- probability space on which c is defined
  Ω : Type*
  instΩ : MeasurableSpace Ω
  P : MeasureTheory.Measure Ω
  -- c is a random vector, c0 its mean, Sigma its covariance
  c : Ω → Fin n → ℝ
  c0 : Fin n → ℝ
  Sigma : Matrix (Fin n) (Fin n) ℝ
  Sigma_symm : Sigma.IsSymm
  Sigma_psd : Sigma.PosSemidef
  gamma : ℝ
  A : Matrix (Fin mIneq) (Fin n) ℝ
  b : Fin mIneq → ℝ
  h_moments : HasLinearMeanVariance P c c0 Sigma

def MeanVarianceLinearCostProgram.objective
    {n mIneq : ℕ} (p : MeanVarianceLinearCostProgram n mIneq) :
    (Fin n → ℝ) → ℝ :=
  fun x => (∑ i, p.c0 i * x i) + p.gamma * (∑ i, x i * ∑ j, p.Sigma i j * x j)

def MeanVarianceLinearCostProgram.feasible
    {n mIneq : ℕ} (p : MeanVarianceLinearCostProgram n mIneq) :
    (Fin n → ℝ) → Prop :=
  fun x => ∀ i : Fin mIneq, ∑ j, p.A i j * x j ≤ p.b i

def MeanVarianceLinearCostProgram.toQuadraticProgram
    {n mIneq : ℕ} (p : MeanVarianceLinearCostProgram n mIneq) :
    QuadraticProgram n 0 mIneq :=
  { Q := fun i j => 2 * p.gamma * p.Sigma i j
    Q_symm := by
      ext i j
      simp [Matrix.transpose_apply, p.Sigma_symm.apply]
    q := p.c0
    r := 0
    Aeq := fun i => Fin.elim0 i
    beq := fun i => Fin.elim0 i
    Aineq := p.A
    bineq := p.b }

/-
Let A ∈ ℝ^{m × n}, b ∈ ℝ^m, c₀ ∈ ℝ^n, σ ∈ ℝ^{n×n}, and γ ∈ ℝ. Let the decision variable be x ∈ ℝ^n,
and let c ∈ ℝ^n be a random vector whose every scalar projection has the prescribed mean and
variance. Assume A, b, and x are deterministic, and interpret Ax preceq b componentwise. Define
var(cᵀ x) = E(cᵀ x)^2 - (Ecᵀ x)^2. Prove that Ecᵀ x + γvar(cᵀ x) = c_0ᵀ x + γ xᵀSigma x for every
x∈ℝ^n. No positivity of γ is needed for this algebraic identity.
-/
theorem meanVarianceLinearCost_objective_eq_quadratic_form
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {n : ℕ} (c : Ω → Fin n → ℝ) (c₀ x : Fin n → ℝ)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (gamma : ℝ)
    (h_moments : HasLinearMeanVariance P c c₀ Sigma)
    (hCov : CovarianceMatrix P c c₀ = Sigma)
    (hc_int : ∀ i : Fin n, MeasureTheory.Integrable (fun ω => c ω i) P)
    (hc2_int : ∀ i j : Fin n, MeasureTheory.Integrable (fun ω => c ω i * c ω j) P) :
    -- E[cᵀx] = c₀ᵀx and Var(cᵀx) = xᵀΣx so the objective equals the QP form
    (∫ ω, (∑ i, c ω i * x i) ∂P) +
      gamma * ((∫ ω, (∑ i, c ω i * x i) ^ 2 ∂P) -
        (∫ ω, (∑ i, c ω i * x i) ∂P) ^ 2) =
      (∑ i, c₀ i * x i) + gamma * (∑ i, x i * ∑ j, Sigma i j * x j) := by
  -- Specialize the projection-moment hypothesis to the portfolio vector `x`.
  rcases h_moments x with ⟨_, _, hMean, hVar⟩
  -- Commute the scalar products so the mean identity matches the statement exactly.
  have hMean' : (∫ ω, ∑ i, c ω i * x i ∂P) = ∑ i, c₀ i * x i := by
    simpa [mul_comm] using hMean
  -- Apply the same normalization to the variance identity for the projected cost.
  have hVar' :
      (∫ ω, (∑ i, c ω i * x i) ^ 2 ∂P) - (∫ ω, ∑ i, c ω i * x i ∂P) ^ 2 =
        ∑ i, x i * ∑ j, Sigma i j * x j := by
    simpa [mul_comm] using hVar
  -- Rewriting the stochastic mean and variance terms leaves the deterministic quadratic form.
  rw [hVar', hMean']

/-
Let A ∈ ℝ^{m × n}, b ∈ ℝ^m, c₀ ∈ ℝ^n, σ ∈ ℝ^{n×n}, and γ ∈ ℝ. The deterministic mean-variance
objective c₀ᵀx + γ xᵀΣx is exactly the quadratic-program objective obtained with Q = 2γΣ, q = c₀,
and r = 0, and the componentwise inequality constraints are identical. Hence feasibility, objective
values, comparisons, and minimizers are preserved. Convexity would require the additional condition
γΣ ⪰ 0; it is not built into this equivalence statement.
-/
/-- The encoded quadratic program has exactly the original inequality-feasibility region. -/
lemma meanVariance_feasible_iff_toQuadratic_feasible
    {n mIneq : ℕ} (p : MeanVarianceLinearCostProgram n mIneq) (x : Fin n → ℝ) :
    p.feasible x ↔ p.toQuadraticProgram.feasible x := by
  -- Unfold both feasibility predicates; the empty equality block disappears immediately.
  unfold MeanVarianceLinearCostProgram.feasible QuadraticProgram.feasible
  simp [MeanVarianceLinearCostProgram.toQuadraticProgram]

/-- The quadratic term in the encoded program simplifies to the original mean-variance penalty. -/
lemma half_two_scaled_quadratic_sum
    {n mIneq : ℕ} (p : MeanVarianceLinearCostProgram n mIneq) (x : Fin n → ℝ) :
    ((1 / 2 : ℝ) * ∑ i, x i * ∑ j, (2 * p.gamma * p.Sigma i j) * x j) =
      p.gamma * (∑ i, x i * ∑ j, p.Sigma i j * x j) := by
  -- First pull the shared scalar `2 * p.gamma` out of each inner sum.
  have hinner :
      ∀ i : Fin n,
        (∑ j, (2 * p.gamma * p.Sigma i j) * x j) =
          (2 * p.gamma) * ∑ j, p.Sigma i j * x j := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- Then factor the same scalar out of the outer sum and cancel it against `1 / 2`.
  calc
    ((1 / 2 : ℝ) * ∑ i, x i * ∑ j, (2 * p.gamma * p.Sigma i j) * x j)
        = ((1 / 2 : ℝ) * ∑ i, x i * ((2 * p.gamma) * ∑ j, p.Sigma i j * x j)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            rw [hinner i]
    _ = ((1 / 2 : ℝ) * ∑ i, (2 * p.gamma) * (x i * ∑ j, p.Sigma i j * x j)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ((1 / 2 : ℝ) * ((2 * p.gamma) * ∑ i, x i * ∑ j, p.Sigma i j * x j)) := by
          congr 1
          rw [Finset.mul_sum]
    _ = p.gamma * (∑ i, x i * ∑ j, p.Sigma i j * x j) := by
          ring

/-- The encoded quadratic objective agrees pointwise with the mean-variance objective. -/
lemma meanVariance_objective_eq_toQuadratic_objective
    {n mIneq : ℕ} (p : MeanVarianceLinearCostProgram n mIneq) (x : Fin n → ℝ) :
    p.objective x = p.toQuadraticProgram.objective x := by
  -- Expand the objective formulas and rewrite the quadratic term via the scalar-cancellation lemma.
  unfold MeanVarianceLinearCostProgram.objective QuadraticProgram.objective
  simp [MeanVarianceLinearCostProgram.toQuadraticProgram]
  rw [← half_two_scaled_quadratic_sum p x]
  ring

theorem meanVarianceLinearCostProgram_is_quadraticProgram
    {n mIneq : ℕ} (p : MeanVarianceLinearCostProgram n mIneq) :
    (∀ x : Fin n → ℝ,
      p.feasible x ↔ p.toQuadraticProgram.feasible x) ∧
    (∀ x : Fin n → ℝ,
      p.objective x = p.toQuadraticProgram.objective x) ∧
    (∀ x y : Fin n → ℝ,
      p.feasible x →
      p.feasible y →
      ((p.objective x ≤ p.objective y) ↔
        (p.toQuadraticProgram.objective x ≤ p.toQuadraticProgram.objective y))) ∧
    (∀ x : Fin n → ℝ,
      p.feasible x →
        ((∀ y : Fin n → ℝ, p.feasible y → p.objective x ≤ p.objective y) ↔
          ∀ y : Fin n → ℝ,
            p.toQuadraticProgram.feasible y →
              p.toQuadraticProgram.objective x ≤ p.toQuadraticProgram.objective y)) := by
  constructor
  · -- Start by identifying the same feasible set on both sides of the reduction.
    intro x
    exact meanVariance_feasible_iff_toQuadratic_feasible p x
  constructor
  · -- Next show that the encoded quadratic objective is pointwise identical.
    intro x
    exact meanVariance_objective_eq_toQuadratic_objective p x
  constructor
  · -- Objective comparisons are preserved because both objective functions are equal.
    intro x y _ _
    rw [meanVariance_objective_eq_toQuadratic_objective p x,
      meanVariance_objective_eq_toQuadratic_objective p y]
  · -- A minimizer transfers by translating each candidate's feasibility and rewriting objectives.
    intro x hx
    constructor
    · intro hxmin y hy
      have hy' : p.feasible y :=
        (meanVariance_feasible_iff_toQuadratic_feasible p y).mpr hy
      rw [← meanVariance_objective_eq_toQuadratic_objective p x,
        ← meanVariance_objective_eq_toQuadratic_objective p y]
      exact hxmin y hy'
    · intro hxmin y hy
      have hy' : p.toQuadraticProgram.feasible y :=
        (meanVariance_feasible_iff_toQuadratic_feasible p y).mp hy
      rw [meanVariance_objective_eq_toQuadratic_objective p x,
        meanVariance_objective_eq_toQuadratic_objective p y]
      exact hxmin y hy'

end «problem-76»
