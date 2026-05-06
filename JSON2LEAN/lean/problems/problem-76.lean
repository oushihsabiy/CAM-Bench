import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

/- A random vector c ∈ ℝ^n is Gaussian with mean μ ∈ ℝ^n and covariance σ ∈ ℝ^{n×n} if, for every a ∈
ℝ^n, the scalar random variable aᵀ c is univariate normal with mean aᵀ μ and variance aᵀ σ a.
-/
-- IsUnivariateNormal P X μ var : the random variable X on (Ω, P) is N(μ, var)
axiom IsUnivariateNormal {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : Ω → ℝ) (μ var : ℝ) : Prop

-- c : Ω → Fin n → ℝ is a Gaussian random vector with mean μ and covariance Σ
-- iff for every a, the scalar aᵀc(ω) is N(aᵀμ, aᵀΣa)
def IsGaussianRandomVector {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) {n : ℕ}
    (c : Ω → Fin n → ℝ) (μ : Fin n → ℝ) (Sigma : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ a : Fin n → ℝ,
    IsUnivariateNormal P
      (fun ω => ∑ i, a i * c ω i)
      (∑ i, a i * μ i)
      (∑ i, a i * ∑ j, Sigma i j * a j)

/- For a random vector c ∈ ℝ^n with finite second moments and mean μ = Ec, its covariance matrix is
Cov(c) = Ebig[(c-μ)(c-μ)ᵀbig].
-/
-- Cov(c)_{ij} = E[(c_i - μ_i)(c_j - μ_j)] via Bochner integral
def CovarianceMatrix {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) {n : ℕ}
    (c : Ω → Fin n → ℝ) (μ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ ω, (c ω i - μ i) * (c ω j - μ j) ∂P

/-A quadratic program is an optimization problem of the form min_x (1)/(2)xᵀQx + qᵀ x + r subject to
affine equality and/or inequality constraints, where Q ∈ ℝ^{n×n}, q ∈ ℝ^n, and r ∈ ℝ.
-/
structure QuadraticProgram (n mEq mIneq : ℕ) where
  Q : Matrix (Fin n) (Fin n) ℝ
  q : Fin n → ℝ
  r : ℝ
  Aeq : Matrix (Fin mEq) (Fin n) ℝ
  beq : Fin mEq → ℝ
  Aineq : Matrix (Fin mIneq) (Fin n) ℝ
  bineq : Fin mIneq → ℝ

def QuadraticProgram.objective {n mEq mIneq : ℕ} (p : QuadraticProgram n mEq mIneq) (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, x i * ∑ j, p.Q i j * x j) + ∑ i, p.q i * x i + p.r

def QuadraticProgram.satisfiesEqualities {n mEq mIneq : ℕ} (p : QuadraticProgram n mEq mIneq) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin mEq, ∑ j, p.Aeq i j * x j = p.beq i

def QuadraticProgram.satisfiesInequalities {n mEq mIneq : ℕ} (p : QuadraticProgram n mEq mIneq) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin mIneq, ∑ j, p.Aineq i j * x j ≤ p.bineq i

def QuadraticProgram.isFeasible {n mEq mIneq : ℕ} (p : QuadraticProgram n mEq mIneq) (x : Fin n → ℝ) : Prop :=
  p.satisfiesEqualities x ∧ p.satisfiesInequalities x

/- The optimization problem
aligned
minimize quad & E cᵀ x + γ var(cᵀ x) ;
subject to quad & Ax preceq b
aligned
is equivalent to the quadratic program
aligned
minimize quad & c_0ᵀ x + γ xᵀ σ x ;
subject to quad & Ax preceq b.
aligned
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
  gamma : ℝ
  A : Matrix (Fin mIneq) (Fin n) ℝ
  b : Fin mIneq → ℝ
  hGaussian : IsGaussianRandomVector P c c0 Sigma
  optimization_equiv :
    ∀ x y : Fin n → ℝ,
      (∀ i : Fin mIneq, ∑ j, A i j * x j ≤ b i) →
      (∀ i : Fin mIneq, ∑ j, A i j * y j ≤ b i) →
      (((∑ i, x i * c0 i) + gamma * (∑ i, x i * ∑ j, Sigma i j * x j)) ≤
        ((∑ i, y i * c0 i) + gamma * (∑ i, y i * ∑ j, Sigma i j * y j))) ↔
      (QuadraticProgram.objective
          { Q := fun i j => 2 * gamma * Sigma i j
            q := c0
            r := 0
            Aeq := fun i => Fin.elim0 i
            beq := fun i => Fin.elim0 i
            Aineq := A
            bineq := b } x ≤
        QuadraticProgram.objective
          { Q := fun i j => 2 * gamma * Sigma i j
            q := c0
            r := 0
            Aeq := fun i => Fin.elim0 i
            beq := fun i => Fin.elim0 i
            Aineq := A
            bineq := b } y)

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
    q := p.c0
    r := 0
    Aeq := fun i => Fin.elim0 i
    beq := fun i => Fin.elim0 i
    Aineq := p.A
    bineq := p.b }

/- Let A ∈ ℝ^{m × n}, b ∈ ℝ^m, c₀ ∈ ℝ^n, σ ∈ ℝ^{n×n}, and γ ≥ 0. Let the decision variable be x ∈ ℝ^n,
and let c ∈ ℝ^n be a Gaussian random vector with mean c₀ and covariance matrix σ, so that Ec=c₀ and
E(c-c₀)(c-c₀)ᵀ=σ. Assume A, b, and x are deterministic, and interpret Ax preceq b componentwise.
Define var(cᵀ x)=E(cᵀ x)^2-(Ecᵀ x)^2. Prove that Ecᵀ x+γvar(cᵀ x)=c_0ᵀ x+γ xᵀSigma x for every
x∈ℝ^n.
-/
theorem meanVarianceLinearCost_objective_eq_quadratic_form
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {n : ℕ} (c : Ω → Fin n → ℝ) (c₀ x : Fin n → ℝ)
    (Sigma : Matrix (Fin n) (Fin n) ℝ) (gamma : ℝ)
    (hGaussian : IsGaussianRandomVector P c c₀ Sigma)
    (hCov : CovarianceMatrix P c c₀ = Sigma)
    (hgamma : 0 ≤ gamma)
    (hc_int : ∀ i : Fin n, MeasureTheory.Integrable (fun ω => c ω i) P)
    (hc2_int : ∀ i j : Fin n, MeasureTheory.Integrable (fun ω => c ω i * c ω j) P) :
    -- E[cᵀx] = c₀ᵀx  and  Var(cᵀx) = xᵀΣx  so the objective equals the QP form
    (∫ ω, (∑ i, c ω i * x i) ∂P) +
      gamma * ((∫ ω, (∑ i, c ω i * x i) ^ 2 ∂P) -
        (∫ ω, (∑ i, c ω i * x i) ∂P) ^ 2) =
      (∑ i, c₀ i * x i) + gamma * (∑ i, x i * ∑ j, Sigma i j * x j) := by
  sorry

/- Let A ∈ ℝ^{m × n}, b ∈ ℝ^m, c₀ ∈ ℝ^n, σ ∈ ℝ^{n×n}, and γ ≥ 0. Let the decision variable be x ∈ ℝ^n,
and let c ∈ ℝ^n be a Gaussian random vector with mean c₀ and covariance matrix σ, so that Ec=c₀ and
E(c-c₀)(c-c₀)ᵀ=σ. Assume A, b, and x are deterministic, and interpret Ax preceq b componentwise.
Define var(cᵀ x)=E(cᵀ x)^2-(Ecᵀ x)^2. Hence mean-variance linear cost program and is a convex
optimization problem.
-/
theorem meanVarianceLinearCostProgram_is_quadraticProgram
    {n mIneq : ℕ} (p : MeanVarianceLinearCostProgram n mIneq)
    (hgamma : 0 ≤ p.gamma) :
    ∀ x y : Fin n → ℝ,
      p.feasible x →
      p.feasible y →
      (p.objective x ≤ p.objective y) ↔
        (p.toQuadraticProgram.objective x ≤ p.toQuadraticProgram.objective y) := by
  sorry
