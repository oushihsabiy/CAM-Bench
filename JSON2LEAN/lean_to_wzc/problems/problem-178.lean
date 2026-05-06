import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators


namespace «problem-178»
/-
For the problem min f(x) subject to equality constraints h(x) = 0 and inequality constraints g(x) ≥
0, the Karush - - Kuhn - - Tucker conditions consist of primal feasibility h(x) = 0, g(x) ≥ 0;
stationarity ∇ f(x) - J_h(x)ᵀλ - J_g(x)ᵀμ = 0; dual feasibility μ ≥ 0; and complementarity μ_i gᵢ(x)
= 0
for all i.
-/
def KarushKuhnTuckerConditions
    {n m p : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin p → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (lam : Fin m → ℝ)
    (mu : Fin p → ℝ) : Prop :=
  h x = 0 ∧
  (∀ i, 0 ≤ g x i) ∧
  (gradient f x
    - (fun j => ∑ i, lam i * gradient (fun y => h y i) x j)
    - (fun j => ∑ i, mu i * gradient (fun y => g y i) x j)) = 0 ∧
  (∀ i, 0 ≤ mu i) ∧
  ∀ i, mu i * g x i = 0

/-
A primal variable x is primal feasible if it satisfies all constraints of the optimization problem;
that is, all equality constraints hold and all inequality constraints are satisfied.
-/
def PrimalFeasible
    {n m p : ℕ}
    (h : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin p → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  h x = 0 ∧ ∀ i, 0 ≤ g x i

/-
A primal - dual tuple satisfies stationarity if the ∇of the Lagrangian with respect to the primal
variables vanishes at that tuple.
-/
def Stationary
    {n m p : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin p → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (lam : Fin m → ℝ)
    (mu : Fin p → ℝ) : Prop :=
  (gradient f x
    - (fun j => ∑ i, lam i * gradient (fun y => h y i) x j)
    - (fun j => ∑ i, mu i * gradient (fun y => g y i) x j)) = 0

/-
Dual feasibility means that the multipliers associated with the inequality constraints satisfy the
required sign condition; for constraints written as g(x) ≥ 0, this means μ ≥ 0 componentwise.
-/
def DualFeasible
    {p : ℕ}
    (mu : Fin p → ℝ) : Prop :=
  ∀ i, 0 ≤ mu i

/-
Complementarity is the condition that each inequality constraint and its associated multiplier have
product zero: μ_i gᵢ(x) = 0 for every inequality index i.
-/
def Complementary
    {n p : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → Fin p → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (mu : Fin p → ℝ) : Prop :=
  ∀ i, mu i * g x i = 0

/-
Lagrange multipliers are auxiliary dual variables introduced for the constraints in the Lagrangian;
for constraints h(x) = 0 and g(x) ≥ 0, they are the vectors λ and μ appearing in L(x, λ, μ) =
f(x) - λᵀ h(x) - μᵀ g(x).
-/
def KKTPoint
    {n m p : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin p → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (lam : Fin m → ℝ)
    (mu : Fin p → ℝ) : Prop :=
  KarushKuhnTuckerConditions f h g x lam mu

/-
For an inequality constraint g(x) ≥ 0, a slack variable is a variable s ≥ 0 introduced so that the
inequality is rewritten as the equality g(x) - s = 0. The nonnegativity of s is part of primal
feasibility; omitting it would make the slack KKT system strictly weaker than the original one.
-/
def SlackKKTPoint
    {n m p : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : EuclideanSpace ℝ (Fin n) → Fin m → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin p → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (s : Fin p → ℝ)
    (lam : Fin m → ℝ)
    (nu mu : Fin p → ℝ) : Prop :=
  h x = 0 ∧
  (∀ i, g x i - s i = 0) ∧
  (∀ i, 0 ≤ s i) ∧
  (gradient f x
    - (fun j => ∑ i, lam i * gradient (fun y => h y i) x j)
    - (fun j => ∑ i, nu i * gradient (fun y => g y i) x j)) = 0 ∧
  (∀ i, nu i = mu i) ∧
  (∀ i, 0 ≤ mu i) ∧
  (∀ i, mu i * s i = 0)

/-
Let f: ℝ^n→ℝ, c_e: ℝ^n→ℝ^{m_e}, and cᵢ: ℝ^n→ℝ^{mᵢ} be continuously differentiable, where n, m_e,
mᵢ∈N0. Consider the nonlinear program min_{x∈ℝ^n} f(x) subject toquad c_e(x) = 0, cᵢ(x) ≥ 0.
-/
structure NonlinearProgram where
  n : ℕ
  me : ℕ
  mi : ℕ
  f : EuclideanSpace ℝ (Fin n) → ℝ
  c_e : EuclideanSpace ℝ (Fin n) → Fin me → ℝ
  c_i : EuclideanSpace ℝ (Fin n) → Fin mi → ℝ
  f_contDiff : ContDiff ℝ 1 f
  c_e_contDiff : ∀ i : Fin me, ContDiff ℝ 1 (fun x => c_e x i)
  c_i_contDiff : ∀ i : Fin mi, ContDiff ℝ 1 (fun x => c_i x i)

def NonlinearProgram.feasibleSet (P : NonlinearProgram) : Set (EuclideanSpace ℝ (Fin P.n)) :=
  {x | P.c_e x = 0 ∧ ∀ i, 0 ≤ P.c_i x i}

def NonlinearProgram.isFeasible (P : NonlinearProgram) (x : EuclideanSpace ℝ (Fin P.n)) : Prop :=
  PrimalFeasible P.c_e P.c_i x

def NonlinearProgram.objective (P : NonlinearProgram) : EuclideanSpace ℝ (Fin P.n) → ℝ :=
  P.f

/-
Its slack - variable reformulation is array{rl} min_{x, s} & f(x); subject to & c_e(x) = 0,; & cᵢ(x)
- s
= 0,; & s ≥ 0, array with x∈ℝ^n, s∈ℝ^{mᵢ}, and s ≥ 0 componentwise.
-/
structure SlackVariableReformulationData where
  P : NonlinearProgram

def SlackVariableReformulationData.feasibleSet (R : SlackVariableReformulationData) :
    Set ((EuclideanSpace ℝ (Fin R.P.n)) × (Fin R.P.mi → ℝ)) :=
  {xs |
    R.P.c_e xs.1 = 0 ∧
    (∀ i, R.P.c_i xs.1 i - xs.2 i = 0) ∧
    ∀ i, 0 ≤ xs.2 i}

def SlackVariableReformulationData.objective (R : SlackVariableReformulationData) :
    ((EuclideanSpace ℝ (Fin R.P.n)) × (Fin R.P.mi → ℝ)) → ℝ :=
  fun xs => R.P.f xs.1

def mkSlackVariableReformulationData (P : NonlinearProgram) :
    SlackVariableReformulationData :=
  { P := P }

instance : Coe NonlinearProgram SlackVariableReformulationData where
  coe := mkSlackVariableReformulationData

structure SlackVariableReformulation where
  data : SlackVariableReformulationData

def SlackVariableReformulation.P (R : SlackVariableReformulation) : NonlinearProgram :=
  R.data.P

def SlackVariableReformulation.isFeasible
    (R : SlackVariableReformulation)
    (x : EuclideanSpace ℝ (Fin R.P.n))
    (s : Fin R.P.mi → ℝ) : Prop :=
  R.P.c_e x = 0 ∧
  (∀ i, R.P.c_i x i - s i = 0) ∧
  ∀ i, 0 ≤ s i

/-
Let f: ℝ^n→ℝ, c_e: ℝ^n→ℝ^{m_e}, and cᵢ: ℝ^n→ℝ^{mᵢ} be continuously differentiable, where n, m_e,
mᵢ∈N0. Consider the nonlinear program min_{x∈ℝ^n} f(x) subject toquad c_e(x) = 0, cᵢ(x) ≥ 0,
where cᵢ(x) ≥ 0 is componentwise, and its slack - variable reformulation array{rl} min_{x, s} &
f(x);
subject to & c_e(x) = 0,; & cᵢ(x) - s = 0,; & s ≥ 0, array with x∈ℝ^n, s∈ℝ^{mᵢ}, and s ≥ 0
componentwise. For each problem, write down the Karush - - Kuhn - - Tucker conditions, including
primal
feasibility, stationarity, dual feasibility, and complementarity, using Lagrange multipliers for the
equality and inequality constraints.
-/
theorem kkt_conditions_for_nonlinear_program_and_slack_reformulation
    (P : NonlinearProgram) :
    (∀ (x : EuclideanSpace ℝ (Fin P.n)),
      (∃ lam : Fin P.me → ℝ, ∃ mu : Fin P.mi → ℝ,
        KKTPoint P.f P.c_e P.c_i x lam mu) ↔
      (∃ lam : Fin P.me → ℝ, ∃ mu : Fin P.mi → ℝ,
        PrimalFeasible P.c_e P.c_i x ∧
        Stationary P.f P.c_e P.c_i x lam mu ∧
        DualFeasible mu ∧
        Complementary P.c_i x mu)) ∧
    (∀ (x : EuclideanSpace ℝ (Fin P.n)) (s : Fin P.mi → ℝ),
      (∃ lam : Fin P.me → ℝ, ∃ nu mu : Fin P.mi → ℝ,
        SlackKKTPoint P.f P.c_e P.c_i x s lam nu mu) ↔
      (∃ lam : Fin P.me → ℝ, ∃ nu mu : Fin P.mi → ℝ,
        P.c_e x = 0 ∧
        (∀ i, P.c_i x i - s i = 0) ∧
        (∀ i, 0 ≤ s i) ∧
        ((gradient P.f x)
          - (fun j => ∑ i, lam i * gradient (fun y => P.c_e y i) x j)
          - (fun j => ∑ i, nu i * gradient (fun y => P.c_i y i) x j) = 0) ∧
        (∀ i, nu i = mu i) ∧
        (∀ i, 0 ≤ mu i) ∧
        (∀ i, mu i * s i = 0))) := by
  sorry

/-
Let f: ℝ^n→ℝ, c_e: ℝ^n→ℝ^{m_e}, and cᵢ: ℝ^n→ℝ^{mᵢ} be continuously differentiable, where n, m_e,
mᵢ∈N0. Consider the nonlinear program min_{x∈ℝ^n} f(x) subject toquad c_e(x) = 0, cᵢ(x) ≥ 0,
where cᵢ(x) ≥ 0 is componentwise, and its slack - variable reformulation array{rl} min_{x, s} &
f(x);
subject to & c_e(x) = 0,; & cᵢ(x) - s = 0,; & s ≥ 0, array with x∈ℝ^n, s∈ℝ^{mᵢ}, and s ≥ 0
componentwise. Establish a one - to - one correspondence between the KKT points of the original
problem and the KKT points of the slack - variable reformulation. With the Lagrangian convention
L = f - λᵀc_e - μᵀcᵢ for cᵢ(x) ≥ 0, the slack formulation uses equality multiplier ν for
cᵢ(x) - s = 0 and inequality multiplier μ for s ≥ 0; stationarity in s forces ν = μ. Hence the
slack and equality multiplier are uniquely determined by s = cᵢ(x) and ν = μ. If mᵢ = 0, all
componentwise conditions over Fin mᵢ are vacuous, so the statement reduces to the equality-
constrained KKT system without adding extra assumptions.
-/
theorem kkt_points_equiv_slack_variable_reformulation
    (P : NonlinearProgram) :
    ∀ (x : EuclideanSpace ℝ (Fin P.n))
      (lam : Fin P.me → ℝ)
      (mu : Fin P.mi → ℝ),
      (KKTPoint P.f P.c_e P.c_i x lam mu ↔
        SlackKKTPoint P.f P.c_e P.c_i
          x
          (fun i => P.c_i x i)
          lam
          mu
          mu) ∧
      (∀ (s nu : Fin P.mi → ℝ),
        SlackKKTPoint P.f P.c_e P.c_i x s lam nu mu →
          s = (fun i => P.c_i x i) ∧
          nu = mu ∧
          KKTPoint P.f P.c_e P.c_i x lam mu) := by
  sorry

end «problem-178»
