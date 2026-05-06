import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-86»

-- Exercise_16_2__a_

/- [BLOCK Exercise 16.2-(a) | 19 | defn]
For a problem with equality constraints hⱼ(x)=0 and inequality constraints gₖ(x) ≤ 0, the Lagrange
multipliers are scalars λ_j and μ_k such that the Lagrangian is
L(x,λ,μ)=f(x)+sum_j λ_j hⱼ(x)+sum_k μ_k g k x.
-/
def lagrangian
    {X J K : Type*}
    [Fintype J]
    [Fintype K]
    (f : X → ℝ)
    (h : J → X → ℝ)
    (g : K → X → ℝ)
    (x : X)
    (lam : J → ℝ)
    (μ : K → ℝ) : ℝ :=
  f x + ∑ j, lam j * h j x + ∑ k, μ k * g k x

/- [BLOCK Exercise 16.2-(a) | 20 | opt_prob]
Let n,T ∈ ℕ with T ≥ 1. For generators i=1,\ldots,n and periods t=1,\ldots,T, let p_{it} ∈ ℝ satisfy
p_{it} ≥ 0. For each period t, let the demand be d_t>0. For each generator i, let
Pᵢ^{min},Pᵢ^{max},Rᵢ ∈ ℝ, and define
φ_i(u)=α_i u+β_i u^2 quad with α_i,β_i>0,
psi_i(v)=γ_i |v| quad with γ_i>0.
Consider the optimization problem
aligned
min_{(p_{it})} quad & sum_{i=1}^n sum_{t=1}ᵀ φ_i(p_{it})+sum_{i=1}^n sum_{t=1}^{T-1}
psi_i(p_{i,t+1}-p_{it}) ;
subject to quad & sum_{i=1}^n p_{it}=d_t, t=1,\ldots,T, ;
& Pᵢ^{min} ≤ p_{it} ≤ Pᵢ^{max}, i=1,\ldots,n,\ t=1,\ldots,T, ;
& |p_{i,t+1}-p_{it}| ≤ Rᵢ, i=1,\ldots,n,\ t=1,\ldots,T-1.
aligned
Assume this problem is feasible and has a unique optimal solution p_{it}^star.
-/
structure MultiPeriodEconomicDispatch
    (n T : ℕ) where
  d : Fin T → ℝ
  Pmin : Fin n → ℝ
  Pmax : Fin n → ℝ
  R : Fin n → ℝ
  α : Fin n → ℝ
  β : Fin n → ℝ
  γ : Fin n → ℝ
  hn : 1 ≤ n
  hT : 1 ≤ T
  demand_pos : ∀ t, 0 < d t
  Pmin_nonneg : ∀ i, 0 ≤ Pmin i
  Pmin_le_Pmax : ∀ i, Pmin i ≤ Pmax i
  R_nonneg : ∀ i, 0 ≤ R i
  alpha_pos : ∀ i, 0 < α i
  beta_pos : ∀ i, 0 < β i
  gamma_pos : ∀ i, 0 < γ i
def nextPeriod {T : ℕ} (hT : 1 ≤ T) (t : Fin (T - 1)) : Fin T :=
  ⟨t.1.succ, by
    have hT' : 0 < T := Nat.succ_le_iff.mp hT
    exact lt_of_le_of_lt (Nat.succ_le_of_lt t.2) (Nat.sub_lt hT' (by simp))⟩

def MultiPeriodEconomicDispatch.phi
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T) (i : Fin n) (u : ℝ) : ℝ :=
  prob.α i * u + prob.β i * u^2

def MultiPeriodEconomicDispatch.psi
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T) (i : Fin n) (v : ℝ) : ℝ :=
  prob.γ i * |v|

def MultiPeriodEconomicDispatch.objective
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T) (q : Fin n → Fin T → ℝ) : ℝ :=
  (∑ i, ∑ t, prob.phi i (q i t)) +
    ∑ i, ∑ t : Fin (T - 1),
      prob.psi i
        (q i (Fin.castLEOrderEmb (Nat.sub_le T 1) t) - q i (nextPeriod prob.hT t))

def MultiPeriodEconomicDispatch.IsFeasible
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T) (q : Fin n → Fin T → ℝ) : Prop :=
  (∀ i t, 0 ≤ q i t) ∧
  (∀ t, ∑ i, q i t = prob.d t) ∧
  (∀ i t, prob.Pmin i ≤ q i t ∧ q i t ≤ prob.Pmax i) ∧
  (∀ i (t : Fin (T - 1)),
    |q i (Fin.castLEOrderEmb (Nat.sub_le T 1) t) -
      q i (nextPeriod prob.hT t)| ≤ prob.R i)

def MultiPeriodEconomicDispatch.IsOptimalSolution
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T) (q : Fin n → Fin T → ℝ) : Prop :=
  prob.IsFeasible q ∧ ∀ q' : Fin n → Fin T → ℝ, prob.IsFeasible q' → prob.objective q ≤ prob.objective q'

def MultiPeriodEconomicDispatch.p
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T)
    (hunique_optimal : ∃! pStar : Fin n → Fin T → ℝ, prob.IsOptimalSolution pStar) :
    Fin n → Fin T → ℝ :=
  Classical.choose (ExistsUnique.exists hunique_optimal)

def MultiPeriodEconomicDispatch.p_spec
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T)
    (hunique_optimal : ∃! pStar : Fin n → Fin T → ℝ, prob.IsOptimalSolution pStar) :
    prob.IsOptimalSolution (prob.p hunique_optimal) := by
  simpa [MultiPeriodEconomicDispatch.p] using
    (Classical.choose_spec (ExistsUnique.exists hunique_optimal))

def MultiPeriodEconomicDispatch.bounds
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T)
    (hunique_optimal : ∃! pStar : Fin n → Fin T → ℝ, prob.IsOptimalSolution pStar) (i : Fin n) :
    ∀ t, prob.Pmin i ≤ prob.p hunique_optimal i t ∧ prob.p hunique_optimal i t ≤ prob.Pmax i :=
  (prob.p_spec hunique_optimal).1.2.2.1 i

def MultiPeriodEconomicDispatch.ramp
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T)
    (hunique_optimal : ∃! pStar : Fin n → Fin T → ℝ, prob.IsOptimalSolution pStar) (i : Fin n) :
    ∀ t : Fin (T - 1),
      |prob.p hunique_optimal i (Fin.castLEOrderEmb (Nat.sub_le T 1) t) -
        prob.p hunique_optimal i (⟨t.1.succ, by
          have hT' : 0 < T := Nat.succ_le_iff.mp prob.hT
          exact lt_of_le_of_lt (Nat.succ_le_of_lt t.2) (Nat.sub_lt hT' (by simp))⟩)| ≤ prob.R i :=
  (prob.p_spec hunique_optimal).1.2.2.2 i

/- [BLOCK Exercise 16.2-(a) | 21 | opt_prob]
aligned
min_{(p_{i,t})} quad & sum_{t=1}ᵀ (φ_i(p_{i,t})-Q_t p_{i,t})+sum_{t=1}^{T-1}
psi_i(p_{i,t+1}-p_{i,t}) ;
subject to quad & Pᵢ^{min} ≤ p_{i,t} ≤ Pᵢ^{max}, t=1,\ldots,T, ;
& |p_{i,t+1}-p_{i,t}| ≤ Rᵢ, t=1,\ldots,T-1.
aligned
-/
structure SingleGeneratorDispatchProblem (T : ℕ) where
  Q : Fin T → ℝ
  Pmin : ℝ
  Pmax : ℝ
  R : ℝ
  α : ℝ
  β : ℝ
  γ : ℝ
  hT : 1 ≤ T
  Pmin_nonneg : 0 ≤ Pmin
  Pmin_le_Pmax : Pmin ≤ Pmax
  R_nonneg : 0 ≤ R
  alpha_pos : 0 < α
  beta_pos : 0 < β
  gamma_pos : 0 < γ

def SingleGeneratorDispatchProblem.objective
    {T : ℕ} (prob : SingleGeneratorDispatchProblem T) : (Fin T → ℝ) → ℝ :=
  fun q =>
    (∑ t, ((prob.α * q t + prob.β * (q t)^2) - prob.Q t * q t)) +
      ∑ t : Fin (T - 1),
        prob.γ * |q (nextPeriod prob.hT t) - q (Fin.castLEOrderEmb (Nat.sub_le T 1) t)|

def SingleGeneratorDispatchProblem.IsFeasible
    {T : ℕ} (prob : SingleGeneratorDispatchProblem T) : (Fin T → ℝ) → Prop :=
  fun q =>
    (∀ t, prob.Pmin ≤ q t ∧ q t ≤ prob.Pmax) ∧
    (∀ t : Fin (T - 1),
      |q (nextPeriod prob.hT t) - q (Fin.castLEOrderEmb (Nat.sub_le T 1) t)| ≤ prob.R)

def SingleGeneratorDispatchProblem.phiDef
    {T : ℕ} (prob : SingleGeneratorDispatchProblem T) (u : ℝ) : ℝ :=
  prob.α * u + prob.β * u^2

def SingleGeneratorDispatchProblem.psiDef
    {T : ℕ} (prob : SingleGeneratorDispatchProblem T) (v : ℝ) : ℝ :=
  prob.γ * |v|

def MultiPeriodEconomicDispatch.singleGeneratorProblem
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T) (Q : Fin T → ℝ) (i : Fin n) :
    SingleGeneratorDispatchProblem T where
  Q := Q
  Pmin := prob.Pmin i
  Pmax := prob.Pmax i
  R := prob.R i
  α := prob.α i
  β := prob.β i
  γ := prob.γ i
  hT := prob.hT
  Pmin_nonneg := prob.Pmin_nonneg i
  Pmin_le_Pmax := prob.Pmin_le_Pmax i
  R_nonneg := prob.R_nonneg i
  alpha_pos := prob.alpha_pos i
  beta_pos := prob.beta_pos i
  gamma_pos := prob.gamma_pos i

def MultiPeriodEconomicDispatch.productFeasible
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T) (q : Fin n → Fin T → ℝ) : Prop :=
  ∀ i : Fin n,
    (prob.singleGeneratorProblem (fun _ => 0) i).IsFeasible (q i)

/- [BLOCK Exercise 16.2-(a) | 22 | thm]
Let n,T ∈ ℕ with T ≥ 1. For generators i=1,\ldots,n and periods t=1,\ldots,T, let p_{it} ∈ ℝ satisfy
p_{it} ≥ 0. For each period t, let the demand be d_t>0. For each generator i, let
Pᵢ^{min},Pᵢ^{max},Rᵢ ∈ ℝ, and define
φ_i(u)=α_i u+β_i u^2 quad with α_i,β_i>0,
psi_i(v)=γ_i |v| quad with γ_i>0.
Consider the multi-period economic dispatch
aligned
min_{(p_{it})} quad & sum_{i=1}^n sum_{t=1}ᵀ φ_i(p_{it})+sum_{i=1}^n sum_{t=1}^{T-1}
psi_i(p_{i,t+1}-p_{it}) ;
subject to quad & sum_{i=1}^n p_{it}=d_t, t=1,\ldots,T, ;
& Pᵢ^{min} ≤ p_{it} ≤ Pᵢ^{max}, i=1,\ldots,n,; t=1,\ldots,T, ;
& |p_{i,t+1}-p_{it}| ≤ Rᵢ, i=1,\ldots,n,; t=1,\ldots,T-1.
aligned
Assume this problem is feasible and has a unique optimal solution p_{it}^star. Prove that there
exist real numbers Q₁,\ldots,Q_T such that, for each i=1,\ldots,n, the sequence
p_{i1}^star,\ldots,p_{iT}^star solves the single-generator dispatch problem
aligned
min_{(p_{i,t})} quad & sum_{t=1}ᵀ (φ_i(p_{i,t})-Q_t p_{i,t})+sum_{t=1}^{T-1}
psi_i(p_{i,t+1}-p_{i,t}) ;
subject to quad & Pᵢ^{min} ≤ p_{i,t} ≤ Pᵢ^{max}, t=1,\ldots,T, ;
& |p_{i,t+1}-p_{i,t}| ≤ Rᵢ, t=1,\ldots,T-1,
aligned
and that the prices Q_t can be chosen as the Lagrange multipliers associated with the coupling
constraints sum_{i=1}^n p_{it}=d_t for t=1,\ldots,T.
-/
theorem exists_prices_as_lagrange_multipliers_for_single_generator_subproblems
    {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T)
    (hunique_optimal : ∃! pStar : Fin n → Fin T → ℝ, prob.IsOptimalSolution pStar) :
    ∃ Q : Fin T → ℝ,
      (∀ i : Fin n,
        (prob.singleGeneratorProblem Q i).IsFeasible (prob.p hunique_optimal i) ∧
        ∀ q : Fin T → ℝ,
          (prob.singleGeneratorProblem Q i).IsFeasible q →
          (prob.singleGeneratorProblem Q i).objective (prob.p hunique_optimal i) ≤
            (prob.singleGeneratorProblem Q i).objective q) ∧
      ∀ q : Fin n → Fin T → ℝ,
        prob.productFeasible q →
        @lagrangian
          (Fin n → Fin T → ℝ)
          (Fin T)
          (Fin 0)
          inferInstance
          inferInstance
          (fun q : Fin n → Fin T → ℝ => prob.objective q)
          (fun t q => ∑ i, q i t - prob.d t)
          (fun _ _ => 0)
          (prob.p hunique_optimal)
          Q
          (fun k => 0) ≤
        @lagrangian
          (Fin n → Fin T → ℝ)
          (Fin T)
          (Fin 0)
          inferInstance
          inferInstance
          (fun q : Fin n → Fin T → ℝ => prob.objective q)
          (fun t q => ∑ i, q i t - prob.d t)
          (fun _ _ => 0)
          q
          Q
          (fun k => 0) := by
  sorry

end «problem-86»
