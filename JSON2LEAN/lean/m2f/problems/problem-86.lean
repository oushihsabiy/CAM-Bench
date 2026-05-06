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

/-- The counterexample uses the one-generator, one-period index facts `1 ≤ 1`. -/
lemma counterexample_hn : 1 ≤ 1 := by
  norm_num

/-- The counterexample uses the one-generator, one-period index facts `1 ≤ 1`. -/
lemma counterexample_hT : 1 ≤ 1 := by
  norm_num

/-- The explicit demand `1` is positive in the one-period counterexample. -/
lemma counterexample_demand_pos : ∀ t : Fin 1, 0 < (1 : ℝ) := by
  intro t
  norm_num

/-- The explicit lower bound `0` is nonnegative in the counterexample. -/
lemma counterexample_Pmin_nonneg : ∀ i : Fin 1, 0 ≤ (0 : ℝ) := by
  intro i
  norm_num

/-- The explicit lower and upper bounds satisfy `0 ≤ 2` in the counterexample. -/
lemma counterexample_Pmin_le_Pmax : ∀ i : Fin 1, (0 : ℝ) ≤ 2 := by
  intro i
  norm_num

/-- The explicit ramp limit `0` is nonnegative in the counterexample. -/
lemma counterexample_R_nonneg : ∀ i : Fin 1, 0 ≤ (0 : ℝ) := by
  intro i
  norm_num

/-- The linear production coefficient is positive in the counterexample. -/
lemma counterexample_alpha_pos : ∀ i : Fin 1, 0 < (1 : ℝ) := by
  intro i
  norm_num

/-- The quadratic production coefficient is positive in the counterexample. -/
lemma counterexample_beta_pos : ∀ i : Fin 1, 0 < (1 : ℝ) := by
  intro i
  norm_num

/-- The ramp penalty coefficient is positive in the counterexample. -/
lemma counterexample_gamma_pos : ∀ i : Fin 1, 0 < (1 : ℝ) := by
  intro i
  norm_num

/-- A one-generator, one-period dispatch instance exposing the sign mismatch. -/
def counterexampleDispatch : MultiPeriodEconomicDispatch 1 1 where
  d := fun _ => 1
  Pmin := fun _ => 0
  Pmax := fun _ => 2
  R := fun _ => 0
  α := fun _ => 1
  β := fun _ => 1
  γ := fun _ => 1
  hn := counterexample_hn
  hT := counterexample_hT
  demand_pos := counterexample_demand_pos
  Pmin_nonneg := counterexample_Pmin_nonneg
  Pmin_le_Pmax := counterexample_Pmin_le_Pmax
  R_nonneg := counterexample_R_nonneg
  alpha_pos := counterexample_alpha_pos
  beta_pos := counterexample_beta_pos
  gamma_pos := counterexample_gamma_pos

/-- The unique feasible dispatch in the counterexample sends one unit in the lone period. -/
def counterexampleOptimalDispatch : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => 1

/-- The all-zero dispatch is the product-feasible competitor used in the contradiction. -/
def counterexampleZeroDispatch : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => 0

/-- The single-generator optimizer candidate is the constant one profile. -/
def counterexampleGeneratorPoint : Fin 1 → ℝ :=
  fun _ => 1

/-- The zero single-generator profile is feasible for the local box constraints. -/
def counterexampleGeneratorZero : Fin 1 → ℝ :=
  fun _ => 0

/-- The profile constantly equal to `2` is also feasible for the local box constraints. -/
def counterexampleGeneratorTwo : Fin 1 → ℝ :=
  fun _ => 2

/-- Feasibility forces the unique coordinate of the counterexample dispatch to equal `1`. -/
lemma counterexample_feasible_iff_value_one
    (q : Fin 1 → Fin 1 → ℝ) :
    counterexampleDispatch.IsFeasible q ↔ q 0 0 = 1 := by
  constructor
  · intro hq
    -- The single demand balance equation fixes the unique scalar dispatch value.
    have hsum := hq.2.1 0
    simpa [counterexampleDispatch] using hsum
  · intro hq
    -- Once that scalar value is fixed, all remaining constraints are immediate.
    constructor
    · intro i t
      fin_cases i
      fin_cases t
      simpa [hq] using (show (0 : ℝ) ≤ 1 by norm_num)
    constructor
    · intro t
      fin_cases t
      simpa [counterexampleDispatch, hq]
    constructor
    · intro i t
      fin_cases i
      fin_cases t
      constructor
      · simpa [counterexampleDispatch, hq]
      · simpa [counterexampleDispatch, hq]
    · intro i t
      fin_cases i
      exact Fin.elim0 t

/-- Every feasible dispatch in the counterexample equals the constant-one optimizer. -/
lemma counterexample_feasible_eq_optimal
    (q : Fin 1 → Fin 1 → ℝ)
    (hq : counterexampleDispatch.IsFeasible q) :
    q = counterexampleOptimalDispatch := by
  -- The demand equality above pins down the only coordinate of the dispatch.
  ext i t
  fin_cases i
  fin_cases t
  simpa [counterexampleOptimalDispatch] using
    (counterexample_feasible_iff_value_one q).1 hq

/-- The counterexample instance has a unique optimal dispatch. -/
lemma counterexample_has_unique_optimal_solution :
    ∃! pStar : Fin 1 → Fin 1 → ℝ, counterexampleDispatch.IsOptimalSolution pStar := by
  refine ⟨counterexampleOptimalDispatch, ?_, ?_⟩
  · -- The constant-one dispatch is feasible, and every feasible competitor coincides with it.
    constructor
    · exact (counterexample_feasible_iff_value_one counterexampleOptimalDispatch).2 (by simp
        [counterexampleOptimalDispatch])
    · intro q hq
      have hqeq := counterexample_feasible_eq_optimal q hq
      simpa [hqeq]
  · intro q hq
    -- Uniqueness follows because any optimal solution is in particular feasible.
    exact counterexample_feasible_eq_optimal q hq.1

/-- The distinguished optimizer selected from the unique existence proof is the constant-one dispatch. -/
lemma counterexample_p_eq_optimal :
    counterexampleDispatch.p counterexample_has_unique_optimal_solution =
      counterexampleOptimalDispatch := by
  -- The chosen optimizer is feasible, so the preceding uniqueness lemma identifies it.
  apply counterexample_feasible_eq_optimal
  exact (counterexampleDispatch.p_spec counterexample_has_unique_optimal_solution).1

/-- The selected optimizer restricted to the unique generator is the constant-one profile. -/
lemma counterexample_p_slice_eq_generator_point :
    counterexampleDispatch.p counterexample_has_unique_optimal_solution 0 =
      counterexampleGeneratorPoint := by
  -- Evaluating the full dispatch equality on the unique generator yields the slice equality.
  ext t
  fin_cases t
  have hp := congrArg (fun p => p 0 0) counterexample_p_eq_optimal
  simpa [counterexampleOptimalDispatch, counterexampleGeneratorPoint] using hp

/-- The zero single-generator profile satisfies the local constraints for any price. -/
lemma counterexample_generator_zero_feasible
    (Q : Fin 1 → ℝ) :
    (counterexampleDispatch.singleGeneratorProblem Q 0).IsFeasible counterexampleGeneratorZero := by
  -- In one period, feasibility reduces to the box constraints `0 ≤ q ≤ 2`.
  constructor
  · intro t
    fin_cases t
    constructor <;> norm_num [counterexampleDispatch, counterexampleGeneratorZero,
      MultiPeriodEconomicDispatch.singleGeneratorProblem]
  · intro t
    exact Fin.elim0 t

/-- The constant-two single-generator profile also satisfies the local constraints. -/
lemma counterexample_generator_two_feasible
    (Q : Fin 1 → ℝ) :
    (counterexampleDispatch.singleGeneratorProblem Q 0).IsFeasible counterexampleGeneratorTwo := by
  -- The upper endpoint `2` remains feasible because the ramp constraints are vacuous.
  constructor
  · intro t
    fin_cases t
    constructor <;> norm_num [counterexampleDispatch, counterexampleGeneratorTwo,
      MultiPeriodEconomicDispatch.singleGeneratorProblem]
  · intro t
    exact Fin.elim0 t

/-- Pointwise optimality of the local single-generator problem forces the price `Q₀ = 3`. -/
lemma counterexample_single_generator_optimality_forces_price_three
    (Q : Fin 1 → ℝ)
    (hopt :
      ∀ q : Fin 1 → ℝ,
        (counterexampleDispatch.singleGeneratorProblem Q 0).IsFeasible q →
        (counterexampleDispatch.singleGeneratorProblem Q 0).objective counterexampleGeneratorPoint ≤
          (counterexampleDispatch.singleGeneratorProblem Q 0).objective q) :
    Q 0 = 3 := by
  -- Comparing against the endpoints puts the unconstrained minimizer inside `[0, 2]`.
  have hzero := hopt counterexampleGeneratorZero (counterexample_generator_zero_feasible Q)
  have hQ_ge_two : 2 ≤ Q 0 := by
    have hzero' : 1 + 1 ≤ Q 0 := by
      simpa [SingleGeneratorDispatchProblem.objective, counterexampleDispatch,
        counterexampleGeneratorPoint, counterexampleGeneratorZero,
        MultiPeriodEconomicDispatch.singleGeneratorProblem] using hzero
    nlinarith
  have htwo := hopt counterexampleGeneratorTwo (counterexample_generator_two_feasible Q)
  have hQ_le_four : Q 0 ≤ 4 := by
    have htwo' : 1 + 1 ≤ 2 + 2 ^ 2 - Q 0 * 2 + Q 0 := by
      simpa [SingleGeneratorDispatchProblem.objective, counterexampleDispatch,
        counterexampleGeneratorPoint, counterexampleGeneratorTwo,
        MultiPeriodEconomicDispatch.singleGeneratorProblem] using htwo
    nlinarith
  let qMid : Fin 1 → ℝ := fun _ => (Q 0 - 1) / 2
  have hmidFeasible : (counterexampleDispatch.singleGeneratorProblem Q 0).IsFeasible qMid := by
    -- The midpoint is feasible because the endpoint comparisons gave `2 ≤ Q₀ ≤ 4`.
    constructor
    · intro t
      fin_cases t
      change 0 ≤ (Q 0 - 1) / 2 ∧ (Q 0 - 1) / 2 ≤ 2
      constructor <;> nlinarith
    · intro t
      exact Fin.elim0 t
  have hmid := hopt qMid hmidFeasible
  have hsquare_le_zero : (Q 0 - 3) ^ 2 ≤ 0 := by
    -- Evaluating at the unconstrained minimizer produces the square obstruction.
    simp [SingleGeneratorDispatchProblem.objective, counterexampleDispatch,
      counterexampleGeneratorPoint, MultiPeriodEconomicDispatch.singleGeneratorProblem, qMid] at hmid
    nlinarith
  have hsquare_nonneg : 0 ≤ (Q 0 - 3) ^ 2 := sq_nonneg (Q 0 - 3)
  nlinarith

/-- The zero dispatch satisfies the product-feasibility constraints of the counterexample. -/
lemma counterexample_zero_product_feasible :
    counterexampleDispatch.productFeasible counterexampleZeroDispatch := by
  -- Product feasibility is checked generator-by-generator, and there is only one generator.
  intro i
  fin_cases i
  constructor
  · intro t
    fin_cases t
    constructor <;> norm_num [counterexampleDispatch, counterexampleZeroDispatch,
      MultiPeriodEconomicDispatch.singleGeneratorProblem]
  · intro t
    exact Fin.elim0 t

/-- The theorem's claimed conclusion fails on the explicit one-generator, one-period instance. -/
lemma counterexample_specialization_is_false :
    ¬ ∃ Q : Fin 1 → ℝ,
      (∀ i : Fin 1,
        (counterexampleDispatch.singleGeneratorProblem Q i).IsFeasible
            (counterexampleDispatch.p counterexample_has_unique_optimal_solution i) ∧
        ∀ q : Fin 1 → ℝ,
          (counterexampleDispatch.singleGeneratorProblem Q i).IsFeasible q →
          (counterexampleDispatch.singleGeneratorProblem Q i).objective
              (counterexampleDispatch.p counterexample_has_unique_optimal_solution i) ≤
            (counterexampleDispatch.singleGeneratorProblem Q i).objective q) ∧
      ∀ q : Fin 1 → Fin 1 → ℝ,
        counterexampleDispatch.productFeasible q →
        @lagrangian
          (Fin 1 → Fin 1 → ℝ)
          (Fin 1)
          (Fin 0)
          inferInstance
          inferInstance
          (fun q : Fin 1 → Fin 1 → ℝ => counterexampleDispatch.objective q)
          (fun t q => ∑ i, q i t - counterexampleDispatch.d t)
          (fun _ _ => 0)
          (counterexampleDispatch.p counterexample_has_unique_optimal_solution)
          Q
          (fun k => 0) ≤
        @lagrangian
          (Fin 1 → Fin 1 → ℝ)
          (Fin 1)
          (Fin 0)
          inferInstance
          inferInstance
          (fun q : Fin 1 → Fin 1 → ℝ => counterexampleDispatch.objective q)
          (fun t q => ∑ i, q i t - counterexampleDispatch.d t)
          (fun _ _ => 0)
          q
          Q
          (fun k => 0) := by
  intro hclaim
  rcases hclaim with ⟨Q, hsingle, hlagrangian⟩
  have hsingle_opt :
      ∀ q : Fin 1 → ℝ,
        (counterexampleDispatch.singleGeneratorProblem Q 0).IsFeasible q →
        (counterexampleDispatch.singleGeneratorProblem Q 0).objective counterexampleGeneratorPoint ≤
          (counterexampleDispatch.singleGeneratorProblem Q 0).objective q := by
    intro q hq
    -- The theorem's local optimality statement specializes to the unique generator.
    have hqopt := (hsingle 0).2 q hq
    simpa [counterexample_p_slice_eq_generator_point] using hqopt
  have hQ : Q 0 = 3 :=
    counterexample_single_generator_optimality_forces_price_three Q hsingle_opt
  have hzero := hlagrangian counterexampleZeroDispatch counterexample_zero_product_feasible
  have hp00 : counterexampleDispatch.p counterexample_has_unique_optimal_solution 0 0 = 1 := by
    -- Evaluating the selected optimizer at the unique coordinate recovers the scalar value `1`.
    have hp := congrArg (fun p => p 0 0) counterexample_p_eq_optimal
    simpa [counterexampleOptimalDispatch] using hp
  have hcontradiction : (2 : ℝ) ≤ -3 := by
    -- Route correction: the local objectives force `Q₀ = 3`, but the global Lagrangian
    -- then ranks the product-feasible zero dispatch strictly below the claimed optimizer.
    have hzero' :
        counterexampleDispatch.p counterexample_has_unique_optimal_solution 0 0 +
            (counterexampleDispatch.p counterexample_has_unique_optimal_solution 0 0) ^ 2 +
            3 * (counterexampleDispatch.p counterexample_has_unique_optimal_solution 0 0 - 1) ≤
          -3 := by
      simpa [lagrangian, MultiPeriodEconomicDispatch.objective, MultiPeriodEconomicDispatch.phi,
        MultiPeriodEconomicDispatch.psi, counterexampleDispatch, counterexampleZeroDispatch,
        counterexampleOptimalDispatch, counterexample_p_eq_optimal, hQ] using hzero
    nlinarith [hp00, hzero']
  norm_num at hcontradiction

/-- Any uniform proof of the theorem's conclusion is refuted by the explicit counterexample. -/
lemma counterexample_refutes_general_price_multiplier_statement :
    (∀ {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T)
        (hunique_optimal : ∃! pStar : Fin n → Fin T → ℝ, prob.IsOptimalSolution pStar),
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
            (fun k => 0)) → False := by
  intro hgeneral
  -- Route correction: specializing the purported general theorem to the explicit
  -- one-generator counterexample yields exactly the existential ruled out above.
  exact counterexample_specialization_is_false
    (hgeneral (n := 1) (T := 1) counterexampleDispatch
      counterexample_has_unique_optimal_solution)

/-- The target theorem statement is formally refuted by the explicit counterexample. -/
private lemma target_statement_is_false :
    ¬ (∀ {n T : ℕ} (prob : MultiPeriodEconomicDispatch n T)
        (hunique_optimal : ∃! pStar : Fin n → Fin T → ℝ, prob.IsOptimalSolution pStar),
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
            (fun k => 0)) := by
  -- Route correction: the counterexample already proves that the fully quantified
  -- statement behind the target theorem cannot hold, so the obstruction is semantic.
  intro htarget
  exact counterexample_refutes_general_price_multiplier_statement htarget

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
  -- Route correction: this is not a missing-library or local-proof-search failure.
  -- The preceding counterexample lemmas already show that the quantified statement
  -- asserted here specializes to a contradiction on `counterexampleDispatch`.
  -- Route correction: the obstruction is semantic, not tactical. Specializing
  -- this theorem to `counterexampleDispatch` and
  -- `counterexample_has_unique_optimal_solution` yields the existential claim
  -- refuted by `counterexample_specialization_is_false`, and
  -- `counterexample_refutes_general_price_multiplier_statement` packages that
  -- specialization into the negation of the fully quantified statement.
  -- The failure comes from the sign mismatch between the single-generator term
  -- `- Q t * q t` and the global Lagrangian term
  -- `+ Q t * (∑ i, q i t - prob.d t)`: in the counterexample the local
  -- optimality clause forces `Q 0 = 3`, while the global inequality at
  -- `counterexampleZeroDispatch` simplifies to the impossible claim `2 ≤ -3`.
  -- The contradiction is recorded concretely in
  -- `counterexample_specialization_is_false` and abstracted as
  -- `target_statement_is_false`; that private lemma negates the fully quantified
  -- proposition proved by this theorem, so any proof term here would be inconsistent.
  -- In particular, `counterexample_refutes_general_price_multiplier_statement`
  -- shows that any universal proof of this theorem would specialize to `False`.
  -- Exact formal negation: `target_statement_is_false` proves `¬ P` for the
  -- proposition `P` asserted by this theorem.
  -- Bad-statement placeholder: there is no term of this type in the current theory,
  -- because the file already proves the negation of this exact proposition.
  -- Route correction: the right next step is not another tactic search here,
  -- but an external repair of the statement's price-sign convention.
  -- Lean-level conflict: a completed proof of this declaration would instantiate
  -- the universal proposition already negated by `target_statement_is_false`.
  -- Counterexample witness: specialize to `counterexampleDispatch`, obtain
  -- `Q 0 = 3` from the local optimality clause, and then the global Lagrangian
  -- inequality at `counterexampleZeroDispatch` collapses to `2 ≤ -3`.
  -- No extra feasibility or uniqueness assumption repairs this instance; the
  -- defect is the sign convention built into the theorem statement itself.
  -- Consequently, any completed proof term here would combine with
  -- `target_statement_is_false` to yield `False`.
  -- This placeholder remains only so the file stays compilable while reporting
  -- the theorem as a bad statement to the orchestrator.
  -- Bad-statement note: this declaration is mathematically false as written,
  -- not a missing-proof artifact. Repair it outside this prover run by aligning
  -- the local objective term
  -- `- Q t * q t` with the global multiplier term
  -- `+ Q t * (∑ i, q i t - prob.d t)`; no extra feasibility or uniqueness
  -- hypothesis repairs the contradiction exhibited by `counterexampleDispatch`.
  -- After that sign correction, replace this placeholder with a proof of the
  -- corrected proposition.
  sorry

end «problem-86»
