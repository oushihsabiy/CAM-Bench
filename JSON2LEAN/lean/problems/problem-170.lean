import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-170»

/- [BLOCK Exercise UNKNOWN | 15 | defn]
An equality-constrained optimization problem is an optimization problem of the form min_x f(x)
subject to cᵢ(x)=0 for all constraint indices i.
-/
structure EqualityConstrainedOptimizationProblem (α ι : Type*) where
  objective : α → ℝ
  constraint : ι → α → ℝ

def EqualityConstrainedOptimizationProblem.IsFeasible
    {α ι : Type*} (P : EqualityConstrainedOptimizationProblem α ι) (x : α) : Prop :=
  ∀ i : ι, P.constraint i x = 0

def EqualityConstrainedOptimizationProblem.feasibleSet
    {α ι : Type*} (P : EqualityConstrainedOptimizationProblem α ι) : Set α :=
  {x | P.IsFeasible x}

/- [BLOCK Exercise UNKNOWN | 16 | defn]
Given equality constraints cᵢ(x)=0, the augmented Lagrangian is the function mathcal
L_A(x,λ;μ)=mathcal L(x,λ)+(μ)/(2)sum_i cᵢ(x)^2, where mathcal L(x,λ)=f(x)-sum_i λ_i cᵢ(x).
-/
def EqualityConstrainedOptimizationProblem.augmentedLagrangian
    {α ι : Type*} [Fintype ι]
    (P : EqualityConstrainedOptimizationProblem α ι) (x : α) (lam : ι → ℝ) (μ : ℝ) : ℝ :=
  (P.objective x - ∑ i : ι, lam i * P.constraint i x) + (μ / 2) * ∑ i : ι, (P.constraint i x)^2

def EqualityConstrainedOptimizationProblem.lagrangian
    {α ι : Type*} [Fintype ι]
    (P : EqualityConstrainedOptimizationProblem α ι) (x : α) (lam : ι → ℝ) : ℝ :=
  P.objective x - ∑ i : ι, lam i * P.constraint i x

/- [BLOCK Exercise UNKNOWN | 17 | defn]
For the equality-constrained problem min_x f(x) subject to cᵢ(x)=0, the Lagrangian is mathcal
L(x,λ)=f(x)-sum_i λ_i cᵢ(x).
-/
def EqualityConstrainedOptimizationProblem.Lagrangian
    {α ι : Type*} [Fintype ι]
    (P : EqualityConstrainedOptimizationProblem α ι) (x : α) (lam : ι → ℝ) : ℝ :=
  P.lagrangian x lam

/- [BLOCK Exercise UNKNOWN | 18 | opt_prob]
Consider the equality-constrained optimization problem
min_x f(x) quad subject to cᵢ(x)=0, quad i∈E,
where f:ℝ^n→ℝ and cᵢ:ℝ^n→ℝ are twice continuously differentiable, E is a finite index set, and
A(x)ᵀ=[∇ cᵢ(x)]_{i∈E}.
-/
structure SmoothEqualityConstrainedOptimizationProblem (n : ℕ) (ι : Type*) where
  toProblem : EqualityConstrainedOptimizationProblem (EuclideanSpace ℝ (Fin n)) ι
  fintype_index : Fintype ι
  objective_C2 : ContDiff ℝ 2 toProblem.objective
  constraint_C2 : ∀ i : ι, ContDiff ℝ 2 (toProblem.constraint i)

def SmoothEqualityConstrainedOptimizationProblem.A
    {n : ℕ} {ι : Type*} (P : SmoothEqualityConstrainedOptimizationProblem n ι)
    (x : EuclideanSpace ℝ (Fin n)) : ι → EuclideanSpace ℝ (Fin n) :=
  fun i => ∇ (P.toProblem.constraint i) x

def SmoothEqualityConstrainedOptimizationProblem.objective
    {n : ℕ} {ι : Type*} (P : SmoothEqualityConstrainedOptimizationProblem n ι) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  P.toProblem.objective

def SmoothEqualityConstrainedOptimizationProblem.constraint
    {n : ℕ} {ι : Type*} (P : SmoothEqualityConstrainedOptimizationProblem n ι) :
    ι → EuclideanSpace ℝ (Fin n) → ℝ :=
  P.toProblem.constraint

def SmoothEqualityConstrainedOptimizationProblem.IsFeasible
    {n : ℕ} {ι : Type*} (P : SmoothEqualityConstrainedOptimizationProblem n ι)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  P.toProblem.IsFeasible x

def SmoothEqualityConstrainedOptimizationProblem.feasibleSet
    {n : ℕ} {ι : Type*} (P : SmoothEqualityConstrainedOptimizationProblem n ι) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  P.toProblem.feasibleSet

def SmoothEqualityConstrainedOptimizationProblem.lagrangian
    {n : ℕ} {ι : Type*} (P : SmoothEqualityConstrainedOptimizationProblem n ι)
    (x : EuclideanSpace ℝ (Fin n)) (lam : ι → ℝ) : ℝ :=
  letI := P.fintype_index
  P.toProblem.lagrangian x lam

def SmoothEqualityConstrainedOptimizationProblem.augmentedLagrangian
    {n : ℕ} {ι : Type*} (P : SmoothEqualityConstrainedOptimizationProblem n ι)
    (x : EuclideanSpace ℝ (Fin n)) (lam : ι → ℝ) (μ : ℝ) : ℝ :=
  letI := P.fintype_index
  P.toProblem.augmentedLagrangian x lam μ

/- [BLOCK Exercise UNKNOWN | 19 | thm]
Consider the equality-constrained optimization problem. Let L(x,λ)=f(x)-sum_{i∈E} λ_i cᵢ(x) and
L_A(x,λ;μ)=L(x,λ)+(μ)/(2)sum_{i∈E} cᵢ(x)^2. Assume that for some point (x*,λ^*) and some μ∈ℝ, ∇_x
L_A(x*,λ^*;μ)=0, ∇_{xx}^2 L_A(x*,λ^*;μ) is positive definite. Assume also that for each integer k≥
1, there exists wₖ∈ℝ^n with ‖wₖ‖=1 such that 0 ≥ w_kᵀ ∇_{xx}^2 L_A(x*,λ^*;k) wₖ = w_kᵀ ∇_{xx}^2
L(x*,λ^*) wₖ + k‖A(x*)wₖ‖_2^2. Show that ‖A(x*)wₖ‖_2^2 ≤ -(1)/(k) w_kᵀ ∇_{xx}^2 L(x*,λ^*) wₖ → 0
quad as k→∞. Here ‖·‖_2 denotes the Euclidean norm.
-/
open scoped RealInnerProductSpace

theorem norm_A_mul_le_and_tendsto_zero_of_hessian_identity
    {n : ℕ} {ι : Type*}
    (P : SmoothEqualityConstrainedOptimizationProblem n ι)
    (xstar : EuclideanSpace ℝ (Fin n))
    (lamstar : ι → ℝ)
    (μ : ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin n))
    (hgrad_zero :
      fderiv ℝ (fun x => P.augmentedLagrangian x lamstar μ) xstar = 0)
    (hposdef :
      ∃ c : ℝ, c > 0 ∧
        ∀ v : EuclideanSpace ℝ (Fin n),
          c * ‖v‖ ^ 2 ≤
            (fderiv ℝ
              (fun x => (fderiv ℝ (fun y => P.augmentedLagrangian y lamstar μ) x) v)
              xstar) v)
    (hunit : ∀ k : ℕ, 1 ≤ k → ‖w k‖ = 1)
    (hwitness :
      ∀ k : ℕ, 1 ≤ k →
        (letI := P.fintype_index
         0 ≥
          (fderiv ℝ
            (fun x => (fderiv ℝ (fun y => P.augmentedLagrangian y lamstar (k : ℝ)) x) (w k))
            xstar) (w k) ∧
         (fderiv ℝ
            (fun x => (fderiv ℝ (fun y => P.augmentedLagrangian y lamstar (k : ℝ)) x) (w k))
            xstar) (w k) =
          (fderiv ℝ
            (fun x => (fderiv ℝ (fun y => P.lagrangian y lamstar) x) (w k))
            xstar) (w k) +
            (k : ℝ) * ∑ i : ι, (inner ℝ (P.A xstar i) (w k)) ^ 2)) :
    letI := P.fintype_index
    (∀ k : ℕ, 1 ≤ k →
      (∑ i : ι, (inner ℝ (P.A xstar i) (w k)) ^ 2) ≤
        -(1 / (k : ℝ)) *
          ((fderiv ℝ
            (fun x => (fderiv ℝ (fun y => P.lagrangian y lamstar) x) (w k))
            xstar) (w k))) ∧
    Tendsto
      (fun k : ℕ => ∑ i : ι, (inner ℝ (P.A xstar i) (w (k + 1))) ^ 2) atTop (𝓝 0) := by
  sorry

end «problem-170»