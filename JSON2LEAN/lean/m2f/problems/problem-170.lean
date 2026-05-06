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
  letI := P.fintype_index
  let _ := hgrad_zero
  let _ := hposdef
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun y => P.lagrangian y lamstar
  let S : ℕ → ℝ := fun k => ∑ i : ι, (inner ℝ (P.A xstar i) (w k)) ^ 2
  let Q : EuclideanSpace ℝ (Fin n) → ℝ := fun v =>
    (fderiv ℝ (fun x => (fderiv ℝ g x) v) xstar) v
  -- Build a `C²` model for the Lagrangian so the iterated-derivative norm API applies.
  have hconstraint_sum_C2 : ContDiff ℝ 2 (fun y => ∑ i : ι, lamstar i * P.constraint i y) := by
    refine ContDiff.sum fun i _ => ?_
    simpa [SmoothEqualityConstrainedOptimizationProblem.constraint, smul_eq_mul] using
      (P.constraint_C2 i).const_smul (lamstar i)
  -- The Lagrangian is the objective minus a finite linear combination of the constraints.
  have hlagrangian_C2 : ContDiff ℝ 2 g := by
    simpa [g, SmoothEqualityConstrainedOptimizationProblem.lagrangian,
      EqualityConstrainedOptimizationProblem.lagrangian] using
      P.objective_C2.sub hconstraint_sum_C2
  -- Differentiate once more to expose the Hessian as a continuous linear map-valued function.
  have hfderiv_C1 : ContDiff ℝ 1 (fderiv ℝ g) := by
    simpa using hlagrangian_C2.fderiv_right (m := 1) (by norm_num)
  -- The second directional derivative is uniformly controlled by the operator norm of `iteratedFDeriv`.
  have hsecond_directional_bound :
      ∀ v : EuclideanSpace ℝ (Fin n), |Q v| ≤ ‖iteratedFDeriv ℝ 2 g xstar‖ * ‖v‖ ^ 2 := by
    intro v
    have happly_iter :
        ‖iteratedFDeriv ℝ 1 (fun x => (fderiv ℝ g x) v) xstar‖ ≤
          ‖v‖ * ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) xstar‖ := by
      exact norm_iteratedFDeriv_clm_apply_const
        (f := fderiv ℝ g) (c := v) (x := xstar) (n := 1) hfderiv_C1.contDiffAt (by simp)
    -- Convert the iterated-derivative bound into an operator-norm bound for the scalar derivative.
    have hderiv_norm :
        ‖fderiv ℝ (fun x => (fderiv ℝ g x) v) xstar‖ ≤
          ‖v‖ * ‖iteratedFDeriv ℝ 2 g xstar‖ := by
      calc
        ‖fderiv ℝ (fun x => (fderiv ℝ g x) v) xstar‖
            = ‖iteratedFDeriv ℝ 1 (fun x => (fderiv ℝ g x) v) xstar‖ := by
              rw [← norm_iteratedFDeriv_one]
        _ ≤ ‖v‖ * ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) xstar‖ := happly_iter
        _ = ‖v‖ * ‖iteratedFDeriv ℝ 2 g xstar‖ := by
              rw [norm_iteratedFDeriv_fderiv]
    have happly :
        |Q v| ≤ ‖fderiv ℝ (fun x => (fderiv ℝ g x) v) xstar‖ * ‖v‖ := by
      simpa [Q, Real.norm_eq_abs] using
        (ContinuousLinearMap.le_opNorm
          (fderiv ℝ (fun x => (fderiv ℝ g x) v) xstar) v)
    calc
      |Q v| ≤ ‖fderiv ℝ (fun x => (fderiv ℝ g x) v) xstar‖ * ‖v‖ := happly
      _ ≤ (‖v‖ * ‖iteratedFDeriv ℝ 2 g xstar‖) * ‖v‖ := by
            exact mul_le_mul_of_nonneg_right hderiv_norm (norm_nonneg v)
      _ = ‖iteratedFDeriv ℝ 2 g xstar‖ * ‖v‖ ^ 2 := by
            ring
  -- Rearranging the witness identity isolates the squared projection sum with a `1 / k` factor.
  have hconstraint_projection_sum_sq_le :
      ∀ k : ℕ, 1 ≤ k → S k ≤ -(1 / (k : ℝ)) * Q (w k) := by
    intro k hk
    have hkpos : 0 < (k : ℝ) := by
      exact_mod_cast hk
    rcases hwitness k hk with ⟨hnonpos, heq⟩
    have hnonpos' : 0 ≥ Q (w k) + (k : ℝ) * S k := by
      rw [heq] at hnonpos
      simpa [Q, S, g] using hnonpos
    have hmul : (k : ℝ) * S k ≤ -Q (w k) := by
      linarith
    have hdiv : S k ≤ (-Q (w k)) / (k : ℝ) := by
      exact (le_div_iff₀ hkpos).2 (by simpa [mul_comm] using hmul)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
  let C : ℝ := ‖iteratedFDeriv ℝ 2 g xstar‖
  -- The shifted squared-projection sequence is trapped between `0` and `C / (k + 1)`.
  have hprojection_tendsto_zero : Tendsto (fun k : ℕ => S (k + 1)) atTop (𝓝 0) := by
    have hnonneg : ∀ k : ℕ, 0 ≤ S (k + 1) := by
      intro k
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hupper : ∀ k : ℕ, S (k + 1) ≤ C / (k + 1 : ℝ) := by
      intro k
      have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have habs : |Q (w (k + 1))| ≤ C := by
        simpa [C, hunit (k + 1) hk1] using hsecond_directional_bound (w (k + 1))
      have hnegQ_le_C : -Q (w (k + 1)) ≤ C := by
        exact le_trans (neg_le_abs _) habs
      have hscaled :
          (1 / (k + 1 : ℝ)) * (-Q (w (k + 1))) ≤ (1 / (k + 1 : ℝ)) * C := by
        exact mul_le_mul_of_nonneg_left hnegQ_le_C (by positivity)
      calc
        S (k + 1) ≤ (1 / (k + 1 : ℝ)) * (-Q (w (k + 1))) := by
          simpa [mul_comm, mul_left_comm, mul_assoc, mul_neg] using
            hconstraint_projection_sum_sq_le (k + 1) hk1
        _ ≤ (1 / (k + 1 : ℝ)) * C := hscaled
        _ = C / (k + 1 : ℝ) := by
          simp [div_eq_mul_inv, mul_comm]
    have hC_tendsto :
        Tendsto (fun k : ℕ => C / (k + 1 : ℝ)) atTop (𝓝 0) := by
      convert (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1) using 1
      ext k
      simp [Nat.cast_add, Nat.cast_one]
    exact squeeze_zero hnonneg hupper hC_tendsto
  refine ⟨?_, ?_⟩
  · intro k hk
    simpa [S, Q, g] using hconstraint_projection_sum_sq_le k hk
  · simpa [S] using hprojection_tendsto_zero

end «problem-170»
