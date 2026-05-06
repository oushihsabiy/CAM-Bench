import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators
open scoped Pointwise

namespace «problem-82»

-- Exercise_13_22__a_

/- [BLOCK Exercise 13.22-(a) | 15 | opt_prob]
Let n,M ∈ ℕ with M ≥ 1, let μ ∈ ℝ^n, let γ > 0, and for each k=1,ldots,M, let σ^{(k)} ∈ S_{++}^n,
where S_{++}^n denotes the set of real symmetric positive definite n × n matrices. Let 1 ∈ ℝ^n
denote the all-ones vector. Consider the problem
aligned
maximize quad & μᵀ w - γ max_{k=1,ldots,M} wᵀ σ^{(k)} w ;
subject to quad & 1ᵀ w = 1,
aligned
over w ∈ ℝ^n, and suppose that w^{star} ∈ ℝ^n is an optimal solution.
-/
open Matrix

structure RobustMeanVariancePortfolioProblem where
  n : ℕ
  M : ℕ
  hM : 1 ≤ M
  μ : Fin n → ℝ
  γ : ℝ
  hγ : 0 < γ
  Sigma : Fin M → Matrix (Fin n) (Fin n) ℝ
  Sigma_symm : ∀ k : Fin M, (Sigma k).IsSymm
  Sigma_pos : ∀ k : Fin M, PosDef (Sigma k)
  wStar : Fin n → ℝ

def RobustMeanVariancePortfolioProblem.objective
    (P : RobustMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : ℝ :=
  (∑ i : Fin P.n, P.μ i * w i) -
    P.γ * sSup (Set.range fun k : Fin P.M => dotProduct w (P.Sigma k *ᵥ w))

def RobustMeanVariancePortfolioProblem.isFeasible
    (P : RobustMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  (∑ i : Fin P.n, w i) = 1

def RobustMeanVariancePortfolioProblem.isOptimalSolution
    (P : RobustMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  P.isFeasible w ∧ ∀ z : Fin P.n → ℝ, P.isFeasible z → P.objective z ≤ P.objective w

/- [BLOCK Exercise 13.22-(a) | 16 | opt_prob]
Consider the problem
aligned
maximize quad & μᵀ w - sum_{k=1}^M γ_k wᵀ σ^{(k)} w ;
subject to quad & 1ᵀ w = 1,
aligned
over w ∈ ℝ^n.
-/
structure WeightedMeanVariancePortfolioProblem where
  n : ℕ
  M : ℕ
  hM : 1 ≤ M
  μ : Fin n → ℝ
  γ : Fin M → ℝ
  hγ : ∀ k : Fin M, 0 ≤ γ k
  Sigma : Fin M → Matrix (Fin n) (Fin n) ℝ
  Sigma_symm : ∀ k : Fin M, (Sigma k).IsSymm
  Sigma_pos : ∀ k : Fin M, PosDef (Sigma k)

def WeightedMeanVariancePortfolioProblem.objective
    (P : WeightedMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : ℝ :=
  (∑ i : Fin P.n, P.μ i * w i) -
    ∑ k : Fin P.M, P.γ k * dotProduct w (P.Sigma k *ᵥ w)

def WeightedMeanVariancePortfolioProblem.isFeasible
    (P : WeightedMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  (∑ i : Fin P.n, w i) = 1

def WeightedMeanVariancePortfolioProblem.isOptimalSolution
    (P : WeightedMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  P.isFeasible w ∧ ∀ z : Fin P.n → ℝ, P.isFeasible z → P.objective z ≤ P.objective w

/-- For a symmetric covariance matrix, the mixed quadratic terms can be swapped. -/
lemma dotProduct_mulVec_swap {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsSymm) (x y : n → ℝ) :
    dotProduct x (A *ᵥ y) = dotProduct y (A *ᵥ x) := by
  -- Rewrite the left factor as a row-vector multiplication.
  rw [dotProduct_mulVec]
  -- Symmetry turns the row action back into the corresponding column action.
  have hvec : x ᵥ* A = A *ᵥ x := by
    simpa [hA.eq] using (vecMul_transpose A x)
  -- The remaining scalar dot product is symmetric over `ℝ`.
  rw [hvec, dotProduct_comm]

/-- Expanding a symmetric quadratic form along a perturbation isolates the linear and quadratic
error terms. -/
lemma quadratic_form_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (w d : Fin n → ℝ) :
    dotProduct (w + d) (A *ᵥ (w + d)) =
      dotProduct w (A *ᵥ w) + 2 * dotProduct d (A *ᵥ w) + dotProduct d (A *ᵥ d) := by
  -- Expand both the matrix multiplication and the dot product.
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
  -- Symmetry identifies the two mixed terms.
  have hswap := dotProduct_mulVec_swap A hA w d
  -- The remaining identity is scalar arithmetic.
  linarith

/-- Two feasible portfolios differ by a direction whose coordinates sum to zero. -/
lemma feasible_sub_sum_eq_zero {n : ℕ} {w z : Fin n → ℝ}
    (hw : (∑ i : Fin n, w i) = 1) (hz : (∑ i : Fin n, z i) = 1) :
    (∑ i : Fin n, (z i - w i)) = 0 := by
  -- Subtract the two budget constraints coordinatewise.
  rw [Finset.sum_sub_distrib, hz, hw, sub_self]

/-- Expanding the weighted quadratic penalty along a perturbation `d` expresses the change as a
sum of linear and quadratic terms in `d`. -/
lemma weighted_quadratic_penalty_add {n M : ℕ} (γw : Fin M → ℝ)
    (Sigma : Fin M → Matrix (Fin n) (Fin n) ℝ) (w d : Fin n → ℝ)
    (hSigma : ∀ k : Fin M, (Sigma k).IsSymm) :
    (∑ k : Fin M, γw k * dotProduct (w + d) (Sigma k *ᵥ (w + d))) -
      ∑ k : Fin M, γw k * dotProduct w (Sigma k *ᵥ w) =
    ∑ k : Fin M,
      (2 * γw k * dotProduct d (Sigma k *ᵥ w) + γw k * dotProduct d (Sigma k *ᵥ d)) := by
  -- Expand each symmetric quadratic form separately.
  simp_rw [quadratic_form_add _ (hSigma _) w d, mul_add]
  -- Then cancel the base-point contribution term by term inside the sum.
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  ring

/-- The weighted objective difference between `w` and `w + d` splits into a linear return term and
the expanded quadratic penalty from `weighted_quadratic_penalty_add`. -/
lemma weighted_objective_difference_add {n M : ℕ} (μ : Fin n → ℝ) (γw : Fin M → ℝ)
    (Sigma : Fin M → Matrix (Fin n) (Fin n) ℝ) (w d : Fin n → ℝ)
    (hSigma : ∀ k : Fin M, (Sigma k).IsSymm) :
    ((∑ i : Fin n, μ i * (w i + d i)) -
        ∑ k : Fin M, γw k * dotProduct (w + d) (Sigma k *ᵥ (w + d))) -
      ((∑ i : Fin n, μ i * w i) -
        ∑ k : Fin M, γw k * dotProduct w (Sigma k *ᵥ w)) =
    (∑ i : Fin n, μ i * d i) -
      ∑ k : Fin M,
        (2 * γw k * dotProduct d (Sigma k *ᵥ w) + γw k * dotProduct d (Sigma k *ᵥ d)) := by
  -- First isolate the linear return increment.
  have hlin :
      (∑ i : Fin n, μ i * (w i + d i)) - ∑ i : Fin n, μ i * w i =
        ∑ i : Fin n, μ i * d i := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    ring
  -- Then plug in the quadratic expansion proved above.
  have hquad := weighted_quadratic_penalty_add γw Sigma w d hSigma
  -- The objective difference is the linear increment minus the quadratic increment.
  linarith

/-- The coordinate-sum functional on `Fin n → ℝ`. -/
def coordinateSumLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.lsum ℝ (fun _ : Fin n => ℝ) ℝ (fun _ => LinearMap.id)

/-- Evaluating `coordinateSumLinear` recovers the budget sum. -/
@[simp] lemma coordinateSumLinear_apply (n : ℕ) (d : Fin n → ℝ) :
    coordinateSumLinear n d = ∑ i : Fin n, d i := by
  -- `LinearMap.lsum` sums the coordinate projections over the finite product.
  simp [coordinateSumLinear, LinearMap.lsum_apply]

/-- The zero-sum direction subspace for the budget constraint. -/
def budgetDir (P : RobustMeanVariancePortfolioProblem) : Submodule ℝ (Fin P.n → ℝ) :=
  LinearMap.ker (coordinateSumLinear P.n)

/-- Membership in `budgetDir` means that the coordinates sum to zero. -/
@[simp] lemma mem_budgetDir_iff (P : RobustMeanVariancePortfolioProblem) (d : Fin P.n → ℝ) :
    d ∈ budgetDir P ↔ (∑ i : Fin P.n, d i) = 0 := by
  -- The kernel condition unfolds to the coordinate-sum equation.
  simp [budgetDir]

/-- The linear return functional on the ambient portfolio space. -/
def returnLinear (P : RobustMeanVariancePortfolioProblem) : (Fin P.n → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.lsum ℝ (fun _ : Fin P.n => ℝ) ℝ (fun i => P.μ i • LinearMap.id)

/-- Evaluating `returnLinear` gives the linear return increment. -/
@[simp] lemma returnLinear_apply (P : RobustMeanVariancePortfolioProblem) (d : Fin P.n → ℝ) :
    returnLinear P d = ∑ i : Fin P.n, P.μ i * d i := by
  -- The coordinatewise weighted sum is exactly the return pairing with `μ`.
  simp [returnLinear, LinearMap.lsum_apply, mul_comm]

/-- The ambient linearized quadratic gradient corresponding to covariance matrix `k`. -/
def gradientLinear (P : RobustMeanVariancePortfolioProblem) (k : Fin P.M) :
    (Fin P.n → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.lsum ℝ (fun _ : Fin P.n => ℝ) ℝ
    (fun i => (2 * (P.Sigma k *ᵥ P.wStar) i) • LinearMap.id)

/-- Evaluating `gradientLinear` gives the directional derivative of the quadratic term at
`P.wStar`. -/
@[simp] lemma gradientLinear_apply (P : RobustMeanVariancePortfolioProblem) (k : Fin P.M)
    (d : Fin P.n → ℝ) :
    gradientLinear P k d = 2 * dotProduct d (P.Sigma k *ᵥ P.wStar) := by
  -- Expand the coordinatewise linear combination and regroup the scalar factors.
  calc
    gradientLinear P k d
        = ∑ i : Fin P.n, (2 * (P.Sigma k *ᵥ P.wStar) i) * d i := by
            simp [gradientLinear, LinearMap.lsum_apply]
    _ = ∑ i : Fin P.n, 2 * (d i * (P.Sigma k *ᵥ P.wStar) i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = 2 * dotProduct d (P.Sigma k *ᵥ P.wStar) := by
          simp [dotProduct, Finset.mul_sum]

/-- The return functional restricted to budget-preserving directions. -/
def returnForm (P : RobustMeanVariancePortfolioProblem) : Module.Dual ℝ (budgetDir P) :=
  (returnLinear P).comp (budgetDir P).subtype

/-- The restricted return functional evaluates by forgetting the subtype. -/
@[simp] lemma returnForm_apply (P : RobustMeanVariancePortfolioProblem) (d : budgetDir P) :
    returnForm P d = ∑ i : Fin P.n, P.μ i * d.1 i := by
  -- Restricting along the subtype does not change the underlying formula.
  simp [returnForm]

/-- The linearized quadratic gradient restricted to budget-preserving directions. -/
def gradientForm (P : RobustMeanVariancePortfolioProblem) (k : Fin P.M) :
    Module.Dual ℝ (budgetDir P) :=
  (gradientLinear P k).comp (budgetDir P).subtype

/-- The restricted gradient functional evaluates by forgetting the subtype. -/
@[simp] lemma gradientForm_apply (P : RobustMeanVariancePortfolioProblem) (k : Fin P.M)
    (d : budgetDir P) :
    gradientForm P k d = 2 * dotProduct d.1 (P.Sigma k *ᵥ P.wStar) := by
  -- The restriction only changes the domain, not the explicit directional derivative formula.
  simp [gradientForm]

/-- Positive scalar multiplication carries the gradient range to the weighted gradient range. -/
lemma scaled_gradient_range_eq (P : RobustMeanVariancePortfolioProblem) (d : budgetDir P) :
    Set.range (fun k : Fin P.M => (P.γ • gradientForm P k) d) =
      P.γ • Set.range (fun k : Fin P.M => gradientForm P k d) := by
  -- Both sets are just two presentations of the same scaled finite family.
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨gradientForm P k d, ⟨k, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, rfl⟩

/-- Optimality at `wStar` bounds the return functional on every budget-preserving direction by the
support function of the weighted linearized quadratic gradients. -/
lemma robust_directional_upper_bound (P : RobustMeanVariancePortfolioProblem)
    (hwStar_optimal : P.isOptimalSolution P.wStar) (d : budgetDir P) :
    returnForm P d ≤ sSup (Set.range fun k : Fin P.M => (P.γ • gradientForm P k) d) := by
  letI : Nonempty (Fin P.M) := ⟨⟨0, P.hM⟩⟩
  -- Route correction: instead of picking a single active covariance matrix, we compare `P.wStar`
  -- with a small feasible perturbation and use the finite support bound for all `k` at once.
  let base : Fin P.M → ℝ := fun k => dotProduct P.wStar (P.Sigma k *ᵥ P.wStar)
  let grad : Fin P.M → ℝ := fun k => gradientForm P k d
  let quad : Fin P.M → ℝ := fun k => dotProduct d.1 (P.Sigma k *ᵥ d.1)
  let baseSup : ℝ := sSup (Set.range base)
  let gradSup : ℝ := sSup (Set.range grad)
  let quadSup : ℝ := sSup (Set.range quad)
  have hgradScaled :
      sSup (Set.range fun k : Fin P.M => (P.γ • gradientForm P k) d) = P.γ * gradSup := by
    -- Positive scaling commutes with the supremum on a nonempty real set.
    rw [scaled_gradient_range_eq]
    simpa [grad, gradSup, smul_eq_mul] using
      (Real.sSup_smul_of_nonneg P.hγ.le (Set.range fun k : Fin P.M => grad k))
  rw [hgradScaled]
  by_contra hlt
  have hgap : 0 < returnForm P d - P.γ * gradSup := sub_pos.mpr (lt_of_not_ge hlt)
  obtain ⟨t, ht_pos, ht_gap⟩ := exists_pos_mul_lt hgap (P.γ * quadSup)
  let z : Fin P.n → ℝ := P.wStar + t • d.1
  have hd_zero : (∑ i : Fin P.n, d.1 i) = 0 := mem_budgetDir_iff P d.1 |>.mp d.2
  have hz_feasible : P.isFeasible z := by
    -- The perturbation stays in the budget hyperplane because `d` has zero coordinate sum.
    dsimp [RobustMeanVariancePortfolioProblem.isFeasible, z]
    rw [Finset.sum_add_distrib, hwStar_optimal.1]
    have hscaled_zero : (∑ i : Fin P.n, t * d.1 i) = 0 := by
      simpa [Finset.mul_sum] using congrArg (fun x : ℝ => t * x) hd_zero
    linarith
  have hlinear :
      (∑ i : Fin P.n, P.μ i * z i) =
        (∑ i : Fin P.n, P.μ i * P.wStar i) + t * returnForm P d := by
    -- Expanding the return term isolates the directional increment `returnForm P d`.
    dsimp [z]
    simp [returnForm_apply, Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_assoc, mul_comm]
  have hquad_expand (k : Fin P.M) :
      dotProduct z (P.Sigma k *ᵥ z) = base k + t * grad k + t ^ 2 * quad k := by
    -- The quadratic expansion at `P.wStar` splits into the base value, linearized gradient, and
    -- second-order nonnegative remainder.
    dsimp [z, base, grad, quad]
    rw [quadratic_form_add _ (P.Sigma_symm k) P.wStar (t • d.1)]
    simp [pow_two, dotProduct_smul, smul_dotProduct, Matrix.mulVec_smul, mul_assoc, mul_left_comm]
  have hsup_bound :
      sSup (Set.range fun k : Fin P.M => dotProduct z (P.Sigma k *ᵥ z)) ≤
        baseSup + t * gradSup + t ^ 2 * quadSup := by
    -- Each expanded quadratic term is bounded by the corresponding supremum envelope.
    refine csSup_le (Set.range_nonempty _) ?_
    intro x hx
    rcases hx with ⟨k, rfl⟩
    have hbase_k : base k ≤ baseSup := by
      exact le_csSup (Set.finite_range base).bddAbove (Set.mem_range_self k)
    have hgrad_k : grad k ≤ gradSup := by
      exact le_csSup (Set.finite_range grad).bddAbove (Set.mem_range_self k)
    have hquad_k : quad k ≤ quadSup := by
      exact le_csSup (Set.finite_range quad).bddAbove (Set.mem_range_self k)
    have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
    have := hquad_expand k
    nlinarith
  have hz_optimal := hwStar_optimal.2 z hz_feasible
  dsimp [RobustMeanVariancePortfolioProblem.objective, z] at hz_optimal
  have hz_lower :
      (∑ i : Fin P.n, P.μ i * z i) - P.γ * (baseSup + t * gradSup + t ^ 2 * quadSup) ≤
        (∑ i : Fin P.n, P.μ i * z i) -
          P.γ * sSup (Set.range fun k : Fin P.M => dotProduct z (P.Sigma k *ᵥ z)) := by
    -- Replacing the supremum by a larger envelope only lowers the objective bound.
    have hmul := mul_le_mul_of_nonneg_left hsup_bound P.hγ.le
    linarith
  have hz_key :
      (∑ i : Fin P.n, P.μ i * z i) - P.γ * (baseSup + t * gradSup + t ^ 2 * quadSup) ≤
        (∑ i : Fin P.n, P.μ i * P.wStar i) -
          P.γ * sSup (Set.range fun k : Fin P.M => dotProduct P.wStar (P.Sigma k *ᵥ P.wStar)) := by
    exact le_trans hz_lower hz_optimal
  have hmain : 0 < t * returnForm P d - P.γ * (t * gradSup + t ^ 2 * quadSup) := by
    nlinarith [ht_gap, ht_pos]
  nlinarith [hz_key, hlinear, hmain]

/-- A linear functional on a finite-dimensional space evaluates on basis coordinates as the dot
product with its values on the basis. -/
lemma basis_coordinate_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis ι ℝ V) (f : Module.Dual ℝ V) (x : ι → ℝ) :
    dotProduct (fun i => f (b i)) x = f (b.equivFun.symm x) := by
  -- Expand the basis reconstruction of the coordinate vector and apply the functional termwise.
  rw [b.equivFun_symm_apply, map_sum, dotProduct]
  -- The resulting two scalar expressions differ only by commuting the real factors.
  simp_rw [map_smulₛₗ, smul_eq_mul, RingHom.id_apply]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simpa using (mul_comm (f (b i)) (x i))

/-- A continuous linear functional on `ι → ℝ` is the dot product with its standard-basis
coefficients. -/
lemma strongDual_pi_apply_eq_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    l x = dotProduct (fun i => l (Pi.basisFun ℝ ι i)) x := by
  -- The standard basis identifies a vector with its coordinate function, so the previous pairing
  -- lemma becomes the usual dot-product formula.
  simpa [Pi.basisFun_equivFun] using
    (basis_coordinate_pairing (b := Pi.basisFun ℝ ι) (f := (l : Module.Dual ℝ (ι → ℝ))) x).symm

/- [BLOCK Exercise 13.22-(a) | 17 | thm]
Let n,M ∈ ℕ with M ≥ 1, let μ ∈ ℝ^n, let γ > 0, and for each k=1,ldots,M, let σ^{(k)} ∈ S_{++}^n,
where S_{++}^n is the set of real symmetric positive definite n × n matrices. Let 1 ∈ ℝ^n be the
vector of all ones. Consider the robust mean-variance portfolio problem, and assume that w^{star} ∈
ℝ^n is a solution. Show that there exist scalars γ_1,ldots,γ_M ∈ ℝ such that γ_k ≥ 0 quad
(k=1,ldots,M), sum_{k=1}^M γ_k = γ, and w^{star} is also a solution of the weighted mean-variance
portfolio problem.
-/
theorem robust_optimal_implies_weighted_optimal
    (P : RobustMeanVariancePortfolioProblem)
    (hwStar_optimal : P.isOptimalSolution P.wStar) :
    ∃ γw : Fin P.M → ℝ,
      ∃ hγw : ∀ k : Fin P.M, 0 ≤ γw k,
        (∑ k : Fin P.M, γw k) = P.γ ∧
        ((∑ i : Fin P.n, P.wStar i) = 1 ∧
          ∀ z : Fin P.n → ℝ, (∑ i : Fin P.n, z i) = 1 →
            ((∑ i : Fin P.n, P.μ i * z i) -
                ∑ k : Fin P.M, γw k * dotProduct z (P.Sigma k *ᵥ z)) ≤
              ((∑ i : Fin P.n, P.μ i * P.wStar i) -
                ∑ k : Fin P.M, γw k * dotProduct P.wStar (P.Sigma k *ᵥ P.wStar))) := by
  -- Route correction: `robust_directional_upper_bound` now isolates the exact first-order
  -- information available from robust optimality on the zero-sum budget subspace.
  -- Route correction: instead of separating directly in the dual of `budgetDir`, transport the
  -- restricted forms to basis coordinates, separate there, and then pull the convex combination
  -- back to the original linear forms.
  classical
  letI : Nonempty (Fin P.M) := ⟨⟨0, P.hM⟩⟩
  let ι := Fin (Module.finrank ℝ (budgetDir P))
  let b : Module.Basis ι ℝ (budgetDir P) := Module.finBasis ℝ (budgetDir P)
  let returnCoord : ι → ℝ := fun i => returnForm P (b i)
  let gradientCoord : Fin P.M → ι → ℝ := fun k i => (P.γ • gradientForm P k) (b i)
  have hreturn_mem : returnCoord ∈ convexHull ℝ (Set.range gradientCoord) := by
    let S : Set (ι → ℝ) := convexHull ℝ (Set.range gradientCoord)
    have hS_convex : Convex ℝ S := by
      -- The coordinate image of the candidate subgradients is convex after taking convex hull.
      dsimp [S]
      exact convex_convexHull ℝ (Set.range gradientCoord)
    have hS_closed : IsClosed S := by
      -- Finite families have closed convex hull in the finite-dimensional coordinate space.
      dsimp [S]
      exact (Set.finite_range gradientCoord).isClosed_convexHull
    have hmem_half :
        returnCoord ∈ ⋂ l : StrongDual ℝ (ι → ℝ), { x | ∃ y ∈ S, l x ≤ l y } := by
      -- Each continuous linear functional is maximized on the finite gradient family by one index,
      -- and the directional upper bound forces `returnCoord` into the same half-space.
      refine Set.mem_iInter.mpr ?_
      intro l
      let c : ι → ℝ := fun i => l (Pi.basisFun ℝ ι i)
      let d : budgetDir P := b.equivFun.symm c
      have hreturn_pair :
          dotProduct returnCoord c = returnForm P d := by
        -- The budget-direction coordinates convert the restricted return form into a dot product.
        simpa [returnCoord, c, d] using
          (basis_coordinate_pairing (b := b) (f := returnForm P) c)
      have hgrad_pair (k : Fin P.M) :
          dotProduct (gradientCoord k) c = (P.γ • gradientForm P k) d := by
        -- The same coordinate pairing works for every weighted restricted gradient.
        simpa [gradientCoord, c, d] using
          (basis_coordinate_pairing (b := b) (f := (P.γ • gradientForm P k)) c)
      have hgrad_range :
          Set.range (fun k : Fin P.M => dotProduct (gradientCoord k) c) =
            Set.range (fun k : Fin P.M => (P.γ • gradientForm P k) d) := by
        -- Both ranges enumerate the same finite family after the coordinate rewrite.
        ext x
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨k, (hgrad_pair k).symm⟩
        · rintro ⟨k, rfl⟩
          exact ⟨k, hgrad_pair k⟩
      have hupper_coord :
          dotProduct returnCoord c ≤
            sSup (Set.range fun k : Fin P.M => dotProduct (gradientCoord k) c) := by
        -- This is exactly the previously proved robust first-order inequality in coordinates.
        have hupper := robust_directional_upper_bound P hwStar_optimal d
        rw [← hreturn_pair, ← hgrad_range] at hupper
        exact hupper
      have hl_return :
          l returnCoord = dotProduct returnCoord c := by
        -- Every separator on the coordinate space is represented by its standard-basis
        -- coefficients.
        calc
          l returnCoord = dotProduct c returnCoord := by
            simpa [c] using (strongDual_pi_apply_eq_dotProduct (l := l) returnCoord)
          _ = dotProduct returnCoord c := by rw [dotProduct_comm]
      have hl_grad (k : Fin P.M) :
          l (gradientCoord k) = dotProduct (gradientCoord k) c := by
        -- The same standard-basis representation applies to each gradient coordinate vector.
        calc
          l (gradientCoord k) = dotProduct c (gradientCoord k) := by
            simpa [c] using (strongDual_pi_apply_eq_dotProduct (l := l) (gradientCoord k))
          _ = dotProduct (gradientCoord k) c := by rw [dotProduct_comm]
      obtain ⟨kMax, -, hkMax⟩ :=
        Finset.exists_max_image (Finset.univ : Finset (Fin P.M))
          (fun k => l (gradientCoord k)) Finset.univ_nonempty
      have hl_grad_range :
          Set.range (fun k : Fin P.M => dotProduct (gradientCoord k) c) =
            Set.range (fun k : Fin P.M => l (gradientCoord k)) := by
        -- After rewriting with `hl_grad`, the support set is now the linear-functional image set.
        ext x
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨k, by simpa using hl_grad k⟩
        · rintro ⟨k, rfl⟩
          exact ⟨k, by simpa using (hl_grad k).symm⟩
      have hl_support :
          l returnCoord ≤ sSup (Set.range fun k : Fin P.M => l (gradientCoord k)) := by
        -- Replacing the dot-product presentation by the actual separator values preserves the
        -- support inequality.
        calc
          l returnCoord = dotProduct returnCoord c := hl_return
          _ ≤ sSup (Set.range fun k : Fin P.M => dotProduct (gradientCoord k) c) := hupper_coord
          _ = sSup (Set.range fun k : Fin P.M => l (gradientCoord k)) := by
            rw [hl_grad_range]
      have hsup_le :
          sSup (Set.range fun k : Fin P.M => l (gradientCoord k)) ≤ l (gradientCoord kMax) := by
        -- A finite family has a maximizing index, so its supremum is bounded by that maximum.
        refine csSup_le (Set.range_nonempty _) ?_
        intro x hx
        rcases hx with ⟨k, rfl⟩
        exact hkMax k (Finset.mem_univ k)
      refine ⟨gradientCoord kMax, ?_, le_trans hl_support hsup_le⟩
      -- The maximizing coordinate vector is itself one of the generators of the convex hull.
      exact subset_convexHull ℝ _ (Set.mem_range_self kMax)
    -- The coordinate return vector lies in every half-space containing the finite gradient hull.
    change returnCoord ∈ S
    rw [← iInter_halfSpaces_eq (s := S) hS_convex hS_closed]
    exact hmem_half
  rw [convexHull_range_eq_exists_affineCombination] at hreturn_mem
  rcases hreturn_mem with ⟨s, weights, hweights_nonneg, hweights_sum, hweights_affine⟩
  let weights0 : Fin P.M → ℝ := fun k => if k ∈ s then weights k else 0
  have hweights0_nonneg : ∀ k : Fin P.M, 0 ≤ weights0 k := by
    -- Zero-extending the finite support preserves nonnegativity on all indices.
    intro k
    by_cases hk : k ∈ s
    · simp [weights0, hk, hweights_nonneg k hk]
    · simp [weights0, hk]
  have hweights0_sum : ∑ k : Fin P.M, weights0 k = 1 := by
    -- The zero extension has the same total mass as the original affine-combination weights.
    simpa [weights0] using hweights_sum
  have hcoord_sum : returnCoord = ∑ k : Fin P.M, weights0 k • gradientCoord k := by
    -- The coordinate convex-hull identity becomes an honest linear combination over all indices.
    have hcoord_sum' : ∑ k : Fin P.M, weights0 k • gradientCoord k = returnCoord := by
      have hcoord_sum_s : Finset.sum s (fun k => weights k • gradientCoord k) = returnCoord := by
        simpa [hweights_sum] using hweights_affine
      calc
        (∑ k : Fin P.M, weights0 k • gradientCoord k) =
            Finset.sum s (fun k => weights k • gradientCoord k) := by
          simp [weights0]
        _ = returnCoord := hcoord_sum_s
    simpa using hcoord_sum'.symm
  let γw : Fin P.M → ℝ := fun k => P.γ * weights0 k
  refine ⟨γw, ?_⟩
  refine ⟨fun k => mul_nonneg P.hγ.le (hweights0_nonneg k), ?_⟩
  constructor
  · -- Scaling the simplex weights by `P.γ` gives the required total penalty budget.
    calc
      ∑ k : Fin P.M, γw k = ∑ k : Fin P.M, P.γ * weights0 k := by
        rfl
      _ = P.γ * ∑ k : Fin P.M, weights0 k := by
        rw [← Finset.mul_sum]
      _ = P.γ := by rw [hweights0_sum, mul_one]
  constructor
  · -- Feasibility of `wStar` is already part of the robust optimality hypothesis.
    exact hwStar_optimal.1
  · intro z hz
    let d : budgetDir P := ⟨z - P.wStar,
      (mem_budgetDir_iff P (z - P.wStar)).2 (feasible_sub_sum_eq_zero hwStar_optimal.1 hz)⟩
    have hz_eq : P.wStar + d.1 = z := by
      -- The budget direction `d` was defined as the feasible perturbation from `wStar` to `z`.
      funext i
      simp [d]
    have hz_eq_apply (i : Fin P.n) : P.wStar i + d.1 i = z i := by
      exact congrFun hz_eq i
    have hreturn_combo :
        returnForm P d = ∑ k : Fin P.M, γw k * gradientForm P k d := by
      -- Evaluating the coordinate convex combination on the coordinates of `d` pulls the affine
      -- identity back to an identity of restricted linear forms.
      let x : ι → ℝ := b.equivFun d
      have hdot :
          dotProduct returnCoord x =
            ∑ k : Fin P.M, weights0 k * dotProduct (gradientCoord k) x := by
        have := congrArg (fun v : ι → ℝ => dotProduct v x) hcoord_sum
        simpa [sum_dotProduct, smul_dotProduct] using this
      have hreturn_pair :
          dotProduct returnCoord x = returnForm P d := by
        simpa [returnCoord, x] using
          (basis_coordinate_pairing (b := b) (f := returnForm P) x)
      have hgrad_pair (k : Fin P.M) :
          dotProduct (gradientCoord k) x = (P.γ • gradientForm P k) d := by
        simpa [gradientCoord, x] using
          (basis_coordinate_pairing (b := b) (f := (P.γ • gradientForm P k)) x)
      calc
        returnForm P d = dotProduct returnCoord x := by
          exact hreturn_pair.symm
        _ = ∑ k : Fin P.M, weights0 k * dotProduct (gradientCoord k) x := hdot
        _ = ∑ k : Fin P.M, γw k * gradientForm P k d := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hgrad_pair k]
          simp [γw]
          ring
    have hlinear_d : ∑ i : Fin P.n, P.μ i * d.1 i = returnForm P d := by
      -- The restricted return form is exactly the linear return increment on the perturbation.
      simpa [returnForm_apply]
    have hgrad_sum :
        ∑ k : Fin P.M, γw k * gradientForm P k d =
          ∑ k : Fin P.M, 2 * γw k * dotProduct d.1 (P.Sigma k *ᵥ P.wStar) := by
      -- Rewriting the restricted gradients exposes the first-order quadratic terms.
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [gradientForm_apply]
      ring
    have hdiff :
        (((∑ i : Fin P.n, P.μ i * z i) -
              ∑ k : Fin P.M, γw k * dotProduct z (P.Sigma k *ᵥ z)) -
            ((∑ i : Fin P.n, P.μ i * P.wStar i) -
              ∑ k : Fin P.M, γw k * dotProduct P.wStar (P.Sigma k *ᵥ P.wStar))) =
          - ∑ k : Fin P.M, γw k * dotProduct d.1 (P.Sigma k *ᵥ d.1) := by
      -- The weighted objective expansion cancels its first-order term because `returnForm` is the
      -- convex combination of the restricted gradients.
      have hbase :=
        weighted_objective_difference_add P.μ γw P.Sigma P.wStar d.1 P.Sigma_symm
      have hbase_z :
          (((∑ i : Fin P.n, P.μ i * z i) -
                ∑ k : Fin P.M, γw k * dotProduct z (P.Sigma k *ᵥ z)) -
              ((∑ i : Fin P.n, P.μ i * P.wStar i) -
                ∑ k : Fin P.M, γw k * dotProduct P.wStar (P.Sigma k *ᵥ P.wStar))) =
            (∑ i : Fin P.n, P.μ i * d.1 i) -
              ∑ k : Fin P.M,
                (2 * γw k * dotProduct d.1 (P.Sigma k *ᵥ P.wStar) +
                  γw k * dotProduct d.1 (P.Sigma k *ᵥ d.1)) := by
        simpa [hz_eq, hz_eq_apply] using hbase
      have hcancel :
          (∑ i : Fin P.n, P.μ i * d.1 i) -
              ∑ k : Fin P.M,
                (2 * γw k * dotProduct d.1 (P.Sigma k *ᵥ P.wStar) +
                  γw k * dotProduct d.1 (P.Sigma k *ᵥ d.1)) =
            - ∑ k : Fin P.M, γw k * dotProduct d.1 (P.Sigma k *ᵥ d.1) := by
        rw [hlinear_d, hreturn_combo, hgrad_sum, Finset.sum_add_distrib]
        ring
      exact hbase_z.trans hcancel
    have hquad_nonneg :
        0 ≤ ∑ k : Fin P.M, γw k * dotProduct d.1 (P.Sigma k *ᵥ d.1) := by
      -- Every covariance quadratic form is nonnegative, and the extracted weights are nonnegative.
      refine Finset.sum_nonneg ?_
      intro k hk
      exact mul_nonneg (mul_nonneg P.hγ.le (hweights0_nonneg k))
        ((P.Sigma_pos k).posSemidef.dotProduct_mulVec_nonneg d.1)
    -- Therefore the weighted objective at `z` is bounded above by the weighted objective at
    -- `wStar`.
    linarith [hdiff, hquad_nonneg]

end «problem-82»
