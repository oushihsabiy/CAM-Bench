import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-63»
/-
A collection of equations and inequalities is called the optimality conditions for an optimization
problem if every optimal point satisfies them. In smooth constrained optimization, this usually
refers to first - order necessary conditions such as the KKT conditions.
-/
def OptimalityConditions {α : Type _} (isOptimal : α → Prop) (conds : α → Prop) : Prop :=
  ∀ ⦃x : α⦄, isOptimal x → conds x

/-
Consider the optimization problem max_{x ∈ ℝ^n} \sum_{j = 1}^m π_j log(p_jᵀ x) subject to 1ᵀ x = 1,
x
succeq 0, where 1 ∈ ℝ^n is the all - ones vector, x succeq 0 means xᵢ ≥ 0 for i = 1, ..., n, and pⱼ
∈
ℝ^n are given vectors for j = 1, ..., m. The probabilities satisfy π_j > 0 for j = 1, ..., m,
\sum_{j =
1}^m π_j = 1. Assume that p_jᵀ x > 0 for every feasible x at which the objective is evaluated.
-/
structure LogUtilitySimplexMaximization where
  n : ℕ
  m : ℕ
  p : Fin m → Fin n → ℝ
  π : Fin m → ℝ
  pi_pos : ∀ j : Fin m, 0 < π j
  pi_sum_one : (∑ j : Fin m, π j) = 1
  payoff_pos_on_simplex :
    ∀ x : Fin n → ℝ,
      ((∑ i : Fin n, x i) = 1 ∧ ∀ i : Fin n, 0 ≤ x i) →
      ∀ j : Fin m, 0 < ∑ i : Fin n, p j i * x i

def LogUtilitySimplexMaximization.Feasible (P : LogUtilitySimplexMaximization) (x : Fin P.n → ℝ) : Prop :=
  (∑ i : Fin P.n, x i) = 1 ∧ ∀ i : Fin P.n, 0 ≤ x i

def LogUtilitySimplexMaximization.payoff (P : LogUtilitySimplexMaximization) (j : Fin P.m)
    (x : Fin P.n → ℝ) : ℝ :=
  ∑ i : Fin P.n, P.p j i * x i

def LogUtilitySimplexMaximization.objective (P : LogUtilitySimplexMaximization)
    (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.m, P.π j * Real.log (P.payoff j x)

def LogUtilitySimplexMaximization.objectiveDefined (P : LogUtilitySimplexMaximization)
    (x : Fin P.n → ℝ) : Prop :=
  ∀ j : Fin P.m, 0 < P.payoff j x

def LogUtilitySimplexMaximization.isOptimal (P : LogUtilitySimplexMaximization)
    (x : Fin P.n → ℝ) : Prop :=
  P.Feasible x ∧ P.objectiveDefined x ∧
    ∀ y : Fin P.n → ℝ, P.Feasible y → P.objectiveDefined y → P.objective y ≤ P.objective x

/-- On the simplex, the standing positivity assumption makes every logarithmic term well-defined. -/
lemma LogUtilitySimplexMaximization.feasible_objectiveDefined
    (P : LogUtilitySimplexMaximization) {x : Fin P.n → ℝ} (hx : P.Feasible x) :
    P.objectiveDefined x := by
  -- The feasibility hypotheses are exactly the hypotheses required by `payoff_pos_on_simplex`.
  intro j
  simpa [LogUtilitySimplexMaximization.objectiveDefined, LogUtilitySimplexMaximization.payoff] using
    P.payoff_pos_on_simplex x hx j

/-- The simplex vertex `e_i` is feasible. -/
lemma LogUtilitySimplexMaximization.vertex_feasible
    (P : LogUtilitySimplexMaximization) (i : Fin P.n) :
    P.Feasible (Pi.single i (1 : ℝ)) := by
  -- Only the `i`-th coordinate is nonzero, so the simplex constraints are immediate.
  constructor
  · simp
  · intro k
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]

/-- The payoff at the simplex vertex `e_i` is the `i`-th payoff coefficient. -/
lemma LogUtilitySimplexMaximization.payoff_vertex
    (P : LogUtilitySimplexMaximization) (i : Fin P.n) (j : Fin P.m) :
    P.payoff j (Pi.single i (1 : ℝ)) = P.p j i := by
  -- Evaluating the linear payoff on a basis vector isolates the matching coefficient.
  simp [LogUtilitySimplexMaximization.payoff, Pi.single_apply]

/-- The segment from a feasible point to a simplex vertex stays feasible. -/
lemma LogUtilitySimplexMaximization.segment_to_vertex_feasible
    (P : LogUtilitySimplexMaximization) {x : Fin P.n → ℝ} (hx : P.Feasible x)
    (i : Fin P.n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    P.Feasible (fun k => (1 - t) * x k + t * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k)) := by
  -- The simplex is convex, and this point is an explicit convex combination of `x` and `e_i`.
  rcases hx with ⟨hxsum, hxnonneg⟩
  rcases ht with ⟨ht0, ht1⟩
  have h_one_sub : 0 ≤ 1 - t := by
    linarith
  constructor
  · calc
      ∑ k : Fin P.n, ((1 - t) * x k + t * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k))
          = (∑ k : Fin P.n, (1 - t) * x k) +
              ∑ k : Fin P.n, t * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k) := by
              rw [Finset.sum_add_distrib]
      _ = (1 - t) * (∑ k : Fin P.n, x k) +
            t * ∑ k : Fin P.n, ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = (1 - t) * 1 + t * 1 := by simp [hxsum]
      _ = 1 := by ring
  · intro k
    have hxk : 0 ≤ x k := hxnonneg k
    have hvertexk : 0 ≤ ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k) := by
      by_cases hk : k = i
      · subst k
        simp
      · simp [hk]
    nlinarith

/-- Along the segment from `x` to the vertex `e_i`, each payoff varies affinely in the parameter. -/
lemma LogUtilitySimplexMaximization.payoff_along_vertex_segment
    (P : LogUtilitySimplexMaximization) (x : Fin P.n → ℝ) (i : Fin P.n) (j : Fin P.m) (t : ℝ) :
    P.payoff j (fun k => (1 - t) * x k + t * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k)) =
      (1 - t) * P.payoff j x + t * P.p j i := by
  -- Expanding the finite sum shows that each payoff is affine along the segment.
  calc
    P.payoff j (fun k => (1 - t) * x k + t * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k))
        = ∑ k : Fin P.n, P.p j k *
            ((1 - t) * x k + t * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k)) := by
            rfl
    _ = ∑ k : Fin P.n,
          ((1 - t) * (P.p j k * x k) +
            t * (P.p j k * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k))) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (∑ k : Fin P.n, (1 - t) * (P.p j k * x k)) +
          ∑ k : Fin P.n, t * (P.p j k * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k)) := by
            rw [Finset.sum_add_distrib]
    _ = (1 - t) * (∑ k : Fin P.n, P.p j k * x k) +
          t * ∑ k : Fin P.n, P.p j k * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = (1 - t) * P.payoff j x + t * P.payoff j (Pi.single i (1 : ℝ)) := by
          rfl
    _ = (1 - t) * P.payoff j x + t * P.p j i := by
          rw [P.payoff_vertex]

/-- The derivative of the objective along the segment from `x` to `e_i` is the `i`-th stationarity
coefficient minus `1`. -/
lemma LogUtilitySimplexMaximization.objectiveAlongVertex_hasDerivWithinAt
    (P : LogUtilitySimplexMaximization) {x : Fin P.n → ℝ} (hx : P.Feasible x) (i : Fin P.n) :
    HasDerivWithinAt
      (fun t : ℝ =>
        P.objective (fun k => (1 - t) * x k + t * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k)))
      ((∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) - 1)
      (Set.Icc (0 : ℝ) 1) 0 := by
  let q : Fin P.m → ℝ := fun j => P.payoff j x
  have hxDef : P.objectiveDefined x := P.feasible_objectiveDefined hx
  let A : Fin P.m → ℝ → ℝ :=
    fun j t => P.π j * Real.log ((1 - t) * q j + t * P.p j i)
  let A' : Fin P.m → ℝ :=
    fun j => P.π j * (((q j)⁻¹) * (P.p j i - q j))
  have hsumAt :
      HasDerivAt
        (fun t : ℝ => ∑ j : Fin P.m, P.π j * Real.log ((1 - t) * q j + t * P.p j i))
        (∑ j : Fin P.m, P.π j * (((q j)⁻¹) * (P.p j i - q j)))
        0 := by
    -- Differentiate each logarithmic term after rewriting its affine scalar argument.
    have hA : ∀ j : Fin P.m, HasDerivAt (A j) (A' j) 0 := by
      intro j
      have hAffine :
          HasDerivAt (fun t : ℝ => (1 - t) * q j + t * P.p j i) (P.p j i - q j) 0 := by
        -- The path derivative is the difference between the endpoint payoffs.
        simpa [q, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (((hasDerivAt_id' (0 : ℝ)).const_sub (1 : ℝ)).mul_const (q j)).add
            ((hasDerivAt_id' (0 : ℝ)).mul_const (P.p j i))
      have hLog :
          HasDerivAt
            (fun t : ℝ => Real.log ((1 - t) * q j + t * P.p j i))
            ((q j)⁻¹ * (P.p j i - q j))
            0 := by
        -- Route correction: we only need the one-variable logarithmic derivative at `t = 0`,
        -- not a full multivariate derivative of the objective on the simplex.
        have hqne : q j ≠ 0 := by
          simpa [q] using (ne_of_gt (hxDef j) : P.payoff j x ≠ 0)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          hAffine.log (by simpa using hqne)
      simpa [A, A'] using hLog.const_mul (P.π j)
    simpa [A, A'] using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin P.m))) (A := A) (A' := A') (x := 0)
        fun j _ => hA j)
  have hsum : HasDerivWithinAt
      (fun t : ℝ => ∑ j : Fin P.m, P.π j * Real.log ((1 - t) * q j + t * P.p j i))
      (∑ j : Fin P.m, P.π j * (((q j)⁻¹) * (P.p j i - q j)))
      (Set.Icc (0 : ℝ) 1) 0 :=
    hsumAt.hasDerivWithinAt
  have hconst :
      (∑ j : Fin P.m, P.π j * (((q j)⁻¹) * (P.p j i - q j))) =
        (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) - 1 := by
    -- Termwise algebra rewrites the derivative into the stationarity coefficient minus `1`.
    calc
      ∑ j : Fin P.m, P.π j * (((q j)⁻¹) * (P.p j i - q j))
          = ∑ j : Fin P.m, (P.π j * (P.p j i / P.payoff j x) - P.π j) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hqne : q j ≠ 0 := ne_of_gt (hxDef j)
              field_simp [q, hqne]
              ring
      _ = (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) - ∑ j : Fin P.m, P.π j := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) - 1 := by
            rw [P.pi_sum_one]
  -- Substitute the affine payoff identity and the simplified derivative.
  convert hsum using 1
  · ext t
    simp [LogUtilitySimplexMaximization.objective, q, P.payoff_along_vertex_segment]
  · exact hconst.symm

/-- The weighted average of the stationarity coefficients equals `1` at every feasible point. -/
lemma LogUtilitySimplexMaximization.weighted_gradient_sum_eq_one
    (P : LogUtilitySimplexMaximization) {x : Fin P.n → ℝ} (hx : P.Feasible x) :
    (∑ i : Fin P.n, x i * (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x))) = 1 := by
  have hxDef : P.objectiveDefined x := P.feasible_objectiveDefined hx
  -- Swapping the finite sums reduces the weighted average to `∑ j π_j`.
  calc
    ∑ i : Fin P.n, x i * (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x))
        = ∑ i : Fin P.n, ∑ j : Fin P.m, x i * (P.π j * (P.p j i / P.payoff j x)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
    _ = ∑ j : Fin P.m, ∑ i : Fin P.n, x i * (P.π j * (P.p j i / P.payoff j x)) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin P.m, (P.π j * ∑ i : Fin P.n, P.p j i * x i) / P.payoff j x := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hqne : P.payoff j x ≠ 0 := ne_of_gt (hxDef j)
          calc
            ∑ i : Fin P.n, x i * (P.π j * (P.p j i / P.payoff j x))
                = ∑ i : Fin P.n, (P.π j * (P.p j i * x i)) / P.payoff j x := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    field_simp [hqne]
            _ = (∑ i : Fin P.n, P.π j * (P.p j i * x i)) / P.payoff j x := by
                  rw [← Finset.sum_div]
            _ = (P.π j * ∑ i : Fin P.n, P.p j i * x i) / P.payoff j x := by
                  rw [Finset.mul_sum]
    _ = ∑ j : Fin P.m, (P.π j * P.payoff j x) / P.payoff j x := by
          simp [LogUtilitySimplexMaximization.payoff]
    _ = ∑ j : Fin P.m, P.π j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hqne : P.payoff j x ≠ 0 := ne_of_gt (hxDef j)
          rw [mul_div_assoc, div_self hqne, mul_one]
    _ = 1 := P.pi_sum_one

/-
Consider the optimization problem log - utility simplex maximization. Show that the optimality
conditions for this problem can be written as 1ᵀ x = 1, x succeq 0, and, for each i = 1, ..., n, xᵢ
>
0 implies \sum_{j = 1}^m π_j \frac{p_{ij}}{p_jᵀ x} = 1, xᵢ = 0 implies \sum_{j = 1}^m π_j
\frac{p_{ij}}{p_jᵀ x} ≤ 1.
-/
theorem logUtilitySimplexMaximization_optimality_conditions
    (P : LogUtilitySimplexMaximization)
    (_conds : Fin P.n → (Fin P.n → ℝ) → Prop := fun i x =>
      if 0 < x i then
        (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) = 1
      else
        (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) ≤ 1) :
    OptimalityConditions P.isOptimal
      (fun x =>
        P.Feasible x ∧
        P.objectiveDefined x ∧
        ∀ i : Fin P.n,
          (0 < x i →
            (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) = 1) ∧
          (x i = 0 →
            (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) ≤ 1)) := by
  intro x hxopt
  rcases hxopt with ⟨hxFeas, hxDef, hxOpt⟩
  let g : Fin P.n → ℝ := fun i => ∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)
  have hbound : ∀ i : Fin P.n, g i ≤ 1 := by
    intro i
    let φ : ℝ → ℝ := fun t =>
      P.objective (fun k => (1 - t) * x k + t * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k))
    have hmax : IsMaxOn φ (Set.Icc (0 : ℝ) 1) 0 := by
      -- Every point on the segment to the vertex is feasible, so optimality makes `t = 0` maximal.
      rw [isMaxOn_iff]
      intro t ht
      have hsegFeas :
          P.Feasible (fun k => (1 - t) * x k + t * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k)) :=
        P.segment_to_vertex_feasible hxFeas i ht
      have hsegDef :
          P.objectiveDefined
            (fun k => (1 - t) * x k + t * ((Pi.single i (1 : ℝ) : Fin P.n → ℝ) k)) :=
        P.feasible_objectiveDefined hsegFeas
      have hopt := hxOpt _ hsegFeas hsegDef
      simpa [φ] using hopt
    have hlocal : IsLocalMaxOn φ (Set.Icc (0 : ℝ) 1) 0 := hmax.localize
    have htan : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) (0 : ℝ) := by
      -- The interval direction `1 - 0` is tangent because the whole segment `[0, 1]` stays inside.
      simpa using
        sub_mem_posTangentConeAt_of_segment_subset
          (s := Set.Icc (0 : ℝ) 1) (x := (0 : ℝ)) (y := (1 : ℝ))
          (by
            simp :
              segment ℝ (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1)
    have hderiv :
        HasDerivWithinAt φ (g i - 1) (Set.Icc (0 : ℝ) 1) 0 := by
      -- This is the previously isolated one-variable derivative computation.
      simpa [g, φ] using P.objectiveAlongVertex_hasDerivWithinAt hxFeas i
    have hnonpos := hlocal.hasFDerivWithinAt_nonpos hderiv.hasFDerivWithinAt htan
    have hnonpos' : g i - 1 ≤ 0 := by
      simpa using hnonpos
    linarith
  have hweighted : ∑ i : Fin P.n, x i * g i = 1 := by
    -- The weighted average identity is the algebraic complement to the vertex-direction bounds.
    simpa [g] using P.weighted_gradient_sum_eq_one hxFeas
  refine ⟨hxFeas, hxDef, ?_⟩
  intro i
  constructor
  · intro hxi
    have hone_sub_nonneg : 0 ≤ 1 - g i := by
      linarith [hbound i]
    have hsum_zero : ∑ k : Fin P.n, x k * (1 - g k) = 0 := by
      -- Rewrite the weighted identity as a sum of nonnegative slack terms.
      calc
        ∑ k : Fin P.n, x k * (1 - g k)
            = ∑ k : Fin P.n, (x k - x k * g k) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
        _ = (∑ k : Fin P.n, x k) - ∑ k : Fin P.n, x k * g k := by
              rw [Finset.sum_sub_distrib]
        _ = 1 - 1 := by rw [hxFeas.1, hweighted]
        _ = 0 := by ring
    have hterm_nonneg : ∀ k : Fin P.n, 0 ≤ x k * (1 - g k) := by
      intro k
      have hxk : 0 ≤ x k := hxFeas.2 k
      have hgk : 0 ≤ 1 - g k := by
        linarith [hbound k]
      nlinarith
    have hterm_zero :
        x i * (1 - g i) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hterm_nonneg k).mp hsum_zero i (by simp)
    have hone_sub_eq_zero : 1 - g i = 0 := by
      nlinarith
    linarith
  · intro hxi0
    exact hbound i

end «problem-63»
