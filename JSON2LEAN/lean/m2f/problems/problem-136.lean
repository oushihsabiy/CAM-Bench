import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-136»
/-
Exercise 6.1 | 15 | defn

Random variables v₁, …, vₘ are independent and identically distributed if they are mutually
independent and there exists a probability distribution P such that vᵢ ∼ P for every i = 1, …, m.
-/
def IsProbabilityDensityFunction (p : ℝ → ℝ) : Prop :=
  Measurable p ∧ (∀ z : ℝ, 0 ≤ p z) ∧ ∫ z : ℝ, p z = 1

/-
A function f: ℝ^n → ℝ_ + is log - concave if its support is convex and, for all x, y in its support
and
all θ ∈ [0, 1], f(θ x + (1 - θ)y) ≥ f(x)^θ f(y)^1 - θ.
-/
def IsLogConcave {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
    Convex ℝ {x : Fin n → ℝ | 0 < f x} ∧
    ∀ ⦃x y : Fin n → ℝ⦄,
      x ∈ {x : Fin n → ℝ | 0 < f x} →
      y ∈ {x : Fin n → ℝ | 0 < f x} →
      ∀ ⦃θ : ℝ⦄, θ ∈ Set.Icc (0 : ℝ) 1 →
        f (θ • x + (1 - θ) • y) ≥
          Real.rpow (f x) θ * Real.rpow (f y) (1 - θ)

/-
The effective domain of an extended - real - valued function g: ℝ^n → ℝ cup {+ ∞} is dom g = {x ∈
ℝ^n | g
x < + ∞}.
-/
def LogLikelihood (L : α → ℝ) : α → EReal :=
  fun θ => if 0 < L θ then (Real.log (L θ) : EReal) else ⊤

/-
The convex optimization problem min_{x∈ℝ^n, μ∈ℝ, σ > 0} (mlog σ + \sum_{i = 1}^m g((yᵢ - a_iᵀ x -
μ)/(σ))).
-/
structure LogConcaveLocationScaleMLE where
  n : ℕ
  m : ℕ
  y : Fin m → ℝ
  a : Fin m → Fin n → ℝ
  g : ℝ → EReal

def LogConcaveLocationScaleMLE.objective
    (p : LogConcaveLocationScaleMLE) :
    (Fin p.n → ℝ) → ℝ → ℝ → EReal :=
  fun x μ σ =>
    (p.m : EReal) * Real.log σ +
      ∑ i : Fin p.m, p.g (((p.y i) - (∑ j : Fin p.n, p.a i j * x j) - μ) / σ)

def LogConcaveLocationScaleMLE.isFeasible
    (p : LogConcaveLocationScaleMLE) :
    (Fin p.n → ℝ) → ℝ → ℝ → Prop :=
  fun _ _ σ => 0 < σ

def LogConcaveLocationScaleMLE.precisionObjective
    (p : LogConcaveLocationScaleMLE) :
    (Fin p.n → ℝ) → ℝ → ℝ → EReal :=
  fun z ν τ =>
    -((p.m : EReal) * Real.log τ) +
      ∑ i : Fin p.m, p.g (τ * p.y i - (∑ j : Fin p.n, p.a i j * z j) - ν)

def LogConcaveLocationScaleMLE.precisionFeasible
    (p : LogConcaveLocationScaleMLE) :
    (Fin p.n → ℝ) → ℝ → ℝ → Prop :=
  fun _ _ τ => 0 < τ

/-- Specialize the `Fin 1` log-concavity hypothesis to scalar arguments. -/
lemma scalar_logconcave_eval
    (f : ℝ → ℝ)
    (hf_logconcave : IsLogConcave (n := 1) (fun x : Fin 1 → ℝ => f (x 0)))
    {r s θ : ℝ} (hr : 0 < f r) (hs : 0 < f s) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.rpow (f r) θ * Real.rpow (f s) (1 - θ) ≤ f (θ * r + (1 - θ) * s) := by
  -- Move from vectors in `Fin 1 → ℝ` back to the scalar statement we need.
  have hmemr : (fun _ : Fin 1 => r) ∈ {x : Fin 1 → ℝ | 0 < f (x 0)} := by
    simpa
  have hmems : (fun _ : Fin 1 => s) ∈ {x : Fin 1 → ℝ | 0 < f (x 0)} := by
    simpa
  have hIcc : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨hθ0, hθ1⟩
  have hmain := hf_logconcave.2.2 hmemr hmems hIcc
  simpa [Pi.add_apply, Pi.smul_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using hmain

/-- The extended-real negative log induced by a log-concave scalar density is convex. -/
lemma ereal_neglog_of_logConcave_le
    (p : LogConcaveLocationScaleMLE)
    (f : ℝ → ℝ)
    (hf_logconcave : IsLogConcave (n := 1) (fun x : Fin 1 → ℝ => f (x 0)))
    (hg : p.g = fun t => if 0 < f t then (-Real.log (f t) : EReal) else ⊤) :
    ∀ r s θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      p.g (θ * r + (1 - θ) * s) ≤
        (θ : EReal) * p.g r + ((1 - θ : ℝ) : EReal) * p.g s := by
  intro r s θ hθ0 hθ1
  -- Boundary weights collapse directly to one endpoint.
  by_cases hθz : θ = 0
  · subst hθz
    simp [hg]
  by_cases hθo : θ = 1
  · subst hθo
    simp [hg]
  have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (by simpa [eq_comm] using hθz)
  have h1θpos : 0 < 1 - θ := sub_pos.mpr (lt_of_le_of_ne hθ1 (by simpa using hθo))
  by_cases hr : 0 < f r
  · by_cases hs : 0 < f s
    · -- On the positive support, convert log-concavity into convexity of `-log`.
      have hprod_le := scalar_logconcave_eval f hf_logconcave hr hs hθ0 hθ1
      have hprod_pos : 0 < Real.rpow (f r) θ * Real.rpow (f s) (1 - θ) := by
        exact mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hs _)
      have hmid : 0 < f (θ * r + (1 - θ) * s) := lt_of_lt_of_le hprod_pos hprod_le
      have hlog :
          θ * Real.log (f r) + (1 - θ) * Real.log (f s) ≤
            Real.log (f (θ * r + (1 - θ) * s)) := by
        calc
          θ * Real.log (f r) + (1 - θ) * Real.log (f s)
              = Real.log ((f r) ^ θ) + Real.log ((f s) ^ (1 - θ)) := by
                  rw [Real.log_rpow hr, Real.log_rpow hs]
          _ = Real.log ((f r) ^ θ * (f s) ^ (1 - θ)) := by
                rw [← Real.log_mul (by positivity) (by positivity)]
          _ ≤ Real.log (f (θ * r + (1 - θ) * s)) := Real.log_le_log hprod_pos hprod_le
      have hreal :
          -Real.log (f (θ * r + (1 - θ) * s)) ≤
            -(θ * Real.log (f r)) + -((1 - θ) * Real.log (f s)) := by
        linarith
      simp [hg, hr, hs, hmid]
      exact_mod_cast hreal
    · -- If one endpoint leaves the positive support in the interior case, the right-hand side is `⊤`.
      have hrhs :
          (θ : EReal) * p.g r + ((1 - θ : ℝ) : EReal) * p.g s = ⊤ := by
        calc
          (θ : EReal) * p.g r + ((1 - θ : ℝ) : EReal) * p.g s
              = ((θ * (-Real.log (f r)) : ℝ) : EReal) +
                  ((1 - θ : ℝ) : EReal) * (⊤ : EReal) := by
                    simp [hg, hr, hs, EReal.coe_mul]
          _ = ((θ * (-Real.log (f r)) : ℝ) : EReal) + ⊤ := by
                rw [EReal.coe_mul_top_of_pos h1θpos]
          _ = ⊤ := by
                rw [EReal.coe_add_top]
      rw [hrhs]
      exact le_top
  · -- The same `⊤` argument works if the first endpoint leaves the support.
    have hrhs :
        (θ : EReal) * p.g r + ((1 - θ : ℝ) : EReal) * p.g s = ⊤ := by
      calc
        (θ : EReal) * p.g r + ((1 - θ : ℝ) : EReal) * p.g s
            = (⊤ : EReal) + ((1 - θ : ℝ) : EReal) * p.g s := by
                rw [show (θ : EReal) * p.g r = (⊤ : EReal) by
                  calc
                    (θ : EReal) * p.g r = (θ : EReal) * (⊤ : EReal) := by
                      simp [hg, hr]
                    _ = ⊤ := EReal.coe_mul_top_of_pos hθpos]
        _ = ⊤ := by
              by_cases hs : 0 < f s
              · calc
                  (⊤ : EReal) + ((1 - θ : ℝ) : EReal) * p.g s
                      = (⊤ : EReal) + (((1 - θ) * (-Real.log (f s)) : ℝ) : EReal) := by
                          simp [hg, hs, EReal.coe_mul]
                  _ = ⊤ := by
                        rw [EReal.top_add_coe]
              · calc
                  (⊤ : EReal) + ((1 - θ : ℝ) : EReal) * p.g s
                      = (⊤ : EReal) + (((1 - θ : ℝ) : EReal) * (⊤ : EReal)) := by
                          simp [hg, hs]
                  _ = (⊤ : EReal) + ⊤ := by
                        rw [EReal.coe_mul_top_of_pos h1θpos]
                  _ = ⊤ := by
                        rw [EReal.top_add_top]
    rw [hrhs]
    exact le_top

/-- The precision residual at a convex combination is the convex combination of the residuals. -/
lemma precisionResidual_affine_combo
    (p : LogConcaveLocationScaleMLE)
    (u u' : (Fin p.n → ℝ) × ℝ × ℝ) (θ : ℝ) (i : Fin p.m) :
    ((θ * u.2.2 + (1 - θ) * u'.2.2) * p.y i
      - (∑ j : Fin p.n, p.a i j * (θ * u.1 j + (1 - θ) * u'.1 j))
      - (θ * u.2.1 + (1 - θ) * u'.2.1)) =
      θ * (u.2.2 * p.y i - (∑ j : Fin p.n, p.a i j * u.1 j) - u.2.1) +
        (1 - θ) * (u'.2.2 * p.y i - (∑ j : Fin p.n, p.a i j * u'.1 j) - u'.2.1) := by
  -- Expand the finite sum first, then normalize the scalar algebra.
  have hsum :
      (∑ j : Fin p.n, p.a i j * (θ * u.1 j + (1 - θ) * u'.1 j)) =
        θ * (∑ j : Fin p.n, p.a i j * u.1 j) +
          (1 - θ) * (∑ j : Fin p.n, p.a i j * u'.1 j) := by
    calc
      (∑ j : Fin p.n, p.a i j * (θ * u.1 j + (1 - θ) * u'.1 j))
          = ∑ j : Fin p.n, (θ * (p.a i j * u.1 j) + (1 - θ) * (p.a i j * u'.1 j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = (∑ j : Fin p.n, θ * (p.a i j * u.1 j)) +
            ∑ j : Fin p.n, (1 - θ) * (p.a i j * u'.1 j) := by
            rw [Finset.sum_add_distrib]
      _ = θ * (∑ j : Fin p.n, p.a i j * u.1 j) +
            (1 - θ) * (∑ j : Fin p.n, p.a i j * u'.1 j) := by
            rw [Finset.mul_sum, Finset.mul_sum]
  rw [hsum]
  ring

/-- The positive-precision feasible region is convex. -/
lemma precisionFeasible_convex
    (p : LogConcaveLocationScaleMLE) :
    Convex ℝ {u : (Fin p.n → ℝ) × ℝ × ℝ | p.precisionFeasible u.1 u.2.1 u.2.2} := by
  intro u hu u' hu' a b ha hb hab
  -- Only the third coordinate matters for feasibility.
  dsimp [LogConcaveLocationScaleMLE.precisionFeasible] at hu hu' ⊢
  change 0 < a * u.2.2 + b * u'.2.2
  have hconv : Convex ℝ (Set.Ioi (0 : ℝ)) := convex_Ioi 0
  have hu_mem : u.2.2 ∈ Set.Ioi (0 : ℝ) := by
    simpa [Set.mem_Ioi] using hu
  have hu'_mem : u'.2.2 ∈ Set.Ioi (0 : ℝ) := by
    simpa [Set.mem_Ioi] using hu'
  have hmem := hconv hu_mem hu'_mem ha hb hab
  simpa [Set.mem_Ioi] using hmem

/-- A finite nonnegative real scalar distributes over an `EReal` finite sum. -/
lemma ereal_mul_finset_sum_of_nonneg
    {α : Type*} [DecidableEq α] (s : Finset α) (w : ℝ) (hw : 0 ≤ w) (F : α → EReal) :
    ((w : ℝ) : EReal) * (∑ x ∈ s, F x) = (∑ x ∈ s, ((w : ℝ) : EReal) * F x) := by
  -- Induct on the finite set and use finite-scalar distributivity at each step.
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha hs =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [EReal.left_distrib_of_nonneg_of_ne_top]
      · rw [hs]
      · exact_mod_cast hw
      · exact EReal.coe_ne_top _

/-- Swap the two middle summands in a four-term commutative sum. -/
lemma add_swap_middle
    {α : Type*} [AddCommMonoid α] (a b c d : α) :
    a + b + (c + d) = a + c + (b + d) := by
  simp [add_left_comm, add_comm]

/-- Two `EReal` finite sums over the same set combine pointwise. -/
lemma ereal_sum_add_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (F G : α → EReal) :
    (∑ x ∈ s, F x) + (∑ x ∈ s, G x) = (∑ x ∈ s, (F x + G x)) := by
  rw [← Finset.sum_add_distrib]

/-- The front term `-m log τ` is convex on positive precisions. -/
lemma scaled_neglog_combo_le
    (p : LogConcaveLocationScaleMLE)
    {τ τ' θ : ℝ}
    (hτ : 0 < τ) (hτ' : 0 < τ') (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    -((p.m : EReal) * Real.log (θ * τ + (1 - θ) * τ')) ≤
      (θ : EReal) * (-((p.m : EReal) * Real.log τ)) +
        ((1 - θ : ℝ) : EReal) * (-((p.m : EReal) * Real.log τ')) := by
  -- Apply concavity of `log` and then multiply by the nonnegative constant `m`.
  have h1θ0 : 0 ≤ 1 - θ := by
    linarith
  have h01 : θ + (1 - θ) = 1 := by
    ring
  have hconc : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have hlog :
      θ * Real.log τ + (1 - θ) * Real.log τ' ≤
        Real.log (θ * τ + (1 - θ) * τ') := by
    have hτ_mem : τ ∈ Set.Ioi (0 : ℝ) := by
      simpa [Set.mem_Ioi] using hτ
    have hτ'_mem : τ' ∈ Set.Ioi (0 : ℝ) := by
      simpa [Set.mem_Ioi] using hτ'
    simpa [smul_eq_mul, h01] using hconc.2 hτ_mem hτ'_mem hθ0 h1θ0 h01
  have hm : 0 ≤ (p.m : ℝ) := by
    positivity
  have hmullog := mul_le_mul_of_nonneg_left hlog hm
  have hreal :
      -((p.m : ℝ) * Real.log (θ * τ + (1 - θ) * τ')) ≤
        -(θ * ((p.m : ℝ) * Real.log τ)) + -((1 - θ) * ((p.m : ℝ) * Real.log τ')) := by
    linarith
  norm_num [EReal.coe_mul, EReal.coe_add, EReal.coe_neg]
  exact_mod_cast hreal

theorem logConcaveLocationScaleMLE_precision_reformulation_convex
    (p : LogConcaveLocationScaleMLE)
    (f : ℝ → ℝ)
    (hf_logconcave : IsLogConcave (n := 1) (fun x : Fin 1 → ℝ => f (x 0)))
    (hg : p.g = fun t => if 0 < f t then (-Real.log (f t) : EReal) else ⊤) :
    (∀ r s θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      p.g (θ * r + (1 - θ) * s) ≤
        (θ : EReal) * p.g r + ((1 - θ : ℝ) : EReal) * p.g s) ∧
    (∀ x : Fin p.n → ℝ, ∀ μ σ τ : ℝ,
      p.isFeasible x μ σ →
      τ = σ⁻¹ →
      p.precisionObjective (fun j => τ * x j) (τ * μ) τ = p.objective x μ σ) ∧
    Convex ℝ {u : (Fin p.n → ℝ) × ℝ × ℝ | p.precisionFeasible u.1 u.2.1 u.2.2} ∧
    ∀ u u' : (Fin p.n → ℝ) × ℝ × ℝ, ∀ θ : ℝ,
      u ∈ {u : (Fin p.n → ℝ) × ℝ × ℝ | p.precisionFeasible u.1 u.2.1 u.2.2} →
      u' ∈ {u : (Fin p.n → ℝ) × ℝ × ℝ | p.precisionFeasible u.1 u.2.1 u.2.2} →
      0 ≤ θ →
      θ ≤ 1 →
      p.precisionObjective
          (fun i => θ * u.1 i + (1 - θ) * u'.1 i)
          (θ * u.2.1 + (1 - θ) * u'.2.1)
          (θ * u.2.2 + (1 - θ) * u'.2.2) ≤
        ((θ : EReal) * p.precisionObjective u.1 u.2.1 u.2.2 +
          ((1 - θ : ℝ) : EReal) * p.precisionObjective u'.1 u'.2.1 u'.2.2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- First prove convexity of the extended-value negative log term.
    intro r s θ hθ0 hθ1
    exact ereal_neglog_of_logConcave_le p f hf_logconcave hg r s θ hθ0 hθ1
  · intro x μ σ τ hσ hτ
    rcases hσ with hσ
    subst hτ
    -- Reparameterize with `τ = σ⁻¹` and normalize the residual algebra.
    unfold LogConcaveLocationScaleMLE.precisionObjective
    unfold LogConcaveLocationScaleMLE.objective
    congr 1
    · rw [Real.log_inv]
      norm_num [EReal.coe_mul, EReal.coe_neg]
    · apply Finset.sum_congr rfl
      intro i hi
      congr 1
      have hsum :
          (∑ j : Fin p.n, p.a i j * (σ⁻¹ * x j)) =
            σ⁻¹ * ∑ j : Fin p.n, p.a i j * x j := by
        calc
          (∑ j : Fin p.n, p.a i j * (σ⁻¹ * x j))
              = ∑ j : Fin p.n, σ⁻¹ * (p.a i j * x j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
          _ = σ⁻¹ * ∑ j : Fin p.n, p.a i j * x j := by
                rw [Finset.mul_sum]
      rw [div_eq_mul_inv, hsum]
      ring
  · -- Feasibility depends only on positivity of the precision coordinate.
    exact precisionFeasible_convex p
  · intro u u' θ hu hu' hθ0 hθ1
    have huτ : 0 < u.2.2 := hu
    have hu'τ : 0 < u'.2.2 := hu'
    have h1θ0 : 0 ≤ 1 - θ := by
      linarith
    have hfront := scaled_neglog_combo_le p huτ hu'τ hθ0 hθ1
    have hsum :
        ∑ i : Fin p.m,
          p.g
            (((θ * u.2.2 + (1 - θ) * u'.2.2) * p.y i) -
              (∑ j : Fin p.n, p.a i j * (θ * u.1 j + (1 - θ) * u'.1 j)) -
              (θ * u.2.1 + (1 - θ) * u'.2.1)) ≤
          ∑ i : Fin p.m,
            ((θ : EReal) * p.g (u.2.2 * p.y i - (∑ j : Fin p.n, p.a i j * u.1 j) - u.2.1) +
              ((1 - θ : ℝ) : EReal) *
                p.g (u'.2.2 * p.y i - (∑ j : Fin p.n, p.a i j * u'.1 j) - u'.2.1)) := by
      -- Apply the scalar convexity inequality to each residual separately and sum.
      apply Finset.sum_le_sum
      intro i hi
      simpa [precisionResidual_affine_combo] using
        ereal_neglog_of_logConcave_le p f hf_logconcave hg
          (u.2.2 * p.y i - (∑ j : Fin p.n, p.a i j * u.1 j) - u.2.1)
          (u'.2.2 * p.y i - (∑ j : Fin p.n, p.a i j * u'.1 j) - u'.2.1)
          θ hθ0 hθ1
    calc
      p.precisionObjective
          (fun i => θ * u.1 i + (1 - θ) * u'.1 i)
          (θ * u.2.1 + (1 - θ) * u'.2.1)
          (θ * u.2.2 + (1 - θ) * u'.2.2)
          =
        -((p.m : EReal) * Real.log (θ * u.2.2 + (1 - θ) * u'.2.2)) +
          ∑ i : Fin p.m,
            p.g
              (((θ * u.2.2 + (1 - θ) * u'.2.2) * p.y i) -
                (∑ j : Fin p.n, p.a i j * (θ * u.1 j + (1 - θ) * u'.1 j)) -
                (θ * u.2.1 + (1 - θ) * u'.2.1)) := by
            rfl
      _ ≤
        ((θ : EReal) * (-((p.m : EReal) * Real.log u.2.2)) +
            ((1 - θ : ℝ) : EReal) * (-((p.m : EReal) * Real.log u'.2.2))) +
          ∑ i : Fin p.m,
            ((θ : EReal) * p.g (u.2.2 * p.y i - (∑ j : Fin p.n, p.a i j * u.1 j) - u.2.1) +
              ((1 - θ : ℝ) : EReal) *
                p.g (u'.2.2 * p.y i - (∑ j : Fin p.n, p.a i j * u'.1 j) - u'.2.1)) := by
            exact add_le_add hfront hsum
      _ =
        ((θ : EReal) * p.precisionObjective u.1 u.2.1 u.2.2 +
          ((1 - θ : ℝ) : EReal) * p.precisionObjective u'.1 u'.2.1 u'.2.2) := by
            -- Expand the weighted objectives and distribute the finite scalar weights.
            symm
            unfold LogConcaveLocationScaleMLE.precisionObjective
            rw [EReal.left_distrib_of_nonneg_of_ne_top, EReal.left_distrib_of_nonneg_of_ne_top]
            · rw [ereal_mul_finset_sum_of_nonneg (Finset.univ : Finset (Fin p.m)) θ hθ0,
                ereal_mul_finset_sum_of_nonneg (Finset.univ : Finset (Fin p.m)) (1 - θ) h1θ0]
              calc
                (θ : EReal) * (-((p.m : EReal) * Real.log u.2.2)) +
                    ∑ x ∈ Finset.univ,
                      (θ : EReal) *
                        p.g (u.2.2 * p.y x - (∑ j : Fin p.n, p.a x j * u.1 j) - u.2.1) +
                  (((1 - θ : ℝ) : EReal) * (-((p.m : EReal) * Real.log u'.2.2)) +
                    ∑ x ∈ Finset.univ,
                      ((1 - θ : ℝ) : EReal) *
                        p.g (u'.2.2 * p.y x - (∑ j : Fin p.n, p.a x j * u'.1 j) - u'.2.1))
                    =
                  (θ : EReal) * (-((p.m : EReal) * Real.log u.2.2)) +
                    ((1 - θ : ℝ) : EReal) * (-((p.m : EReal) * Real.log u'.2.2)) +
                      ((∑ x ∈ Finset.univ,
                          (θ : EReal) *
                            p.g (u.2.2 * p.y x - (∑ j : Fin p.n, p.a x j * u.1 j) - u.2.1)) +
                        ∑ x ∈ Finset.univ,
                          ((1 - θ : ℝ) : EReal) *
                            p.g (u'.2.2 * p.y x - (∑ j : Fin p.n, p.a x j * u'.1 j) - u'.2.1)) := by
                      rw [add_swap_middle]
                _ =
                  (θ : EReal) * (-((p.m : EReal) * Real.log u.2.2)) +
                    ((1 - θ : ℝ) : EReal) * (-((p.m : EReal) * Real.log u'.2.2)) +
                      ∑ x ∈ Finset.univ,
                        ((θ : EReal) *
                            p.g (u.2.2 * p.y x - (∑ j : Fin p.n, p.a x j * u.1 j) - u.2.1) +
                          ((1 - θ : ℝ) : EReal) *
                            p.g (u'.2.2 * p.y x - (∑ j : Fin p.n, p.a x j * u'.1 j) - u'.2.1)) := by
                      rw [ereal_sum_add_sum]
            · exact_mod_cast h1θ0
            · exact EReal.coe_ne_top _
            · exact_mod_cast hθ0
            · exact EReal.coe_ne_top _

end «problem-136»
