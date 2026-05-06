import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-13»
/-
Exercise 8.11 | 12 | defn

The damped Newton method uses the Newton direction δx^{(k)} = −(∇²f(x^{(k)}))⁻¹ ∇f(x^{(k)}) and
updates x^{(k + 1)} = x^{(k)} + t^{(k)}δx^{(k)}, where t^{(k)} ∈ (0, 1].
-/

def ScalarNewtonMethod
    (f : ℝ → ℝ) (deriv : ℝ → ℝ) (secondDeriv : ℝ → ℝ)
    (xStar x0 : ℝ) (hx0_lt_xStar : x0 < xStar) : ℕ → ℝ
  | 0 => x0
  | k + 1 => ScalarNewtonMethod f deriv secondDeriv xStar x0 hx0_lt_xStar k
      - deriv (ScalarNewtonMethod f deriv secondDeriv xStar x0 hx0_lt_xStar k) /
          secondDeriv (ScalarNewtonMethod f deriv secondDeriv xStar x0 hx0_lt_xStar k)

def ScalarNewtonDirection
    (deriv : ℝ → ℝ) (secondDeriv : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv x / secondDeriv x

def ScalarFullNewtonArmijo
    (f : ℝ → ℝ) (deriv : ℝ → ℝ) (secondDeriv : ℝ → ℝ) (α x : ℝ) : Prop :=
  let d := ScalarNewtonDirection deriv secondDeriv x
  f (x + d) ≤ f x + α * deriv x * d

/-
Exercise 8.11 | 16 | algo

The damped Newton method with backtracking line search is defined by δx^{(k)} = - f′(x^{(k)}) /
f″(x^{(k)}), x^{(k + 1)} = x^{(k)} + t^{(k)}δx^{(k)}, where t^{(k)} ∈ (0, 1] is the first element of
the sequence 1, β, β², …, with fixed α ∈ (0, 1/2) and β ∈ (0, 1), such that f(x^{(k)} +
t^{(k)}δx^{(k)}) ≤ f(x^{(k)}) + α t^{(k)} f′(x^{(k)})δx^{(k)}.
-/
structure ScalarDampedNewtonBacktracking where
  f : ℝ → ℝ
  deriv : ℝ → ℝ
  secondDeriv : ℝ → ℝ
  α : ℝ
  β : ℝ
  x0 : ℝ
  hα : 0 < α ∧ α < (1 / 2 : ℝ)
  hβ : 0 < β ∧ β < 1
  x : ℕ → ℝ
  t : ℕ → ℝ
  hx0 : x 0 = x0
  ht_bounds : ∀ k : ℕ, 0 < t k ∧ t k ≤ 1
  hstep : ∀ k : ℕ,
    x (k + 1) = x k + t k * (-deriv (x k) / secondDeriv (x k))
  ht_first : ∀ k : ℕ,
    ∃ m : ℕ,
      t k = β ^ m ∧
      f (x k + t k * (-deriv (x k) / secondDeriv (x k))) ≤
        f (x k) + α * t k * deriv (x k) * (-deriv (x k) / secondDeriv (x k)) ∧
      ∀ j : ℕ, j < m →
        ¬ (f (x k + (β ^ j) * (-deriv (x k) / secondDeriv (x k))) ≤
            f (x k) + α * (β ^ j) * deriv (x k) * (-deriv (x k) / secondDeriv (x k)))

def ScalarDampedNewtonBacktracking.direction (N : ScalarDampedNewtonBacktracking) (x : ℝ) : ℝ :=
  -N.deriv x / N.secondDeriv x

def ScalarDampedNewtonBacktracking.armijoAt (N : ScalarDampedNewtonBacktracking) (x : ℝ)
    (t : ℝ) : Prop :=
  N.f (x + t * N.direction x) ≤ N.f x + N.α * t * N.deriv x * N.direction x

def ScalarDampedNewtonBacktracking.stepSize (N : ScalarDampedNewtonBacktracking) (x : ℝ) : Prop :=
  ∃ k : ℕ,
    let t : ℝ := N.β ^ k
    N.armijoAt x t ∧
      ∀ j : ℕ, j < k → ¬N.armijoAt x (N.β ^ j)

def ScalarDampedNewtonBacktracking.step (N : ScalarDampedNewtonBacktracking) (x : ℝ)
    (t : ℝ) : ℝ :=
  x + t * N.direction x

def ScalarDampedNewtonBacktracking.iterate (N : ScalarDampedNewtonBacktracking)
    (stepSize : ℕ → ℝ) : ℕ → ℝ
  | 0 => N.x0
  | k + 1 => N.step (N.iterate stepSize k) (stepSize k)

/-
Let f: ℝ→ℝ be a C^{3} function that is strongly convex and smooth on ℝ, and assume that f'''(x) ≤ 0
for all x∈ ℝ. Let x*∈ ℝ be the minimizer of f. Since f is strongly convex, x* is unique, f'(x*) = 0,
and f''(x) > 0 for all x∈ℝ. Define Newton's method by x^{(k + 1)} =
x^{(k)} - \frac{f'(x^{(k)})}{f''(x^{(k)})}, k = 0, 1, 2, ..., with initial point x^{(0)} < x*. Also
define damped Newton backtracking by δ x^{(k)} = - \frac{f'(x^{(k)})}{f''(x^{(k)})}, x^{(k + 1)} =
x^{(k)} + t^{(k)}δ x^{(k)}, where t^{(k)}∈(0, 1] is the first element of the sequence 1, β, β^{2},
...,
with fixed α∈(0, 1/2) and β∈(0, 1), such that f(x^{(k)} + t^{(k)}δ x^{(k)}) ≤ f(x^{(k)}) + α t^{(k)}
f'(x^{(k)})δ x^{(k)}. Show that the Newton iterates x^{(k)} converge monotonically to x*, and that
t^{(k)} = 1 for all k. More precisely, each full Newton step is a nonnegative step that stays in
the interval (-∞, x*], satisfies the full-step Armijo condition, decreases the objective, and hence
is the first backtracking trial.
-/
theorem scalar_newton_monotone_converges_and_backtracking_unit_steps
    (f : ℝ → ℝ)
    (xStar x0 α β : ℝ)
    (hx0_lt_xStar : x0 < xStar)
    (hC3 : ContDiff ℝ 3 f)
    (hstrong_convex : ∃ m : ℝ, 0 < m ∧ ∀ x : ℝ, m ≤ deriv^[2] f x)
    (hsmooth : ∃ L : ℝ, 0 ≤ L ∧ ∀ x : ℝ, deriv^[2] f x ≤ L)
    (hthird_nonpos : ∀ x : ℝ, deriv^[3] f x ≤ 0)
    (hminimizer : ∀ x : ℝ, f xStar ≤ f x)
    (hderiv_xStar : deriv f xStar = 0)
    (hsecond_pos : ∀ x : ℝ, 0 < deriv^[2] f x)
    (hα : 0 < α ∧ α < (1 / 2 : ℝ))
    (hβ : 0 < β ∧ β < 1) :
    (∀ k : ℕ,
      let xk := ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar k
      let xnext := ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar (k + 1)
      let dk := ScalarNewtonDirection (deriv f) (deriv^[2] f) xk
      x0 ≤ xk ∧
      xk ≤ xStar ∧
      deriv f xk ≤ 0 ∧
      xk ≤ xnext ∧
      xnext ≤ xStar ∧
      0 < (deriv^[2] f) xk ∧
      0 ≤ dk ∧
      xnext = xk + dk ∧
      ScalarFullNewtonArmijo f (deriv f) (deriv^[2] f) α xk ∧
      f xStar ≤ f xnext ∧
      f xnext ≤ f xk) ∧
    Tendsto (ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar) atTop (𝓝 xStar) ∧
    -- backtracking always accepts the full Newton step (t^(k) = 1 for all k)
    (∀ N : ScalarDampedNewtonBacktracking,
      N.f = f →
      N.deriv = deriv f →
      N.secondDeriv = deriv^[2] f →
      N.α = α →
      N.β = β →
      N.x0 = x0 →
      N.x = ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar →
      ∀ k : ℕ, N.t k = 1) := by
  -- Route correction: prove reusable one-step facts first, then lift them to the iterates.
  let seq : ℕ → ℝ := ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar
  let direction : ℝ → ℝ := fun x => ScalarNewtonDirection (deriv f) (deriv^[2] f) x
  have hf_diff : Differentiable ℝ f := hC3.differentiable (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hderiv_diff : Differentiable ℝ (deriv f) :=
    hC3.deriv'.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hsecond_diff : Differentiable ℝ (deriv^[2] f) := by
    simpa using (hC3.deriv'.deriv').differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hderiv_cont : Continuous (deriv f) :=
    hC3.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hstrict : StrictConvexOn ℝ Set.univ f :=
    strictConvexOn_univ_of_deriv2_pos hC3.continuous hsecond_pos
  have hconcave : ConcaveOn ℝ Set.univ (deriv f) := by
    refine concaveOn_univ_of_deriv2_nonpos hderiv_diff hsecond_diff ?_
    intro x
    simpa [Function.comp] using hthird_nonpos x
  have hsecond_antitone : Antitone (deriv^[2] f) :=
    antitone_of_deriv_nonpos hsecond_diff (fun x => by simpa using hthird_nonpos x)
  -- This is the geometric one-step fact: the derivative is nonpositive, the Newton step is
  -- nonnegative, and the step cannot overshoot the minimizer.
  have hdirection_geom :
      ∀ {x : ℝ}, x ≤ xStar →
        deriv f x ≤ 0 ∧ 0 ≤ direction x ∧ direction x ≤ xStar - x := by
    intro x hx
    rcases lt_or_eq_of_le hx with hlt | rfl
    · have hderiv_lt : deriv f x < slope f x xStar :=
        hstrict.deriv_lt_slope (by simp) (by simp) hlt (hf_diff x)
      have hslope_nonpos : slope f x xStar ≤ 0 := by
        rw [slope_def_field]
        exact div_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (hminimizer x))
          (sub_nonneg.mpr hx)
      have hderiv_nonpos : deriv f x ≤ 0 := hderiv_lt.le.trans hslope_nonpos
      have hslope_deriv : slope (deriv f) x xStar ≤ deriv^[2] f x := by
        simpa [iteratedDeriv_eq_iterate] using
          hconcave.slope_le_deriv (by simp) (by simp) hlt (hderiv_diff x)
      have hslope_deriv' : -deriv f x / (xStar - x) ≤ deriv^[2] f x := by
        simpa [slope_def_field, hderiv_xStar, sub_eq_add_neg] using hslope_deriv
      have hbound_num : -deriv f x ≤ deriv^[2] f x * (xStar - x) :=
        (div_le_iff₀ (sub_pos.mpr hlt)).mp hslope_deriv'
      refine ⟨hderiv_nonpos, ?_, ?_⟩
      · simpa [direction, ScalarNewtonDirection] using
          div_nonneg (neg_nonneg.mpr hderiv_nonpos) (le_of_lt (hsecond_pos x))
      · exact (div_le_iff₀ (hsecond_pos x)).2 (by
          simpa [direction, ScalarNewtonDirection, mul_comm] using hbound_num)
    · simpa [direction, ScalarNewtonDirection, hderiv_xStar]
  -- This packages the full-step Armijo estimate and the objective decrease.
  have hfull_step :
      ∀ {x : ℝ}, x ≤ xStar →
        ScalarFullNewtonArmijo f (deriv f) (deriv^[2] f) α x ∧
          f xStar ≤ f (x + direction x) ∧
          f (x + direction x) ≤ f x := by
    intro x hx
    rcases hdirection_geom hx with ⟨hderiv_nonpos, hd_nonneg, hd_le⟩
    set d : ℝ := direction x with hd_def
    have hd_eq : direction x = d := hd_def.symm
    have hd_eq' : ScalarNewtonDirection (deriv f) (deriv (deriv f)) x = d := by
      simpa [direction, iteratedDeriv_eq_iterate] using hd_eq
    have hmin' : f xStar ≤ f (x + d) := by
      simpa [direction, hd_def] using hminimizer (x + d)
    by_cases hd_zero : d = 0
    · refine ⟨?_, hmin', ?_⟩
      · change
          f (x + ScalarNewtonDirection (deriv f) (deriv^[2] f) x) ≤
            f x + α * deriv f x * ScalarNewtonDirection (deriv f) (deriv^[2] f) x
        simpa [iteratedDeriv_eq_iterate, hd_eq', hd_zero]
      · simpa [hd_eq, hd_zero]
    · have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg (by simpa [eq_comm] using hd_zero)
      have hs : UniqueDiffOn ℝ (Set.Icc x (x + d)) := uniqueDiffOn_Icc (by linarith)
      have hsx : UniqueDiffWithinAt ℝ (Set.Icc x (x + d)) x :=
        hs.uniqueDiffWithinAt (by constructor <;> linarith)
      have hderivWithin : derivWithin f (Set.Icc x (x + d)) x = deriv f x :=
        (hf_diff x).derivWithin hsx
      -- Taylor's theorem gives the second-order remainder with a pointwise Hessian bound.
      obtain ⟨ξ, hξ, hTaylor⟩ :=
        taylor_mean_remainder_lagrange_iteratedDeriv
          (f := f) (x := x + d) (x₀ := x) (n := 1)
          (by linarith)
          ((hC3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffOn)
      have hTaylorEval :
          taylorWithinEval f 1 (Set.Icc x (x + d)) x (x + d) = f x + d * deriv f x := by
        rw [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_one,
          hderivWithin]
        norm_num
      have hrem_le : iteratedDeriv 2 f ξ * d ^ 2 / 2 ≤ deriv^[2] f x * d ^ 2 / 2 := by
        have hξ_le : iteratedDeriv 2 f ξ ≤ deriv^[2] f x := by
          have : deriv^[2] f ξ ≤ deriv^[2] f x := hsecond_antitone (le_of_lt hξ.1)
          simpa [iteratedDeriv_eq_iterate] using this
        have hd_sq_nonneg : 0 ≤ d ^ 2 := sq_nonneg d
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hξ_le hd_sq_nonneg)
          (by norm_num)
      have hupper : f (x + d) ≤ f x + d * deriv f x + deriv^[2] f x * d ^ 2 / 2 := by
        have hpow : (x + d - x) ^ 2 = d ^ 2 := by ring
        have hEq :
            f (x + d) =
              taylorWithinEval f 1 (Set.Icc x (x + d)) x (x + d) +
                iteratedDeriv 2 f ξ * d ^ 2 / 2 := by
          rw [show iteratedDeriv (1 + 1) f ξ = iteratedDeriv 2 f ξ by rfl, hpow] at hTaylor
          nlinarith
        have hadd :
            f x + d * deriv f x + iteratedDeriv 2 f ξ * d ^ 2 / 2 ≤
              f x + d * deriv f x + deriv^[2] f x * d ^ 2 / 2 := by
          nlinarith [hrem_le]
        calc
          f (x + d) =
              taylorWithinEval f 1 (Set.Icc x (x + d)) x (x + d) +
                iteratedDeriv 2 f ξ * d ^ 2 / 2 := hEq
          _ = f x + d * deriv f x + iteratedDeriv 2 f ξ * d ^ 2 / 2 := by
              rw [hTaylorEval]
          _ ≤ f x + d * deriv f x + deriv^[2] f x * d ^ 2 / 2 := hadd
      have hquad : d * deriv f x + deriv^[2] f x * d ^ 2 / 2 = deriv f x * d / 2 := by
        have hsec_pos : 0 < deriv^[2] f x := hsecond_pos x
        have hquad' :
            direction x * deriv f x + deriv^[2] f x * direction x ^ 2 / 2 =
              deriv f x * direction x / 2 := by
          dsimp [direction, ScalarNewtonDirection]
          field_simp [hsec_pos.ne']
          ring
        rw [hd_def]
        exact hquad'
      -- The Newton identity turns the quadratic model into a half-gradient decrease.
      have hhalf : f (x + d) ≤ f x + deriv f x * d / 2 := by
        nlinarith [hupper, hquad]
      have hprod_nonpos : deriv f x * d ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hderiv_nonpos hd_nonneg
      have hArmijoBound : f x + deriv f x * d / 2 ≤ f x + α * deriv f x * d := by
        nlinarith [hα.2, hprod_nonpos]
      have hdescent : f (x + d) ≤ f x := by
        have : f x + deriv f x * d / 2 ≤ f x := by
          nlinarith [hprod_nonpos]
        exact hhalf.trans this
      refine ⟨?_, hmin', hdescent⟩
      change
        f (x + ScalarNewtonDirection (deriv f) (deriv^[2] f) x) ≤
          f x + α * deriv f x * ScalarNewtonDirection (deriv f) (deriv^[2] f) x
      simpa [iteratedDeriv_eq_iterate, hd_eq'] using hhalf.trans hArmijoBound
  -- Induct only on the interval bounds; every other one-step property is reused from above.
  have hstate : ∀ k : ℕ, x0 ≤ seq k ∧ seq k ≤ xStar := by
    intro k
    induction k with
    | zero =>
        constructor
        · change x0 ≤ x0
          exact le_rfl
        · simpa [seq, iteratedDeriv_eq_iterate] using hx0_lt_xStar.le
    | succ k ih =>
        rcases ih with ⟨hx0_le, hxk_le⟩
        rcases hdirection_geom hxk_le with ⟨_, hd_nonneg, hd_le⟩
        have hstep_eq : seq (k + 1) = seq k + direction (seq k) := by
          change
            seq k - deriv f (seq k) / (deriv^[2] f) (seq k) = seq k + direction (seq k)
          simp [direction, ScalarNewtonDirection, sub_eq_add_neg, iteratedDeriv_eq_iterate,
            neg_div]
        constructor
        · rw [hstep_eq]
          linarith
        · rw [hstep_eq]
          linarith
  -- This reassembles the exact first conjunct from the generic one-step lemmas.
  have hiter :
      ∀ k : ℕ,
        let xk := seq k
        let xnext := seq (k + 1)
        let dk := direction xk
        x0 ≤ xk ∧
        xk ≤ xStar ∧
        deriv f xk ≤ 0 ∧
        xk ≤ xnext ∧
        xnext ≤ xStar ∧
        0 < (deriv^[2] f) xk ∧
        0 ≤ dk ∧
        xnext = xk + dk ∧
        ScalarFullNewtonArmijo f (deriv f) (deriv^[2] f) α xk ∧
        f xStar ≤ f xnext ∧
        f xnext ≤ f xk := by
    intro k
    rcases hstate k with ⟨hx0_le, hxk_le⟩
    rcases hdirection_geom hxk_le with ⟨hderiv_nonpos, hd_nonneg, hd_le⟩
    rcases hfull_step hxk_le with ⟨harmijo, hobj_lo, hobj_hi⟩
    have hstep_eq : seq (k + 1) = seq k + direction (seq k) := by
      change
        seq k - deriv f (seq k) / (deriv^[2] f) (seq k) = seq k + direction (seq k)
      simp [direction, ScalarNewtonDirection, sub_eq_add_neg, iteratedDeriv_eq_iterate, neg_div]
    refine ⟨hx0_le, hxk_le, hderiv_nonpos, ?_, ?_, hsecond_pos (seq k), hd_nonneg, hstep_eq,
      harmijo, ?_, ?_⟩
    · rw [hstep_eq]
      linarith
    · rw [hstep_eq]
      linarith
    · simpa [hstep_eq] using hobj_lo
    · simpa [hstep_eq] using hobj_hi
  obtain ⟨m, hm_pos, hm_lower⟩ := hstrong_convex
  obtain ⟨L, hL_nonneg, hL_upper⟩ := hsmooth
  have hm_le_L : m ≤ L := (hm_lower xStar).trans (hL_upper xStar)
  have hL_pos : 0 < L := lt_of_lt_of_le hm_pos hm_le_L
  let q : ℝ := 1 - m / L
  have hq_nonneg : 0 ≤ q := by
    have hdiv_le_one : m / L ≤ 1 := (div_le_iff₀ hL_pos).2 (by simpa using hm_le_L)
    dsimp [q]
    linarith
  have hq_lt_one : q < 1 := by
    have hdiv_pos : 0 < m / L := div_pos hm_pos hL_pos
    dsimp [q]
    linarith
  -- The strong-convexity/smoothness bounds give a uniform linear contraction of the error.
  have hcontract :
      ∀ {x : ℝ}, x ≤ xStar →
        xStar - (x + direction x) ≤ q * (xStar - x) := by
    intro x hx
    rcases lt_or_eq_of_le hx with hlt | rfl
    · have hgap_pos : 0 < xStar - x := sub_pos.mpr hlt
      obtain ⟨ξ, hξ, hξeq⟩ :=
        exists_deriv_eq_slope (f := deriv f) hlt
          hderiv_cont.continuousOn hderiv_diff.differentiableOn
      have hnum_bound : m * (xStar - x) ≤ -deriv f x := by
        have hmξ : m ≤ deriv^[2] f ξ := hm_lower ξ
        have hdiv : m ≤ (-deriv f x) / (xStar - x) := by
          simpa [iteratedDeriv_eq_iterate, Function.comp, slope_def_field, hderiv_xStar,
            sub_eq_add_neg, zero_sub] using hmξ.trans_eq hξeq
        exact (le_div_iff₀ hgap_pos).mp hdiv
      have hnum_nonneg : 0 ≤ -deriv f x := by
        have hlhs_pos : 0 < m * (xStar - x) := mul_pos hm_pos hgap_pos
        linarith
      have hdir_lower : (m / L) * (xStar - x) ≤ direction x := by
        have hdiv1 : (m * (xStar - x)) / L ≤ (-deriv f x) / L :=
          div_le_div_of_nonneg_right hnum_bound hL_nonneg
        have hdiv2 : (-deriv f x) / L ≤ (-deriv f x) / deriv^[2] f x :=
          div_le_div_of_nonneg_left hnum_nonneg (hsecond_pos x) (hL_upper x)
        have hchain : (m * (xStar - x)) / L ≤ (-deriv f x) / deriv^[2] f x :=
          hdiv1.trans hdiv2
        simpa [direction, ScalarNewtonDirection, div_eq_mul_inv, mul_assoc, mul_left_comm,
          mul_comm] using hchain
      dsimp [q]
      nlinarith
    · simp [q, direction, ScalarNewtonDirection, hderiv_xStar]
  have hgap_geometric : ∀ k : ℕ, xStar - seq k ≤ q ^ k * (xStar - x0) := by
    intro k
    induction k with
    | zero =>
        change xStar - x0 ≤ q ^ 0 * (xStar - x0)
        simp
    | succ k ih =>
        rcases hstate k with ⟨_, hxk_le⟩
        calc
          xStar - seq (k + 1) = xStar - (seq k + direction (seq k)) := by
              change
                xStar - (seq k - deriv f (seq k) / (deriv^[2] f) (seq k)) =
                  xStar - (seq k + direction (seq k))
              simp [direction, ScalarNewtonDirection, sub_eq_add_neg, iteratedDeriv_eq_iterate,
                neg_div]
          _ ≤ q * (xStar - seq k) := hcontract hxk_le
          _ ≤ q * (q ^ k * (xStar - x0)) := by
              gcongr
          _ = q ^ (k + 1) * (xStar - x0) := by
              rw [pow_succ]
              ring
  have hgeom_tendsto : Tendsto (fun k : ℕ => q ^ k * (xStar - x0)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
    simpa using hpow.mul tendsto_const_nhds
  have hgap_tendsto : Tendsto (fun k : ℕ => xStar - seq k) atTop (𝓝 0) :=
    squeeze_zero
      (fun k => sub_nonneg.mpr (hstate k).2)
      hgap_geometric
      hgeom_tendsto
  have hseq_tendsto : Tendsto seq atTop (𝓝 xStar) := by
    have hsub : Tendsto (fun k : ℕ => xStar - (xStar - seq k)) atTop (𝓝 (xStar - 0)) :=
      tendsto_const_nhds.sub hgap_tendsto
    simpa using hsub
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simpa [seq, direction]
      using hiter k
  · simpa [seq] using hseq_tendsto
  · intro N hNf hNderiv hNsecond hNα hNβ _ hNx k
    rcases hiter k with ⟨_, _, _, _, _, _, _, _, hkArmijo, _, _⟩
    have hkArmijoN : N.armijoAt (N.x k) 1 := by
      simpa [ScalarFullNewtonArmijo, ScalarDampedNewtonBacktracking.armijoAt,
        ScalarNewtonDirection, ScalarDampedNewtonBacktracking.direction, iteratedDeriv_eq_iterate,
        hNf, hNderiv, hNsecond, hNα, hNx]
        using hkArmijo
    obtain ⟨m', hm', _, hminimal⟩ := N.ht_first k
    have hm_zero : m' = 0 := by
      by_contra hm_ne
      have hm_pos : 0 < m' := Nat.pos_of_ne_zero hm_ne
      exact hminimal 0 hm_pos (by simpa [ScalarDampedNewtonBacktracking.armijoAt,
        ScalarDampedNewtonBacktracking.direction] using hkArmijoN)
    calc
      N.t k = N.β ^ m' := hm'
      _ = N.β ^ 0 := by rw [hm_zero]
      _ = 1 := by simp

end «problem-13»
