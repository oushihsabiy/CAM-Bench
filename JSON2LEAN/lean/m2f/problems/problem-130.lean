import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-130»
/-
For an extended - real - valued function f: ℝ^n→ℝ + ∞, the perspective closure of (t, x)mapsto t
f(x/t) is
the extension defined by g(t, x) = t f(x/t) for t > 0, and by g(0, x) = liminf_τdownarrow 0, y→ x τ
f(y/τ). For the exponential power term used below, on the domain x ≥ 0 this gives g(0, 0) = 0
and g(0, x) = +∞ for x > 0; negative x is intentionally kept outside the convex-program domain.
-/
def perspectiveClosure (f : ℝ → EReal) : ℝ → ℝ → EReal
  | t, x =>
      if _ : 0 < t then
        (t : EReal) * f (x / t)
      else if _ : t = 0 then
        Filter.liminf
          (fun p : ℝ × ℝ => ((p.1 : EReal) * f (p.2 / p.1)))
          ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝 x))
      else
        ⊤

/-
If f: ℝ^n → ℝ + ∞, its perspective is the function g: (0, ∞)× ℝ^n→ ℝ + ∞ defined by g(t, x) = t
f(x/t),
t > 0.
-/
def perspective (f : ℝ → EReal) : {t : ℝ // 0 < t} → ℝ → EReal
  | t, x => ((t : ℝ) : EReal) * f (x / (t : ℝ))

def logScaleShift (n : ℕ) (T : ℝ) : EReal :=
  ∑ _ : Fin n, (Real.log T : EReal)

/-
Let n ∈ ℕ, let aᵢ > 0 for i = 1, ..., n, and let b > 0, T > 0, and P^{max}∈ℝ. Consider the
optimization problem in the variables r = (r₁, ..., rₙ)∈ℝ^n and t = (t₁, ..., tₙ)∈ℝ^n: maximize &
\sum_{i = 1}^n log rᵢ; subject to & (1)/(T)\sum_{i = 1}^n tᵢ aᵢ(e^{bTr_i/tᵢ} - 1) ≤ P^{max},; &
\sum_{i =
1}^n tᵢ = T,; & tᵢ ≥ 0 (i = 1, ..., n), where each term is interpreted via the perspective closure:
if tᵢ = 0 and rᵢ = 0, then tᵢ e^{bTr_i/tᵢ} = 0, while if tᵢ = 0 and rᵢ > 0, the power is + ∞.
-/
structure TimeAllocationPowerMaximization where
  n : ℕ
  n_pos : 0 < n
  a : Fin n → ℝ
  a_pos : ∀ i, 0 < a i
  b : ℝ
  b_pos : 0 < b
  T : ℝ
  T_pos : 0 < T
  Pmax : ℝ

def TimeAllocationPowerMaximization.powerTerm
    (P : TimeAllocationPowerMaximization)
    (t r : Fin P.n → ℝ)
    (i : Fin P.n) : EReal :=
  perspectiveClosure
    (fun x => ((P.a i) : EReal) * (EReal.exp (P.b * P.T * x) - 1))
    (t i) (r i)

def TimeAllocationPowerMaximization.totalPower
    (P : TimeAllocationPowerMaximization)
    (t r : Fin P.n → ℝ) : EReal :=
  ((P.T : EReal)⁻¹) * ∑ i, P.powerTerm t r i

def TimeAllocationPowerMaximization.timeConstraint
    (P : TimeAllocationPowerMaximization)
    (t : Fin P.n → ℝ) : Prop :=
  ∑ i, t i = P.T

def TimeAllocationPowerMaximization.nonnegativeTimes
    (P : TimeAllocationPowerMaximization)
    (t : Fin P.n → ℝ) : Prop :=
  ∀ i, 0 ≤ t i

def TimeAllocationPowerMaximization.positiveRates
    (P : TimeAllocationPowerMaximization)
    (r : Fin P.n → ℝ) : Prop :=
  ∀ i, 0 < r i

def TimeAllocationPowerMaximization.feasible
    (P : TimeAllocationPowerMaximization)
    (r t : Fin P.n → ℝ) : Prop :=
  P.totalPower t r ≤ P.Pmax ∧ P.timeConstraint t ∧ P.nonnegativeTimes t

def TimeAllocationPowerMaximization.objective
    (P : TimeAllocationPowerMaximization)
    (r : Fin P.n → ℝ) : EReal :=
  if _ : ∀ i, 0 < r i then
    ∑ i, (Real.log (r i) : EReal)
  else
    ⊥

/-
minimize & - \sum_{i = 1}^n log xᵢ; subject to & (1)/(T)\sum_{i = 1}^n aᵢ(tᵢ e^{b xᵢ/tᵢ} - tᵢ) ≤
P^{max},; & \sum_{i = 1}^n tᵢ = T,; & tᵢ ≥ 0 (i = 1, ..., n),; & xᵢ > 0 (i = 1, ..., n), where xᵢ =
T
rᵢ for i = 1, ..., n.
-/
structure ConvexReformulatedProgram where
  n : ℕ
  n_pos : 0 < n
  a : Fin n → ℝ
  a_pos : ∀ i, 0 < a i
  b : ℝ
  b_pos : 0 < b
  T : ℝ
  T_pos : 0 < T
  Pmax : ℝ

def ConvexReformulatedProgram.powerTerm
    (P : ConvexReformulatedProgram)
    (t x : Fin P.n → ℝ)
    (i : Fin P.n) : EReal :=
  perspectiveClosure
    (fun y => ((P.a i) : EReal) * (EReal.exp (P.b * y) - 1))
    (t i) (x i)

def ConvexReformulatedProgram.totalPower
    (P : ConvexReformulatedProgram)
    (t x : Fin P.n → ℝ) : EReal :=
  ((P.T : EReal)⁻¹) * ∑ i, P.powerTerm t x i

def ConvexReformulatedProgram.timeConstraint
    (P : ConvexReformulatedProgram)
    (t : Fin P.n → ℝ) : Prop :=
  ∑ i, t i = P.T

def ConvexReformulatedProgram.nonnegativeTimes
    (P : ConvexReformulatedProgram)
    (t : Fin P.n → ℝ) : Prop :=
  ∀ i, 0 ≤ t i

def ConvexReformulatedProgram.positiveVariables
    (P : ConvexReformulatedProgram)
    (x : Fin P.n → ℝ) : Prop :=
  ∀ i, 0 < x i

def ConvexReformulatedProgram.feasible
    (P : ConvexReformulatedProgram)
    (x t : Fin P.n → ℝ) : Prop :=
  P.totalPower t x ≤ P.Pmax ∧
    P.timeConstraint t ∧
    P.nonnegativeTimes t ∧
    P.positiveVariables x

def ConvexReformulatedProgram.objective
    (P : ConvexReformulatedProgram)
    (x : Fin P.n → ℝ) : EReal :=
  -∑ i, (Real.log (x i) : EReal)

def ConvexReformulatedProgram.rateVariables
    (P : ConvexReformulatedProgram)
    (x : Fin P.n → ℝ)
    (i : Fin P.n) : ℝ :=
  x i / P.T

/-- Rewrite `EReal.exp` of a real quotient back to the corresponding real exponential. -/
lemma ereal_exp_mul_div (c u v : ℝ) :
    EReal.exp (c * (u / v)) = ENNReal.ofReal (Real.exp (c * (u / v))) := by
  -- Re-express the `EReal` argument as the coercion of the original real product.
  have hinner : ((c * (u / v) : ℝ) : EReal) = ((c : EReal) * ((u : EReal) / v)) := by
    have hdiv : ((↑u / ↑v : EReal)) = (((u / v : ℝ)) : EReal) := by
      norm_num [div_eq_mul_inv, EReal.coe_mul, EReal.coe_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      (((c * (u / v) : ℝ)) : EReal) = (↑c * (((u / v : ℝ)) : EReal) : EReal) := by
        rw [← EReal.coe_mul]
      _ = ((c : EReal) * ((u : EReal) / v)) := by
        rw [hdiv]
  simpa [EReal.exp_coe] using congrArg EReal.exp hinner.symm

/-- On the positive branch, the exponential perspective term is an ordinary real expression. -/
lemma positive_branch_exponential_perspective_eq_real (a c t x : ℝ) :
    ((t : EReal) * ((a : EReal) * (EReal.exp (c * (x / t)) - 1))) =
      ((t * (a * (Real.exp (c * (x / t)) - 1))) : EReal) := by
  -- Rewrite the exponential term to a real-valued expression before collapsing the coercions.
  rw [ereal_exp_mul_div]
  rw [ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg _)]
  change ((t : EReal) * ((a : EReal) * (((Real.exp (c * (x / t)) : ℝ) : EReal) - 1))) = _
  rfl

/-- If the carried variable is positive, the zero-time exponential perspective term is `⊤`. -/
lemma perspectiveClosure_exponential_zero_eq_top (a c x : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hx : 0 < x) :
    perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) 0 x = ⊤ := by
  -- Route correction: at `t = 0` we prove the liminf is `⊤` by forcing a real lower bound to diverge.
  rw [perspectiveClosure]
  simp
  have haux : Tendsto
      (fun p : ℝ × ℝ => (a / 2) * (Real.exp ((c * (x / 2)) * p.1⁻¹) / p.1⁻¹))
      (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x)) atTop := by
    -- After the substitution `u = p.1⁻¹`, exponential growth dominates the linear denominator.
    have hinv : Tendsto (fun p : ℝ × ℝ => p.1⁻¹) (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x)) atTop := by
      exact tendsto_inv_nhdsGT_zero.comp tendsto_fst
    have hexp : Tendsto
        (fun p : ℝ × ℝ => Real.exp ((c * (x / 2)) * p.1⁻¹) / ((p.1⁻¹) ^ (1 : ℝ)))
        (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x)) atTop := by
      exact (tendsto_exp_mul_div_rpow_atTop (1 : ℝ) (c * (x / 2)) (by positivity)).comp hinv
    simpa using hexp.const_mul_atTop (by positivity : 0 < a / 2)
  have hmain : Tendsto
      (fun p : ℝ × ℝ => (((p.1 : EReal) * ((a : EReal) * (EReal.exp (c * (p.2 / p.1)) - 1))) : EReal))
      (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x)) (𝓝 ⊤) := by
    rw [EReal.tendsto_nhds_top_iff_real]
    intro z
    have hz := (tendsto_atTop.1 haux) (z + 1)
    have htwo : ∀ᶠ p : ℝ × ℝ in (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x)),
        2 ≤ Real.exp ((c * (x / 2)) * p.1⁻¹) := by
      -- The auxiliary exponential is eventually at least `2`, so subtracting `1` still preserves growth.
      have hinv : Tendsto (fun p : ℝ × ℝ => p.1⁻¹) (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x)) atTop := by
        exact tendsto_inv_nhdsGT_zero.comp tendsto_fst
      have hExp : Tendsto (fun u : ℝ => Real.exp ((c * (x / 2)) * u)) atTop atTop := by
        exact Real.tendsto_exp_atTop.comp
          (tendsto_id.const_mul_atTop (by positivity : 0 < c * (x / 2)))
      exact (hExp.comp hinv).eventually (eventually_ge_atTop (2 : ℝ))
    filter_upwards [hz,
      tendsto_fst.eventually (show ∀ᶠ q : ℝ in 𝓝[>] (0 : ℝ), 0 < q from self_mem_nhdsWithin),
      tendsto_snd.eventually (Ioi_mem_nhds (by linarith : x / 2 < x)),
      htwo] with p hz hp0 hpx htwo
    have hmon : Real.exp ((c * (x / 2)) * p.1⁻¹) ≤ Real.exp (c * (p.2 / p.1)) := by
      -- Replacing `x / 2` by the nearby value `p.2` only increases the exponent.
      apply Real.exp_le_exp.mpr
      have hcmp : c * (x / 2) ≤ c * p.2 := by
        nlinarith
      have hnonneg : 0 ≤ p.1⁻¹ := by
        positivity
      have := mul_le_mul_of_nonneg_right hcmp hnonneg
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have hsub : Real.exp ((c * (x / 2)) * p.1⁻¹) / 2 ≤ Real.exp (c * (p.2 / p.1)) - 1 := by
      -- The factor `1 / 2` is absorbed by the eventual bound `exp(...) ≥ 2`.
      have hhalf :
          Real.exp ((c * (x / 2)) * p.1⁻¹) / 2 ≤
            Real.exp ((c * (x / 2)) * p.1⁻¹) - 1 := by
        nlinarith [htwo]
      exact hhalf.trans (by linarith [hmon])
    have hp1 : 0 ≤ p.1 := le_of_lt hp0
    have ha' : 0 ≤ a := le_of_lt ha
    have hp1a : 0 ≤ p.1 * a := mul_nonneg hp1 ha'
    have hreal :
        (a / 2) * (Real.exp ((c * (x / 2)) * p.1⁻¹) / p.1⁻¹) ≤
          p.1 * (a * (Real.exp (c * (p.2 / p.1)) - 1)) := by
      -- Multiplying by the positive scalar `p.1 * a` transfers the exponential lower bound.
      have := mul_le_mul_of_nonneg_left hsub hp1a
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have hz_lt :
        z < (a / 2) * (Real.exp ((c * (x / 2)) * p.1⁻¹) / p.1⁻¹) := by
      linarith
    have hzE :
        ((z : ℝ) : EReal) <
          (((a / 2) * (Real.exp ((c * (x / 2)) * p.1⁻¹) / p.1⁻¹) : ℝ) : EReal) := by
      exact EReal.coe_lt_coe_iff.2 hz_lt
    have hrealE :
        ((((a / 2) * (Real.exp ((c * (x / 2)) * p.1⁻¹) / p.1⁻¹)) : ℝ) : EReal) ≤
          (((p.1 * (a * (Real.exp (c * (p.2 / p.1)) - 1))) : ℝ) : EReal) := by
      exact EReal.coe_le_coe_iff.2 hreal
    -- The real lower bound sits below the original `EReal` perspective term on the positive branch.
    have htarget := positive_branch_exponential_perspective_eq_real a c p.1 p.2
    exact lt_of_lt_of_le hzE (hrealE.trans htarget.ge)
  simpa using Filter.Tendsto.liminf_eq hmain

/-
Let n ∈ ℕ, let aᵢ > 0 for i = 1, ..., n, and let b > 0, T > 0, and P^{max}∈ℝ. Consider the
optimization problem time allocation power maximization. Prove that this problem is equivalent to
the convex optimization problem convex reformulated program.
-/
theorem timeAllocationPowerMaximization_equiv_convexReformulatedProgram
    (p : TimeAllocationPowerMaximization) :
    ∃ q : ConvexReformulatedProgram,
      ∃ hqn : q.n = p.n,
        (∀ i : Fin q.n, q.a i = p.a (Fin.cast hqn i)) ∧
        q.b = p.b ∧
        q.T = p.T ∧
        q.Pmax = p.Pmax ∧
        (∀ r t : Fin p.n → ℝ,
          q.feasible
              (fun i : Fin q.n => p.T * r (Fin.cast hqn i))
              (fun i : Fin q.n => t (Fin.cast hqn i)) ↔
            p.feasible r t ∧ p.positiveRates r) ∧
        (∀ x t : Fin q.n → ℝ,
          p.feasible
              (fun i : Fin p.n => x (Fin.cast hqn.symm i) / p.T)
              (fun i : Fin p.n => t (Fin.cast hqn.symm i)) ∧
            p.positiveRates (fun i : Fin p.n => x (Fin.cast hqn.symm i) / p.T) ↔
            q.feasible x t) ∧
        (∀ r : Fin p.n → ℝ,
          p.positiveRates r →
            q.objective (fun i : Fin q.n => p.T * r (Fin.cast hqn i)) =
              -p.objective r - logScaleShift p.n p.T) ∧
        (∀ x : Fin q.n → ℝ,
          q.positiveVariables x →
            p.objective (fun i : Fin p.n => x (Fin.cast hqn.symm i) / p.T) =
              -q.objective x - logScaleShift q.n q.T) ∧
        (∀ v : EReal,
          (∃ r t : Fin p.n → ℝ,
            p.feasible r t ∧ p.positiveRates r ∧ p.objective r = v) ↔
            ∃ x t : Fin q.n → ℝ,
              q.feasible x t ∧ q.objective x = -v - logScaleShift p.n p.T) ∧
        ((∃ r t : Fin p.n → ℝ,
            p.feasible r t ∧
            p.positiveRates r ∧
            ∀ r' t' : Fin p.n → ℝ,
              p.feasible r' t' ∧ p.positiveRates r' →
                p.objective r' ≤ p.objective r) ↔
          ∃ x t : Fin q.n → ℝ,
            q.feasible x t ∧
            ∀ x' t' : Fin q.n → ℝ,
              q.feasible x' t' →
                q.objective x ≤ q.objective x') := by
  let q : ConvexReformulatedProgram :=
    { n := p.n
      n_pos := p.n_pos
      a := p.a
      a_pos := p.a_pos
      b := p.b
      b_pos := p.b_pos
      T := p.T
      T_pos := p.T_pos
      Pmax := p.Pmax }
  -- Route correction: instead of forcing global strict positivity of all feasible times first,
  -- we compare each power term directly by splitting on `t i = 0` versus `0 < t i`.
  have hsum_coe :
      ∀ {n : ℕ} (f : Fin n → ℝ),
        (∑ i : Fin n, (f i : EReal)) = (((∑ i : Fin n, f i : ℝ)) : EReal) := by
    intro n f
    induction n with
    | zero =>
        simp
    | succ n ih =>
        simp [Fin.sum_univ_succ, ih]
  have hnegsum_coe :
      ∀ {n : ℕ} (f : Fin n → ℝ),
        -(∑ i : Fin n, (f i : EReal)) = (((-∑ i : Fin n, f i : ℝ)) : EReal) := by
    intro n f
    calc
      -(∑ i : Fin n, (f i : EReal)) = -((((∑ i : Fin n, f i : ℝ)) : EReal)) := by
        rw [hsum_coe f]
      _ = (((-∑ i : Fin n, f i : ℝ)) : EReal) := by
        simp
  -- These scaling identities let us rewrite arbitrary convex-side variables in the form `T * r`.
  have hscale_cancel :
      ∀ x : Fin p.n → ℝ, (fun i => p.T * (x i / p.T)) = x := by
    intro x
    funext i
    field_simp [p.T_pos.ne']
  have hunscale_cancel :
      ∀ r : Fin p.n → ℝ, (fun i => (p.T * r i) / p.T) = r := by
    intro r
    funext i
    field_simp [p.T_pos.ne']
  -- The logarithmic scale shift is a finite real constant inside `EReal`.
  have hshift_coe :
      logScaleShift p.n p.T = (((∑ i : Fin p.n, Real.log p.T : ℝ)) : EReal) := by
    simpa [logScaleShift] using hsum_coe (fun _ : Fin p.n => Real.log p.T)
  -- Positive rates are exactly the positive variables after multiplying by `T > 0`.
  have hpositive_scaled :
      ∀ {r : Fin p.n → ℝ},
        p.positiveRates r → q.positiveVariables (fun i => p.T * r i) := by
    intro r hr i
    simpa [q] using mul_pos p.T_pos (hr i)
  have hpositive_unscaled :
      ∀ {x : Fin p.n → ℝ},
        q.positiveVariables x → p.positiveRates (fun i => x i / p.T) := by
    intro x hx i
    have hx' : 0 < x i := hx i
    have : 0 < x i / p.T := by
      exact div_pos hx' p.T_pos
    simpa [q] using this
  -- On nonnegative times, the original and convex power terms agree after the scaling change.
  have hpower_forward :
      ∀ {r t : Fin p.n → ℝ} {i : Fin p.n},
        p.nonnegativeTimes t →
        p.positiveRates r →
        q.powerTerm t (fun j => p.T * r j) i = p.powerTerm t r i := by
    intro r t i ht hr
    have hti_nonneg : 0 ≤ t i := ht i
    by_cases hzero : t i = 0
    · -- At zero time, both closures are `⊤` because the carried variable is strictly positive.
      calc
        q.powerTerm t (fun j => p.T * r j) i
            = perspectiveClosure
                (fun y => ((p.a i : EReal) * (EReal.exp (p.b * y) - 1)))
                0 (p.T * r i) := by
                  simp [q, ConvexReformulatedProgram.powerTerm, hzero]
        _ = ⊤ := by
          apply perspectiveClosure_exponential_zero_eq_top
          · exact p.a_pos i
          · exact p.b_pos
          · exact mul_pos p.T_pos (hr i)
        _ = perspectiveClosure
              (fun y => ((p.a i : EReal) * (EReal.exp (p.b * p.T * y) - 1)))
              0 (r i) := by
                symm
                apply perspectiveClosure_exponential_zero_eq_top
                · exact p.a_pos i
                · exact mul_pos p.b_pos p.T_pos
                · exact hr i
        _ = p.powerTerm t r i := by
          simp [TimeAllocationPowerMaximization.powerTerm, hzero]
    · have hti_pos : 0 < t i := by
        exact lt_of_le_of_ne hti_nonneg (Ne.symm hzero)
      -- On the positive branch the two exponential arguments agree by elementary algebra.
      rw [ConvexReformulatedProgram.powerTerm, TimeAllocationPowerMaximization.powerTerm]
      simp [q, perspectiveClosure, hti_pos]
      have harg : p.b * ((p.T * r i) / t i) = p.b * p.T * (r i / t i) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      have hleft :
          ((p.b : EReal) * (((p.T * r i / t i : ℝ)) : EReal)) =
            (((p.b * (p.T * r i / t i) : ℝ)) : EReal) := by
        rw [← EReal.coe_mul]
      have hright :
          ((p.b : EReal) * (p.T : EReal) * (((r i / t i : ℝ)) : EReal)) =
            (((p.b * p.T * (r i / t i) : ℝ)) : EReal) := by
        rw [← EReal.coe_mul, ← EReal.coe_mul]
      rw [hleft, hright]
      simpa [harg]
  have hpower_backward :
      ∀ {x t : Fin p.n → ℝ} {i : Fin p.n},
        p.nonnegativeTimes t →
        q.positiveVariables x →
        p.powerTerm t (fun j => x j / p.T) i = q.powerTerm t x i := by
    intro x t i ht hx
    have hti_nonneg : 0 ≤ t i := ht i
    by_cases hzero : t i = 0
    · -- The reverse transport uses the same closure-at-zero fact after dividing by `T > 0`.
      calc
        p.powerTerm t (fun j => x j / p.T) i
            = perspectiveClosure
                (fun y => ((p.a i : EReal) * (EReal.exp (p.b * p.T * y) - 1)))
                0 (x i / p.T) := by
                  simp [TimeAllocationPowerMaximization.powerTerm, hzero]
        _ = ⊤ := by
          apply perspectiveClosure_exponential_zero_eq_top
          · exact p.a_pos i
          · exact mul_pos p.b_pos p.T_pos
          · exact div_pos (hx i) p.T_pos
        _ = perspectiveClosure
              (fun y => ((p.a i : EReal) * (EReal.exp (p.b * y) - 1)))
              0 (x i) := by
                symm
                apply perspectiveClosure_exponential_zero_eq_top
                · exact p.a_pos i
                · exact p.b_pos
                · exact hx i
        _ = q.powerTerm t x i := by
          simp [q, ConvexReformulatedProgram.powerTerm, hzero]
    · have hti_pos : 0 < t i := by
        exact lt_of_le_of_ne hti_nonneg (Ne.symm hzero)
      -- After unfolding the positive branch, the factor `T` cancels from the exponential argument.
      rw [TimeAllocationPowerMaximization.powerTerm, ConvexReformulatedProgram.powerTerm]
      simp [q, perspectiveClosure, hti_pos]
      have harg : p.b * p.T * ((x i / p.T) / t i) = p.b * (x i / t i) := by
        field_simp [div_eq_mul_inv, p.T_pos.ne']
      have hleft :
          ((p.b : EReal) * (p.T : EReal) * (((x i / p.T / t i : ℝ)) : EReal)) =
            (((p.b * p.T * (x i / p.T / t i) : ℝ)) : EReal) := by
        rw [← EReal.coe_mul, ← EReal.coe_mul]
      have hright :
          ((p.b : EReal) * (((x i / t i : ℝ)) : EReal)) =
            (((p.b * (x i / t i) : ℝ)) : EReal) := by
        rw [← EReal.coe_mul]
      rw [hleft, hright]
      simpa [harg]
  -- Summing the pointwise identities transports the total-power constraint.
  have htotal_forward :
      ∀ {r t : Fin p.n → ℝ},
        p.nonnegativeTimes t →
        p.positiveRates r →
        q.totalPower t (fun i => p.T * r i) = p.totalPower t r := by
    intro r t ht hr
    change ((p.T : EReal)⁻¹) * ∑ i : Fin p.n, q.powerTerm t (fun j => p.T * r j) i =
      ((p.T : EReal)⁻¹) * ∑ i : Fin p.n, p.powerTerm t r i
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact hpower_forward ht hr
  have htotal_backward :
      ∀ {x t : Fin p.n → ℝ},
        p.nonnegativeTimes t →
        q.positiveVariables x →
        p.totalPower t (fun i => x i / p.T) = q.totalPower t x := by
    intro x t ht hx
    change ((p.T : EReal)⁻¹) * ∑ i : Fin p.n, p.powerTerm t (fun j => x j / p.T) i =
      ((p.T : EReal)⁻¹) * ∑ i : Fin p.n, q.powerTerm t x i
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact hpower_backward ht hx
  -- The original objective is finite exactly on positive rates.
  have hpobjective_coe :
      ∀ {r : Fin p.n → ℝ},
        p.positiveRates r →
        p.objective r = (((∑ i : Fin p.n, Real.log (r i) : ℝ)) : EReal) := by
    intro r hr
    unfold TimeAllocationPowerMaximization.objective
    split_ifs with h
    · simpa using hsum_coe (fun i : Fin p.n => Real.log (r i))
    · exact False.elim (h hr)
  have hqobjective_coe :
      ∀ x : Fin p.n → ℝ,
        q.objective x = (((-∑ i : Fin p.n, Real.log (x i) : ℝ)) : EReal) := by
    intro x
    simp [q, ConvexReformulatedProgram.objective, hnegsum_coe]
  -- Rewriting each logarithm by `log (T * r_i)` produces the constant additive shift.
  have hobjective_forward :
      ∀ r : Fin p.n → ℝ,
        p.positiveRates r →
          q.objective (fun i => p.T * r i) =
            -p.objective r - logScaleShift p.n p.T := by
    intro r hr
    rw [hqobjective_coe, hpobjective_coe hr, hshift_coe]
    apply congrArg (fun z : ℝ => (z : EReal))
    calc
      (-∑ i : Fin p.n, Real.log (p.T * r i) : ℝ)
          = -(∑ i : Fin p.n, (Real.log p.T + Real.log (r i))) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              rw [Real.log_mul p.T_pos.ne' (ne_of_gt (hr i))]
      _ = -(∑ i : Fin p.n, Real.log (r i)) - ∑ i : Fin p.n, Real.log p.T := by
        rw [Finset.sum_add_distrib]
        ring
  -- Dividing by `T` converts the convex objective back to the original logarithmic sum.
  have hobjective_backward :
      ∀ x : Fin p.n → ℝ,
        q.positiveVariables x →
          p.objective (fun i => x i / p.T) =
            -q.objective x - logScaleShift p.n p.T := by
    intro x hx
    rw [hpobjective_coe (hpositive_unscaled hx), hqobjective_coe, hshift_coe]
    apply congrArg (fun z : ℝ => (z : EReal))
    calc
      (∑ i : Fin p.n, Real.log (x i / p.T) : ℝ)
          = ∑ i : Fin p.n, (Real.log (x i) - Real.log p.T) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Real.log_div (ne_of_gt (hx i)) p.T_pos.ne']
      _ = -(-∑ i : Fin p.n, Real.log (x i) : ℝ) - ∑ i : Fin p.n, Real.log p.T := by
        rw [Finset.sum_sub_distrib]
        ring
  -- Feasibility transport is now a direct rewrite of the power, time, and positivity constraints.
  have hfeasible_forward :
      ∀ r t : Fin p.n → ℝ,
        q.feasible (fun i => p.T * r i) t ↔
          p.feasible r t ∧ p.positiveRates r := by
    intro r t
    constructor
    · intro hqf
      rcases hqf with ⟨hqpow, hqtime, hqnonneg, hqpos⟩
      have hr : p.positiveRates r := by
        intro i
        have hdiv : 0 < (p.T * r i) / p.T := by
          exact div_pos (hqpos i) p.T_pos
        have hcancel : (p.T * r i) / p.T = r i := by
          field_simp [p.T_pos.ne']
        simpa [hcancel] using hdiv
      refine ⟨?_, hr⟩
      refine ⟨?_, hqtime, hqnonneg⟩
      simpa [q, htotal_forward hqnonneg hr] using hqpow
    · intro hp
      rcases hp with ⟨hpfeas, hr⟩
      rcases hpfeas with ⟨hppow, hptime, hpnonneg⟩
      refine ⟨?_, hptime, hpnonneg, hpositive_scaled hr⟩
      simpa [q, htotal_forward hpnonneg hr] using hppow
  have hfeasible_backward :
      ∀ x t : Fin p.n → ℝ,
        p.feasible (fun i => x i / p.T) t ∧
            p.positiveRates (fun i => x i / p.T) ↔
          q.feasible x t := by
    intro x t
    constructor
    · intro hp
      rcases hp with ⟨hpfeas, hr⟩
      rcases hpfeas with ⟨hppow, hptime, hpnonneg⟩
      have hx : q.positiveVariables x := by
        intro i
        have hmul : 0 < p.T * (x i / p.T) := by
          exact mul_pos p.T_pos (hr i)
        have hcancel : p.T * (x i / p.T) = x i := by
          field_simp [p.T_pos.ne']
        simpa [q, hcancel] using hmul
      refine ⟨?_, hptime, hpnonneg, hx⟩
      simpa [q, htotal_backward hpnonneg hx] using hppow
    · intro hqf
      rcases hqf with ⟨hqpow, hqtime, hqnonneg, hqpos⟩
      refine ⟨?_, hpositive_unscaled hqpos⟩
      refine ⟨?_, hqtime, hqnonneg⟩
      simpa [q, htotal_backward hqnonneg hqpos] using hqpow
  refine ⟨q, rfl, ?_⟩
  refine ⟨?_, rfl, rfl, rfl, hfeasible_forward, hfeasible_backward,
    hobjective_forward, hobjective_backward, ?_, ?_⟩
  · intro i
    rfl
  · intro v
    constructor
    · intro hv
      rcases hv with ⟨r, t, hpfeas, hr, hobj⟩
      refine ⟨(fun i => p.T * r i), t, ?_, ?_⟩
      · exact (hfeasible_forward r t).2 ⟨hpfeas, hr⟩
      · calc
          q.objective (fun i => p.T * r i)
              = -p.objective r - logScaleShift p.n p.T := hobjective_forward r hr
          _ = -v - logScaleShift p.n p.T := by simpa [hobj]
    · intro hv
      rcases hv with ⟨x, t, hqfeas, hobj⟩
      have hback := (hfeasible_backward x t).2 hqfeas
      rcases hback with ⟨hpfeas, hr⟩
      have hqreal :
          q.objective x = (((-∑ i : Fin p.n, Real.log (x i) : ℝ)) : EReal) := hqobjective_coe x
      have hv' :
          v = (((-(-∑ i : Fin p.n, Real.log (x i) : ℝ) -
              ∑ i : Fin p.n, Real.log p.T : ℝ)) : EReal) := by
        cases v with
        | top =>
            have : False := by
              simpa [hqreal, hshift_coe] using hobj
            exact False.elim this
        | bot =>
            have : False := by
              have htop : (⊤ : EReal) - logScaleShift p.n p.T = ⊤ := by
                rw [hshift_coe]
                exact EReal.top_sub_coe (∑ i : Fin p.n, Real.log p.T)
              have hobj' : q.objective x = (⊤ : EReal) := by
                simpa [htop] using hobj
              simp [hqreal] at hobj'
            exact False.elim this
        | coe a =>
            have hreal :
                (-∑ i : Fin p.n, Real.log (x i) : ℝ) =
                  -a - ∑ i : Fin p.n, Real.log p.T := by
              exact EReal.coe_eq_coe_iff.mp (by simpa [hqreal, hshift_coe] using hobj)
            apply congrArg (fun z : ℝ => (z : EReal))
            linarith
      refine ⟨(fun i => x i / p.T), t, hpfeas, hr, ?_⟩
      calc
        p.objective (fun i => x i / p.T)
            = (((-(-∑ i : Fin p.n, Real.log (x i) : ℝ) -
                ∑ i : Fin p.n, Real.log p.T : ℝ)) : EReal) := by
                  simpa [hqobjective_coe, hshift_coe] using
                    hobjective_backward x hqfeas.2.2.2
        _ = v := by
          simpa using hv'.symm
  · constructor
    · intro hp
      rcases hp with ⟨r, t, hpfeas, hr, hopt⟩
      refine ⟨(fun i => p.T * r i), t, ?_, ?_⟩
      · exact (hfeasible_forward r t).2 ⟨hpfeas, hr⟩
      · intro x' t' hqfeas'
        have hback' := (hfeasible_backward x' t').2 hqfeas'
        rcases hback' with ⟨hpfeas', hr'⟩
        have hpineq : p.objective (fun i => x' i / p.T) ≤ p.objective r := by
          exact hopt (fun i => x' i / p.T) t' ⟨hpfeas', hr'⟩
        have hpineq_real :
            (∑ i : Fin p.n, Real.log (x' i / p.T) : ℝ) ≤
              ∑ i : Fin p.n, Real.log (r i) := by
          exact EReal.coe_le_coe_iff.mp (by
            simpa [hpobjective_coe hr', hpobjective_coe hr] using hpineq)
        have hqineq_real :
            (-∑ i : Fin p.n, Real.log (p.T * r i) : ℝ) ≤
              -∑ i : Fin p.n, Real.log (x' i) := by
          have hleft :
              (-∑ i : Fin p.n, Real.log (p.T * r i) : ℝ) =
                -(∑ i : Fin p.n, Real.log (r i)) - ∑ i : Fin p.n, Real.log p.T := by
            calc
              (-∑ i : Fin p.n, Real.log (p.T * r i) : ℝ)
                  = -(∑ i : Fin p.n, (Real.log p.T + Real.log (r i))) := by
                      congr 1
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [Real.log_mul p.T_pos.ne' (ne_of_gt (hr i))]
              _ = -(∑ i : Fin p.n, Real.log (r i)) - ∑ i : Fin p.n, Real.log p.T := by
                rw [Finset.sum_add_distrib]
                ring
          have hright :
              (-∑ i : Fin p.n, Real.log (x' i) : ℝ) =
                -(∑ i : Fin p.n, Real.log (x' i / p.T)) - ∑ i : Fin p.n, Real.log p.T := by
            have hcalc :
                (∑ i : Fin p.n, Real.log (x' i / p.T) : ℝ) =
                  -(-∑ i : Fin p.n, Real.log (x' i) : ℝ) -
                    ∑ i : Fin p.n, Real.log p.T := by
              calc
                (∑ i : Fin p.n, Real.log (x' i / p.T) : ℝ)
                    = ∑ i : Fin p.n, (Real.log (x' i) - Real.log p.T) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        rw [Real.log_div (ne_of_gt (hqfeas'.2.2.2 i)) p.T_pos.ne']
                _ = -(-∑ i : Fin p.n, Real.log (x' i) : ℝ) -
                      ∑ i : Fin p.n, Real.log p.T := by
                  rw [Finset.sum_sub_distrib]
                  ring
            linarith
          linarith [hpineq_real]
        rw [hqobjective_coe, hqobjective_coe]
        exact EReal.coe_le_coe_iff.mpr hqineq_real
    · intro hq
      rcases hq with ⟨x, t, hqfeas, hopt⟩
      have hback := (hfeasible_backward x t).2 hqfeas
      rcases hback with ⟨hpfeas, hr⟩
      refine ⟨(fun i => x i / p.T), t, hpfeas, hr, ?_⟩
      intro r' t' hp'
      rcases hp' with ⟨hpfeas', hr'⟩
      have hqfeas' : q.feasible (fun i => p.T * r' i) t' := by
        exact (hfeasible_forward r' t').2 ⟨hpfeas', hr'⟩
      have hqineq : q.objective x ≤ q.objective (fun i => p.T * r' i) := by
        exact hopt (fun i => p.T * r' i) t' hqfeas'
      have hqineq_real :
          (-∑ i : Fin p.n, Real.log (x i) : ℝ) ≤
            -∑ i : Fin p.n, Real.log (p.T * r' i) := by
        exact EReal.coe_le_coe_iff.mp (by
          simpa [hqobjective_coe] using hqineq)
      have hpineq_real :
          (∑ i : Fin p.n, Real.log (r' i) : ℝ) ≤
            ∑ i : Fin p.n, Real.log (x i / p.T) := by
        have hleft :
            (-∑ i : Fin p.n, Real.log (x i) : ℝ) =
              -(∑ i : Fin p.n, Real.log (x i / p.T)) - ∑ i : Fin p.n, Real.log p.T := by
          have hcalc :
              (∑ i : Fin p.n, Real.log (x i / p.T) : ℝ) =
                -(-∑ i : Fin p.n, Real.log (x i) : ℝ) -
                  ∑ i : Fin p.n, Real.log p.T := by
            calc
              (∑ i : Fin p.n, Real.log (x i / p.T) : ℝ)
                  = ∑ i : Fin p.n, (Real.log (x i) - Real.log p.T) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [Real.log_div (ne_of_gt (hqfeas.2.2.2 i)) p.T_pos.ne']
              _ = -(-∑ i : Fin p.n, Real.log (x i) : ℝ) -
                    ∑ i : Fin p.n, Real.log p.T := by
                rw [Finset.sum_sub_distrib]
                ring
          linarith
        have hright :
            (-∑ i : Fin p.n, Real.log (p.T * r' i) : ℝ) =
              -(∑ i : Fin p.n, Real.log (r' i)) - ∑ i : Fin p.n, Real.log p.T := by
          calc
            (-∑ i : Fin p.n, Real.log (p.T * r' i) : ℝ)
                = -(∑ i : Fin p.n, (Real.log p.T + Real.log (r' i))) := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [Real.log_mul p.T_pos.ne' (ne_of_gt (hr' i))]
            _ = -(∑ i : Fin p.n, Real.log (r' i)) - ∑ i : Fin p.n, Real.log p.T := by
              rw [Finset.sum_add_distrib]
              ring
        linarith [hqineq_real]
      rw [hpobjective_coe hr', hpobjective_coe hr]
      exact EReal.coe_le_coe_iff.mpr hpineq_real

/-
Let n ∈ ℕ, let aᵢ > 0 for i = 1, ..., n, and let b > 0, T > 0, and P^{max}∈ℝ. Consider the convex
optimization problem convex reformulated program. Prove also that the objective - \sum_{i = 1}^n log
xᵢ is convex and that the constraint function (t, x) mapsto (1)/(T)\sum_{i = 1}^n aᵢ(tᵢ e^{b
xᵢ/tᵢ} - tᵢ) is convex on the domain tᵢ ≥ 0, xᵢ ≥ 0, so the reformulated problem is a convex
optimization problem. The final feasible set uses xᵢ > 0 for the logarithmic objective and the
time-allocation equality; the perspective power term is evaluated through its lower-semicontinuous
closure at tᵢ = 0, so no division by zero occurs.
-/
/-- A finite sum of real numbers coerces to `EReal` termwise. -/
lemma ereal_fin_sum_coe {n : ℕ} (f : Fin n → ℝ) :
    (∑ i : Fin n, (f i : EReal)) = (((∑ i : Fin n, f i : ℝ)) : EReal) := by
  -- The coercion commutes with finite sums by induction on the index type.
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Fin.sum_univ_succ, ih]

/-- Negating a finite `EReal` sum of real coercions is the same as coercing the negated real sum. -/
lemma ereal_neg_fin_sum_coe {n : ℕ} (f : Fin n → ℝ) :
    -(∑ i : Fin n, (f i : EReal)) = (((-∑ i : Fin n, f i : ℝ)) : EReal) := by
  -- First collapse the sum inside `EReal`, then move the negation back to `ℝ`.
  calc
    -(∑ i : Fin n, (f i : EReal)) = -((((∑ i : Fin n, f i : ℝ)) : EReal)) := by
      rw [ereal_fin_sum_coe]
    _ = (((-∑ i : Fin n, f i : ℝ)) : EReal) := by
      simp

/-- The negative logarithmic objective is convex on the positive orthant. -/
lemma convexOn_negLogSum_positiveOrthant (n : ℕ) :
    ConvexOn ℝ
      { x : Fin n → ℝ | ∀ i, 0 < x i }
      (fun x : Fin n → ℝ => -(∑ i, Real.log (x i))) := by
  classical
  -- We rewrite the orthant as a product of one-dimensional positive intervals.
  have hs : Convex ℝ ({ x : Fin n → ℝ | ∀ i, 0 < x i }) := by
    have hs' : Convex ℝ (Set.univ.pi fun _ : Fin n => Set.Ioi (0 : ℝ)) :=
      convex_pi (𝕜 := ℝ) (s := Set.univ) (t := fun _ : Fin n => Set.Ioi (0 : ℝ))
        (fun (_ : Fin n) _ => convex_Ioi (0 : ℝ))
    convert hs' using 1
    ext x
    simp [Set.mem_pi]
  -- Each coordinate contribution `x ↦ -log (x i)` is convex after composing with the projection.
  have hcoord :
      ∀ i : Fin n,
        ConvexOn ℝ
          { x : Fin n → ℝ | ∀ j, 0 < x j }
          (fun x : Fin n → ℝ => -Real.log (x i)) := by
    intro i
    let πi : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (i := i)
    have hbase :
        ConvexOn ℝ (πi ⁻¹' Set.Ioi (0 : ℝ)) (fun x : Fin n → ℝ => -Real.log (x i)) := by
      simpa [πi, Function.comp] using
        (strictConcaveOn_log_Ioi.concaveOn.neg.comp_linearMap πi)
    exact hbase.subset (by intro x hx; exact hx i) hs
  -- Summing the coordinatewise convex functions preserves convexity.
  have hsum :
      ∀ t : Finset (Fin n),
        ConvexOn ℝ
          { x : Fin n → ℝ | ∀ j, 0 < x j }
          (fun x : Fin n → ℝ => -(t.sum fun i => Real.log (x i))) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simpa using (convexOn_const (𝕜 := ℝ) (β := ℝ) 0 hs)
    · intro a t ha ht
      have hadd := (hcoord a).add ht
      simpa [Finset.sum_insert ha, add_assoc, add_comm, add_left_comm, neg_add] using hadd
  simpa using hsum Finset.univ

/-- At `(t, x) = (0, 0)`, the exponential perspective closure equals `0`. -/
lemma perspectiveClosure_exponential_zero_zero_eq_zero (a c : ℝ)
    (ha : 0 < a) (hc : 0 < c) :
    perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) 0 0 = 0 := by
  let g : ℝ × ℝ → EReal :=
    fun p => ((p.1 : EReal) * ((a : EReal) * (EReal.exp (c * (p.2 / p.1)) - 1)))
  -- Route correction: instead of trying to show full convergence at `(0, 0)`, we bracket the liminf
  -- between a uniform lower bound `-a t` and the pathwise value `0` along `(t, 0)`.
  have hlower : 0 ≤ Filter.liminf g (((𝓝[>] (0 : ℝ)) ×ˢ (𝓝 (0 : ℝ)))) := by
    -- Every value sits above `-a * t`, and that lower barrier tends to `0`.
    rw [le_liminf_iff]
    intro y hy
    have hpos : ∀ᶠ p : ℝ × ℝ in (((𝓝[>] (0 : ℝ)) ×ˢ (𝓝 (0 : ℝ)))), 0 < p.1 :=
      tendsto_fst.eventually (show ∀ᶠ q : ℝ in 𝓝[>] (0 : ℝ), 0 < q from self_mem_nhdsWithin)
    cases y with
    | top =>
        exact False.elim (not_lt_of_ge le_top hy)
    | bot =>
        filter_upwards [hpos] with p hp1
        simpa [g, positive_branch_exponential_perspective_eq_real] using
          (EReal.bot_lt_coe (p.1 * (a * (Real.exp (c * (p.2 / p.1)) - 1))))
    | coe r =>
        have hr : r < 0 := by
          simpa using hy
        have hneg : 0 < -r := by
          linarith
        have hsmall : ∀ᶠ q : ℝ in 𝓝[>] (0 : ℝ), q < (-r) / a :=
          Filter.Eventually.filter_mono
            (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
            (Iio_mem_nhds (show (0 : ℝ) < (-r) / a by exact div_pos hneg ha))
        have hlt :
            ∀ᶠ p : ℝ × ℝ in (((𝓝[>] (0 : ℝ)) ×ˢ (𝓝 (0 : ℝ)))), p.1 < (-r) / a :=
          tendsto_fst.eventually hsmall
        filter_upwards [hlt, hpos] with p hp hp1
        have hry : r < -(a * p.1) := by
          have hmul : a * p.1 < a * ((-r) / a) := mul_lt_mul_of_pos_left hp ha
          have hcancel : a * ((-r) / a) = -r := by
            field_simp [ha.ne']
          linarith
        have haux : -(a * p.1) ≤ p.1 * (a * (Real.exp (c * (p.2 / p.1)) - 1)) := by
          calc
            -(a * p.1) = p.1 * (a * (-1 : ℝ)) := by
              ring
            _ ≤ p.1 * (a * (Real.exp (c * (p.2 / p.1)) - 1)) := by
              gcongr
              nlinarith [Real.exp_nonneg (c * (p.2 / p.1))]
        have hrealE :
            ((r : ℝ) : EReal) <
              (((p.1 * (a * (Real.exp (c * (p.2 / p.1)) - 1))) : ℝ) : EReal) := by
          exact EReal.coe_lt_coe_iff.2 (lt_of_lt_of_le hry haux)
        have hEq := positive_branch_exponential_perspective_eq_real a c p.1 p.2
        exact lt_of_lt_of_eq hrealE (by simpa [g] using hEq.symm)
  have hupper : Filter.liminf g (((𝓝[>] (0 : ℝ)) ×ˢ (𝓝 (0 : ℝ)))) ≤ 0 := by
    -- Along the path `(t, 0)`, the perspective term is exactly `0`, so the liminf cannot exceed `0`.
    apply Filter.liminf_le_of_frequently_le'
    have hzero : ∃ᶠ p : ℝ × ℝ in (((𝓝[>] (0 : ℝ)) ×ˢ (𝓝 (0 : ℝ)))), p.2 = 0 := by
      have h :
          (∃ᶠ p : ℝ × ℝ in (((𝓝[>] (0 : ℝ)) ×ˢ (𝓝 (0 : ℝ)))), True ∧ p.2 = 0) ↔
            (∃ᶠ a : ℝ in (𝓝[>] (0 : ℝ)), True) ∧
              ∃ᶠ b : ℝ in (𝓝 (0 : ℝ)), b = 0 := by
        simpa using
          (Filter.frequently_prod_and (f := (𝓝[>] (0 : ℝ))) (g := (𝓝 (0 : ℝ)))
            (p := fun _ : ℝ => True) (q := fun y : ℝ => y = 0))
      have h1 : ∃ᶠ a : ℝ in (𝓝[>] (0 : ℝ)), True := Frequently.of_forall (fun _ => trivial)
      have h2 : ∃ᶠ b : ℝ in (𝓝 (0 : ℝ)), b = 0 := by
        have h0 : ∃ᶠ b : ℝ in (pure (0 : ℝ) : Filter ℝ), b = 0 := by
          rw [Filter.frequently_iff]
          simp
        exact h0.filter_mono (pure_le_nhds (0 : ℝ))
      exact (h.mpr ⟨h1, h2⟩).mono fun _ hp => hp.2
    exact hzero.mono fun p hp => by
      have hg : g p =
          ((p.1 : EReal) * ((a : EReal) * (EReal.exp (c * (0 / p.1)) - 1))) := by
        simpa [g, hp]
      rw [hg]
      have hEq :
          ((p.1 : EReal) * ((a : EReal) * (EReal.exp (c * (0 / p.1)) - 1))) =
            (((p.1 * (a * (Real.exp (c * (0 / p.1)) - 1))) : ℝ) : EReal) :=
        positive_branch_exponential_perspective_eq_real a c p.1 0
      rw [hEq]
      simp
  rw [perspectiveClosure]
  simp [g]
  exact le_antisymm hupper hlower

/-- On the nonnegative domain, the exponential perspective closure has the expected closed form. -/
lemma perspectiveClosure_exponential_nonneg_eq (a c t x : ℝ)
    (ha : 0 < a) (hc : 0 < c) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) t x =
      if t = 0 then
        if x = 0 then 0 else ⊤
      else
        ((t * (a * (Real.exp (c * (x / t)) - 1))) : EReal) := by
  -- We separate the zero-time branches from the genuine positive-time branch.
  by_cases ht0 : t = 0
  · subst ht0
    by_cases hx0 : x = 0
    · subst hx0
      simp [perspectiveClosure_exponential_zero_zero_eq_zero, ha, hc]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      simp [perspectiveClosure_exponential_zero_eq_top, ha, hc, hxpos, hx0]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    simp [perspectiveClosure, htpos, ht0]
    exact positive_branch_exponential_perspective_eq_real a c t x

/-- On the positive-positive branch, the exponential perspective term satisfies Jensen's inequality. -/
lemma exponentialPerspective_positive_positive
    (a c θ t x t' x' : ℝ) (ha : 0 < a)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ht : 0 < t) (ht' : 0 < t') :
    let s := θ * t + (1 - θ) * t'
    s * (a * (Real.exp (c * ((θ * x + (1 - θ) * x') / s)) - 1)) ≤
      θ * (t * (a * (Real.exp (c * (x / t)) - 1))) +
        (1 - θ) * (t' * (a * (Real.exp (c * (x' / t')) - 1))) := by
  -- We normalize by the combined time `s` and apply convexity of `exp` to the mixed exponent.
  dsimp
  let s := θ * t + (1 - θ) * t'
  have htheta : 0 ≤ 1 - θ := by
    linarith
  have hs : 0 < s := by
    by_cases hθ : θ = 0
    · dsimp [s]
      simp [hθ, ht']
    · have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθ)
      dsimp [s]
      exact add_pos_of_pos_of_nonneg (mul_pos hθpos ht) (mul_nonneg htheta ht'.le)
  have hlam0 : 0 ≤ (θ * t) / s := by
    positivity
  have hmu0 : 0 ≤ ((1 - θ) * t') / s := by
    positivity
  have hsum : (θ * t) / s + ((1 - θ) * t') / s = 1 := by
    field_simp [s, hs.ne']
    ring
  have hexp :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) hlam0 hmu0 hsum
        (x := c * (x / t)) (y := c * (x' / t'))
  have harg :
      ((θ * t) / s) * (c * (x / t)) + (((1 - θ) * t') / s) * (c * (x' / t')) =
        c * ((θ * x + (1 - θ) * x') / s) := by
    field_simp [s, hs.ne', ht.ne', ht'.ne']
  have hexp' :
      Real.exp (c * ((θ * x + (1 - θ) * x') / s)) ≤
        ((θ * t) / s) * Real.exp (c * (x / t)) +
          (((1 - θ) * t') / s) * Real.exp (c * (x' / t')) := by
    simpa [smul_eq_mul, harg, add_assoc, add_comm, add_left_comm] using hexp
  have hmul := mul_le_mul_of_nonneg_left hexp' (by positivity : 0 ≤ s * a)
  have hleft :
      s * (a * (Real.exp (c * ((θ * x + (1 - θ) * x') / s)) - 1)) =
        s * a * Real.exp (c * ((θ * x + (1 - θ) * x') / s)) - s * a := by
    ring
  have hright :
      θ * (t * (a * (Real.exp (c * (x / t)) - 1))) +
          (1 - θ) * (t' * (a * (Real.exp (c * (x' / t')) - 1))) =
        s * a *
            ((((θ * t) / s) * Real.exp (c * (x / t))) +
              (((1 - θ) * t') / s) * Real.exp (c * (x' / t'))) -
          s * a := by
    field_simp [s, hs.ne']
    ring
  rw [hleft, hright]
  linarith

/-- Positive scaling factors out of the real positive-branch exponential perspective term. -/
lemma exponentialPerspective_positive_scale (a c l t x : ℝ)
    (hl : 0 < l) (ht : 0 < t) :
    (l * t) * (a * (Real.exp (c * ((l * x) / (l * t))) - 1)) =
      l * (t * (a * (Real.exp (c * (x / t)) - 1))) := by
  -- The quotient is invariant under positive scaling, so the whole term is positively homogeneous.
  field_simp [div_eq_mul_inv, hl.ne', ht.ne']

/-- On the nonnegative domain, the closed exponential perspective never drops below `0`. -/
lemma perspectiveClosure_exponential_nonneg_nonneg
    (a c t x : ℝ) (ha : 0 < a) (hc : 0 < c) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) t x := by
  -- The closed form is either `0`, `⊤`, or the nonnegative real positive-branch expression.
  rw [perspectiveClosure_exponential_nonneg_eq a c t x ha hc ht hx]
  by_cases ht0 : t = 0
  · simp [ht0]
    split_ifs <;> simp
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    simp [ht0]
    apply EReal.coe_nonneg.2
    have harg_nonneg : 0 ≤ c * (x / t) := by positivity
    have hexp_nonneg : 0 ≤ Real.exp (c * (x / t)) - 1 := by
      nlinarith [Real.one_le_exp_iff.2 harg_nonneg]
    positivity

/-- On the nonnegative domain, the closed exponential perspective is positively homogeneous. -/
lemma perspectiveClosure_exponential_nonneg_homogeneous
    (a c l t x : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hl : 0 ≤ l) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) (l * t) (l * x) =
      ((l : EReal) *
        perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) t x) := by
  -- Route correction: the mixed zero-time branches are handled by factoring out the convex weight.
  by_cases hl0 : l = 0
  · -- If the scaling factor vanishes, both coordinates collapse to `(0, 0)`.
    subst hl0
    simpa using (perspectiveClosure_exponential_zero_zero_eq_zero a c ha hc)
  · have hlpos : 0 < l := lt_of_le_of_ne hl (Ne.symm hl0)
    by_cases ht0 : t = 0
    · -- At zero time, the closure is either `0` at `x = 0` or `⊤` for `x > 0`.
      subst ht0
      by_cases hx0 : x = 0
      · subst hx0
        calc
          perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) (l * 0) (l * 0) = 0 := by
            simpa [mul_zero] using perspectiveClosure_exponential_zero_zero_eq_zero a c ha hc
          _ = ((l : EReal) *
                perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) 0 0) := by
                rw [perspectiveClosure_exponential_zero_zero_eq_zero a c ha hc]
                simp
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        have hlxpos : 0 < l * x := mul_pos hlpos hxpos
        rw [show l * (0 : ℝ) = 0 by ring]
        rw [perspectiveClosure_exponential_zero_eq_top a c (l * x) ha hc hlxpos]
        rw [perspectiveClosure_exponential_zero_eq_top a c x ha hc hxpos]
        rw [EReal.mul_top_of_pos (EReal.coe_pos.2 hlpos)]
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hltpos : 0 < l * t := mul_pos hlpos htpos
      -- On the positive branch, both sides are finite and reduce to the real homogeneity identity.
      rw [perspectiveClosure_exponential_nonneg_eq a c (l * t) (l * x) ha hc
        (by positivity) (by positivity)]
      rw [perspectiveClosure_exponential_nonneg_eq a c t x ha hc ht hx]
      simp [hltpos.ne', ht0]
      rw [← EReal.coe_mul]
      apply congrArg (fun r : ℝ => (r : EReal))
      simpa using exponentialPerspective_positive_scale a c l t x hlpos htpos

/-- The closed exponential perspective is convex on the nonnegative `(t, x)` domain. -/
lemma exponentialPerspective_nonneg_convex
    (a c θ t x t' x' : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (ht : 0 ≤ t) (hx : 0 ≤ x) (ht' : 0 ≤ t') (hx' : 0 ≤ x') :
    perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1))
        (θ * t + (1 - θ) * t') (θ * x + (1 - θ) * x') ≤
      ((θ : EReal) *
          perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) t x +
        ((1 - θ : ℝ) : EReal) *
          perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) t' x') := by
  -- Route correction: instead of forcing a direct Jensen proof in every branch, we reduce the
  -- mixed zero-time cases to positive homogeneity and reserve Jensen only for `t, t' > 0`.
  by_cases hθ : θ = 0
  · -- Degenerate weight `θ = 0` leaves only the second endpoint.
    subst hθ
    simp [perspectiveClosure_exponential_nonneg_eq, ha, hc, ht, hx, ht', hx']
  by_cases hθeq1 : θ = 1
  · -- Degenerate weight `θ = 1` leaves only the first endpoint.
    subst hθeq1
    simp [perspectiveClosure_exponential_nonneg_eq, ha, hc, ht, hx, ht', hx']
  have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθ)
  have hθlt1 : θ < 1 := lt_of_le_of_ne hθ1 hθeq1
  have hone_sub_pos : 0 < 1 - θ := sub_pos.mpr hθlt1
  have hone_sub_nonneg : 0 ≤ 1 - θ := by linarith
  by_cases ht0 : t = 0
  · subst ht0
    by_cases ht'0 : t' = 0
    · subst ht'0
      -- With both times zero, the right-hand side is `⊤` unless both carried variables vanish.
      by_cases hx0 : x = 0
      · subst hx0
        by_cases hx'0 : x' = 0
        · subst hx'0
          simp [perspectiveClosure_exponential_zero_zero_eq_zero, ha, hc]
        · have hx'pos : 0 < x' := lt_of_le_of_ne hx' (Ne.symm hx'0)
          have hright :
              ((θ : EReal) *
                  perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) 0 0 +
                ((1 - θ : ℝ) : EReal) *
                  perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) 0 x') = ⊤ := by
            rw [perspectiveClosure_exponential_zero_zero_eq_zero a c ha hc]
            rw [perspectiveClosure_exponential_zero_eq_top a c x' ha hc hx'pos]
            rw [EReal.mul_top_of_pos (EReal.coe_pos.2 hone_sub_pos)]
            simpa using EReal.add_top_of_ne_bot
              (ne_of_gt <|
                lt_of_lt_of_le EReal.bot_lt_zero <|
                  mul_nonneg (EReal.coe_nonneg.2 hθ0)
                    (perspectiveClosure_exponential_nonneg_nonneg a c 0 0 ha hc (by simp) (by simp)))
          rw [hright]
          exact le_top
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        have hright :
            ((θ : EReal) *
                perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) 0 x +
              ((1 - θ : ℝ) : EReal) *
                perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) 0 x') = ⊤ := by
          rw [perspectiveClosure_exponential_zero_eq_top a c x ha hc hxpos]
          rw [EReal.mul_top_of_pos (EReal.coe_pos.2 hθpos)]
          simpa using EReal.top_add_of_ne_bot
            (ne_of_gt <|
              lt_of_lt_of_le EReal.bot_lt_zero <|
                mul_nonneg (EReal.coe_nonneg.2 hone_sub_nonneg)
                  (perspectiveClosure_exponential_nonneg_nonneg a c 0 x' ha hc (by simp) hx'))
        rw [hright]
        exact le_top
    · have ht'pos : 0 < t' := lt_of_le_of_ne ht' (Ne.symm ht'0)
      by_cases hx0 : x = 0
      · subst hx0
        -- If the zero-time endpoint carries zero mass, homogeneity turns the left side into a copy
        -- of the positive-time endpoint scaled by `1 - θ`.
        calc
          perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1))
              (θ * 0 + (1 - θ) * t') (θ * 0 + (1 - θ) * x') =
              perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1))
                ((1 - θ) * t') ((1 - θ) * x') := by simp
          _ = (((1 - θ : ℝ) : EReal) *
                perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) t' x') := by
                simpa [mul_comm] using
                  perspectiveClosure_exponential_nonneg_homogeneous
                    a c (1 - θ) t' x' ha hc hone_sub_nonneg ht' hx'
          _ ≤ ((θ : EReal) *
                perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) 0 0 +
                ((1 - θ : ℝ) : EReal) *
                  perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) t' x') := by
                rw [perspectiveClosure_exponential_zero_zero_eq_zero a c ha hc]
                simp
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        -- If the zero-time endpoint carries positive mass, its weighted contribution is already `⊤`.
        have hright :
            ((θ : EReal) *
                perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) 0 x +
              ((1 - θ : ℝ) : EReal) *
                perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) t' x') = ⊤ := by
          rw [perspectiveClosure_exponential_zero_eq_top a c x ha hc hxpos]
          rw [EReal.mul_top_of_pos (EReal.coe_pos.2 hθpos)]
          simpa using EReal.top_add_of_ne_bot
            (ne_of_gt <|
              lt_of_lt_of_le EReal.bot_lt_zero <|
                mul_nonneg (EReal.coe_nonneg.2 hone_sub_nonneg)
                  (perspectiveClosure_exponential_nonneg_nonneg a c t' x' ha hc ht' hx'))
        rw [hright]
        exact le_top
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    by_cases ht'0 : t' = 0
    · subst ht'0
      by_cases hx'0 : x' = 0
      · subst hx'0
        -- This is the symmetric mixed branch, now scaling the first endpoint by `θ`.
        calc
          perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1))
              (θ * t + (1 - θ) * 0) (θ * x + (1 - θ) * 0) =
              perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1))
                (θ * t) (θ * x) := by simp
          _ = ((θ : EReal) *
                perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) t x) := by
                simpa [mul_comm] using
                  perspectiveClosure_exponential_nonneg_homogeneous
                    a c θ t x ha hc hθ0 ht hx
          _ ≤ ((θ : EReal) *
                perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) t x +
                ((1 - θ : ℝ) : EReal) *
                  perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) 0 0) := by
                rw [perspectiveClosure_exponential_zero_zero_eq_zero a c ha hc]
                simp
      · have hx'pos : 0 < x' := lt_of_le_of_ne hx' (Ne.symm hx'0)
        have hright :
            ((θ : EReal) *
                perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) t x +
              ((1 - θ : ℝ) : EReal) *
                perspectiveClosure (fun y => (a : EReal) * (EReal.exp (c * y) - 1)) 0 x') = ⊤ := by
          rw [perspectiveClosure_exponential_zero_eq_top a c x' ha hc hx'pos]
          rw [EReal.mul_top_of_pos (EReal.coe_pos.2 hone_sub_pos)]
          simpa using EReal.add_top_of_ne_bot
            (ne_of_gt <|
              lt_of_lt_of_le EReal.bot_lt_zero <|
                mul_nonneg (EReal.coe_nonneg.2 hθ0)
                  (perspectiveClosure_exponential_nonneg_nonneg a c t x ha hc ht hx))
        rw [hright]
        exact le_top
    · have ht'pos : 0 < t' := lt_of_le_of_ne ht' (Ne.symm ht'0)
      have hspos : 0 < θ * t + (1 - θ) * t' := by
        exact add_pos (mul_pos hθpos htpos) (mul_pos hone_sub_pos ht'pos)
      -- On the strictly positive branch, the closure reduces to the ordinary perspective term and
      -- Jensen's inequality is exactly the previously proved real convexity estimate.
      rw [perspectiveClosure_exponential_nonneg_eq a c
        (θ * t + (1 - θ) * t') (θ * x + (1 - θ) * x') ha hc
        (by positivity) (by positivity)]
      rw [perspectiveClosure_exponential_nonneg_eq a c t x ha hc ht hx]
      rw [perspectiveClosure_exponential_nonneg_eq a c t' x' ha hc ht' hx']
      simp [hspos.ne', ht0, ht'0]
      exact_mod_cast
        (exponentialPerspective_positive_positive a c θ t x t' x' ha hθ0 hθ1 htpos ht'pos)

/-- A nonnegative real scalar distributes across a finite sum of nonnegative `EReal` terms. -/
lemma ereal_coe_mul_finset_sum_of_nonneg {ι : Type*}
    (s : Finset ι) (c : ℝ) (hc : 0 ≤ c) (f : ι → EReal)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ((c : EReal) * s.sum f) = s.sum (fun i => (c : EReal) * f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro hf
    simp
  · intro a s ha ih hf
    have hsum_nonneg : 0 ≤ s.sum f := by
      exact Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [EReal.left_distrib_of_nonneg (hf a (Finset.mem_insert_self a s)) hsum_nonneg]
    rw [ih]
    intro i hi
    exact hf i (Finset.mem_insert_of_mem hi)

theorem convexReformulatedProgram_isConvexOptimization
    (p : ConvexReformulatedProgram) :
    ConvexOn ℝ
      { x : Fin p.n → ℝ | ∀ i, 0 < x i }
      (fun x : Fin p.n → ℝ => -∑ i, Real.log (x i)) ∧
    (∀ x : Fin p.n → ℝ,
      p.positiveVariables x →
        p.objective x = (((-∑ i, Real.log (x i)) : ℝ) : EReal)) ∧
    let D : Set ((Fin p.n → ℝ) × (Fin p.n → ℝ)) :=
      { z | p.nonnegativeTimes z.1 ∧ ∀ i, 0 ≤ z.2 i }
    Convex ℝ D ∧
    ∀ z z' : (Fin p.n → ℝ) × (Fin p.n → ℝ), ∀ θ : ℝ,
      z ∈ D →
      z' ∈ D →
      0 ≤ θ →
      θ ≤ 1 →
      p.totalPower
          (fun i => θ * z.1 i + (1 - θ) * z'.1 i)
          (fun i => θ * z.2 i + (1 - θ) * z'.2 i) ≤
        ((θ : EReal) * p.totalPower z.1 z.2 +
          ((1 - θ : ℝ) : EReal) * p.totalPower z'.1 z'.2) ∧
    let feasibleSet : Set ((Fin p.n → ℝ) × (Fin p.n → ℝ)) :=
      { z |
        p.timeConstraint z.1 ∧
        p.nonnegativeTimes z.1 ∧
        p.positiveVariables z.2 ∧
        p.totalPower z.1 z.2 ≤ p.Pmax }
    Convex ℝ feasibleSet := by
  refine ⟨convexOn_negLogSum_positiveOrthant p.n, ?_, ?_⟩
  · -- The reformulated objective is exactly the coerced negative log-sum on positive variables.
    intro x hx
    simp [ConvexReformulatedProgram.objective, ereal_neg_fin_sum_coe]
  · -- We next isolate the nonnegative domain `D` for the power term.
    dsimp
    let D : Set ((Fin p.n → ℝ) × (Fin p.n → ℝ)) :=
      { z | p.nonnegativeTimes z.1 ∧ ∀ i, 0 ≤ z.2 i }
    have hconvexD : Convex ℝ D := by
      -- Both coordinates are coordinatewise nonnegative orthants, so convexity is pointwise.
      have htimes : Convex ℝ { t : Fin p.n → ℝ | ∀ i, 0 ≤ t i } := by
        intro x hx y hy a b ha hb hab i
        exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
      have hvars : Convex ℝ { x : Fin p.n → ℝ | ∀ i, 0 ≤ x i } := by
        intro x hx y hy a b ha hb hab i
        exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
      have hprod := Convex.prod htimes hvars
      simpa [D, ConvexReformulatedProgram.nonnegativeTimes] using hprod
    have htotalPower :
        ∀ z z' : (Fin p.n → ℝ) × (Fin p.n → ℝ), ∀ θ : ℝ,
          z ∈ D →
          z' ∈ D →
          0 ≤ θ →
          θ ≤ 1 →
          p.totalPower
              (fun i => θ * z.1 i + (1 - θ) * z'.1 i)
              (fun i => θ * z.2 i + (1 - θ) * z'.2 i) ≤
            ((θ : EReal) * p.totalPower z.1 z.2 +
              ((1 - θ : ℝ) : EReal) * p.totalPower z'.1 z'.2) := by
      intro z z' θ hz hz' hθ0 hθ1
      -- Route correction: we now prove convexity coordinatewise for each power term, sum those
      -- inequalities, and only then distribute the outer factor `T⁻¹`.
      let tmix : Fin p.n → ℝ := fun i => θ * z.1 i + (1 - θ) * z'.1 i
      let xmix : Fin p.n → ℝ := fun i => θ * z.2 i + (1 - θ) * z'.2 i
      have hcoord :
          ∀ i : Fin p.n,
            p.powerTerm tmix xmix i ≤
              ((θ : EReal) * p.powerTerm z.1 z.2 i +
                ((1 - θ : ℝ) : EReal) * p.powerTerm z'.1 z'.2 i) := by
        intro i
        -- Each coordinate is the scalar convexity inequality on the nonnegative domain.
        simpa [tmix, xmix, ConvexReformulatedProgram.powerTerm] using
          exponentialPerspective_nonneg_convex
            (p.a i) p.b θ (z.1 i) (z.2 i) (z'.1 i) (z'.2 i)
            (p.a_pos i) p.b_pos hθ0 hθ1 (hz.1 i) (hz.2 i) (hz'.1 i) (hz'.2 i)
      have hsum :
          ∑ i : Fin p.n, p.powerTerm tmix xmix i ≤
            ∑ i : Fin p.n,
              ((θ : EReal) * p.powerTerm z.1 z.2 i +
                ((1 - θ : ℝ) : EReal) * p.powerTerm z'.1 z'.2 i) := by
        -- Finite summation preserves the pointwise order.
        exact Finset.sum_le_sum fun i _ => hcoord i
      have hterm_nonneg :
          ∀ i : Fin p.n, 0 ≤ p.powerTerm z.1 z.2 i := by
        intro i
        simpa [ConvexReformulatedProgram.powerTerm] using
          perspectiveClosure_exponential_nonneg_nonneg
            (p.a i) p.b (z.1 i) (z.2 i) (p.a_pos i) p.b_pos (hz.1 i) (hz.2 i)
      have hterm_nonneg' :
          ∀ i : Fin p.n, 0 ≤ p.powerTerm z'.1 z'.2 i := by
        intro i
        simpa [ConvexReformulatedProgram.powerTerm] using
          perspectiveClosure_exponential_nonneg_nonneg
            (p.a i) p.b (z'.1 i) (z'.2 i) (p.a_pos i) p.b_pos (hz'.1 i) (hz'.2 i)
      have hsum_nonneg :
          0 ≤ ∑ i : Fin p.n, p.powerTerm z.1 z.2 i := by
        exact Finset.sum_nonneg fun i _ => hterm_nonneg i
      have hsum_nonneg' :
          0 ≤ ∑ i : Fin p.n, p.powerTerm z'.1 z'.2 i := by
        exact Finset.sum_nonneg fun i _ => hterm_nonneg' i
      have hsum_left :
          ∑ i : Fin p.n, (θ : EReal) * p.powerTerm z.1 z.2 i =
            (θ : EReal) * ∑ i : Fin p.n, p.powerTerm z.1 z.2 i := by
        simpa using
          (ereal_coe_mul_finset_sum_of_nonneg
            (Finset.univ : Finset (Fin p.n)) θ hθ0
            (fun i : Fin p.n => p.powerTerm z.1 z.2 i)
            (fun i _ => hterm_nonneg i)).symm
      have hsum_right :
          ∑ i : Fin p.n, ((1 - θ : ℝ) : EReal) * p.powerTerm z'.1 z'.2 i =
            ((1 - θ : ℝ) : EReal) * ∑ i : Fin p.n, p.powerTerm z'.1 z'.2 i := by
        simpa using
          (ereal_coe_mul_finset_sum_of_nonneg
            (Finset.univ : Finset (Fin p.n)) (1 - θ) (by linarith)
            (fun i : Fin p.n => p.powerTerm z'.1 z'.2 i)
            (fun i _ => hterm_nonneg' i)).symm
      have hweighted_nonneg :
          0 ≤ (θ : EReal) * ∑ i : Fin p.n, p.powerTerm z.1 z.2 i := by
        exact mul_nonneg (EReal.coe_nonneg.2 hθ0) hsum_nonneg
      have hweighted_nonneg' :
          0 ≤ ((1 - θ : ℝ) : EReal) * ∑ i : Fin p.n, p.powerTerm z'.1 z'.2 i := by
        exact mul_nonneg (EReal.coe_nonneg.2 (by linarith : 0 ≤ 1 - θ)) hsum_nonneg'
      have hTinv_nonneg : 0 ≤ ((p.T : EReal)⁻¹) := by
        exact EReal.inv_nonneg_of_nonneg (EReal.coe_nonneg.2 p.T_pos.le)
      have hscaled := mul_le_mul_of_nonneg_left hsum hTinv_nonneg
      -- Unfolding `totalPower` after scaling exposes the two endpoint sums with weights `θ` and `1 - θ`.
      calc
        p.totalPower tmix xmix
            = ((p.T : EReal)⁻¹) * ∑ i : Fin p.n, p.powerTerm tmix xmix i := by
              simp [ConvexReformulatedProgram.totalPower]
        _ ≤ ((p.T : EReal)⁻¹) *
              ∑ i : Fin p.n,
                ((θ : EReal) * p.powerTerm z.1 z.2 i +
                  ((1 - θ : ℝ) : EReal) * p.powerTerm z'.1 z'.2 i) := hscaled
        _ = ((p.T : EReal)⁻¹) *
              ((θ : EReal) * ∑ i : Fin p.n, p.powerTerm z.1 z.2 i +
                ((1 - θ : ℝ) : EReal) * ∑ i : Fin p.n, p.powerTerm z'.1 z'.2 i) := by
              rw [Finset.sum_add_distrib, hsum_left, hsum_right]
        _ = ((p.T : EReal)⁻¹) * ((θ : EReal) * ∑ i : Fin p.n, p.powerTerm z.1 z.2 i) +
              ((p.T : EReal)⁻¹) * (((1 - θ : ℝ) : EReal) * ∑ i : Fin p.n, p.powerTerm z'.1 z'.2 i) := by
              rw [EReal.left_distrib_of_nonneg hweighted_nonneg hweighted_nonneg']
        _ = ((θ : EReal) * p.totalPower z.1 z.2 +
              ((1 - θ : ℝ) : EReal) * p.totalPower z'.1 z'.2) := by
              rw [ConvexReformulatedProgram.totalPower, ConvexReformulatedProgram.totalPower]
              ac_rfl
    have hfeasible :
        let feasibleSet : Set ((Fin p.n → ℝ) × (Fin p.n → ℝ)) :=
          { z |
            p.timeConstraint z.1 ∧
            p.nonnegativeTimes z.1 ∧
            p.positiveVariables z.2 ∧
            p.totalPower z.1 z.2 ≤ p.Pmax }
        Convex ℝ feasibleSet := by
      -- The affine time equality, positivity constraints, and power bound are all preserved by convex combinations.
      dsimp
      intro z hz z' hz' a b ha hb hab
      rcases hz with ⟨hztime, hznonneg, hzpos, hzpow⟩
      rcases hz' with ⟨hz'time, hz'nonneg, hz'pos, hz'pow⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- The time-allocation equality is affine.
        calc
          (∑ i, (a * z.1 i + b * z'.1 i) : ℝ) =
              a * ∑ i, z.1 i + b * ∑ i, z'.1 i := by
                rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ = p.T := by
                rw [hztime, hz'time]
                calc
                  a * p.T + b * p.T = (a + b) * p.T := by ring
                  _ = p.T := by simp [hab]
      · -- Nonnegative times are preserved coordinatewise.
        intro i
        exact add_nonneg (mul_nonneg ha (hznonneg i)) (mul_nonneg hb (hz'nonneg i))
      · -- Positive variables remain positive because the coefficients form a convex combination.
        intro i
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by
            linarith [hab, ha0]
          simp [ha0, hb1, hz'pos i]
        · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          exact add_pos_of_pos_of_nonneg (mul_pos hapos (hzpos i))
            (mul_nonneg hb (hz'pos i).le)
      · -- The power constraint uses the Jensen inequality already proved on `D`.
        have hzD : z ∈ D := ⟨hznonneg, fun i => (hzpos i).le⟩
        have hz'D : z' ∈ D := ⟨hz'nonneg, fun i => (hz'pos i).le⟩
        have hbEq : b = 1 - a := by
          linarith [hab]
        have hba : 0 ≤ b := hb
        have hpower :=
          htotalPower z z' a hzD hz'D ha (by linarith [hab])
        calc
          p.totalPower (fun i => a * z.1 i + b * z'.1 i) (fun i => a * z.2 i + b * z'.2 i) ≤
              ((a : EReal) * p.totalPower z.1 z.2 +
                (b : EReal) * p.totalPower z'.1 z'.2) := by
                  simpa [hbEq] using hpower
          _ ≤ ((a : EReal) * p.Pmax + (b : EReal) * p.Pmax) := by
                gcongr
          _ = p.Pmax := by
                rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
                apply congrArg (fun r : ℝ => (r : EReal))
                calc
                  a * p.Pmax + b * p.Pmax = (a + b) * p.Pmax := by
                    ring
                  _ = p.Pmax := by
                    simp [hab]
    refine ⟨hconvexD, ?_⟩
    intro z z' θ hz hz' hθ0 hθ1
    exact ⟨htotalPower z z' θ hz hz' hθ0 hθ1, hfeasible⟩

end «problem-130»
