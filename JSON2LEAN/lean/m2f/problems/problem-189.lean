import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-189»

/- [BLOCK Exercise 2.15 | 17 | defn]
A sequence (xₖ) converges Q-superlinearly to x* if xₖ → x* and
lim_k→∞ frac{‖x_k+1-x*‖}{‖x_k-x*‖}=0,
whenever the denominator is nonzero for all sufficiently large k.
-/
def QSuperlinearlyConverges {E : Type*} [NormedAddCommGroup E] (x : ℕ → E) (xStar : E) : Prop :=
  Tendsto x atTop (𝓝 xStar) ∧
    ((∀ᶠ k in atTop, x k ≠ xStar) →
      Tendsto
        (fun k => ‖x (k + 1) - xStar‖ / ‖x k - xStar‖)
        atTop
        (𝓝 0))

/- [BLOCK Exercise 2.15 | 18 | defn]
A sequence (xₖ) converges Q-quadratically to x* if there exist constants M>0 and k₀∈N such
that, for all k≥ k₀,
‖x_k+1-x*‖≤ M‖x_k-x*‖^2.
-/
def QQuadraticallyConverges {E : Type*} [NormedAddCommGroup E] (x : ℕ → E) (xStar : E) : Prop :=
  Tendsto x atTop (𝓝 xStar) ∧
    ∃ (M : ℝ) (k₀ : ℕ), 0 < M ∧ ∀ k ≥ k₀, ‖x (k + 1) - xStar‖ ≤ M * ‖x k - xStar‖ ^ 2

/-
Exercise 2.15 | 19 | thm

Let (xₖ)_{k ∈ ℕ} be the sequence defined by xₖ = 1/k!, ℕ = {1, 2, 3, …}, k! = 1 · 2 · … · k. Using
the definition lim_{k → ∞} |x_{k+1}| / |xₖ| = 0 for Q-superlinear convergence to 0, show that the
sequence xₖ = 1/k! converges Q-superlinearly.
-/
theorem factorialInverse_qsuperlinearlyConverges :
    QSuperlinearlyConverges (fun k : ℕ => ((k + 1).factorial : ℝ)⁻¹) 0 := by
  have factorialInverse_shiftedFactorial_tendstoAtTop :
      Tendsto (fun k : ℕ => (((k + 1).factorial : ℝ))) atTop atTop := by
    -- Shift the index so the standard factorial divergence theorem applies directly.
    simpa using
      (tendsto_natCast_atTop_atTop.comp
        (factorial_tendsto_atTop.comp (tendsto_add_atTop_nat 1)))
  have factorialInverse_tendsto_zero :
      Tendsto (fun k : ℕ => (((k + 1).factorial : ℝ)⁻¹)) atTop (𝓝 0) := by
    -- Once the denominator tends to `∞`, its reciprocal tends to `0`.
    exact tendsto_inv_atTop_zero.comp factorialInverse_shiftedFactorial_tendstoAtTop
  have factorialInverse_ratio_eq_one_div_shift :
      ∀ k : ℕ,
        ‖((((k + 2).factorial : ℝ)⁻¹) - 0)‖ / ‖((((k + 1).factorial : ℝ)⁻¹) - 0)‖ =
          (1 : ℝ) / (k + 2) := by
    intro k
    -- The factorial inverses are nonnegative, so the norms reduce to the underlying terms.
    rw [sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    -- Rewrite successive factorials and clear the positive denominator.
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))]
    norm_num [Nat.cast_add, Nat.add_assoc]
  refine ⟨factorialInverse_tendsto_zero, ?_⟩
  intro _
  -- The eventual nonzero hypothesis is not needed: the quotient identity holds for every `k`.
  have hratio :
      (fun k : ℕ =>
        ‖((((k + 1) + 1).factorial : ℝ)⁻¹) - 0‖ / ‖((((k + 1).factorial : ℝ)⁻¹) - 0)‖) =
        fun k : ℕ => (1 : ℝ) / (k + 2) := by
    -- Expand the quotient pointwise and replace it with the simpler shifted reciprocal sequence.
    funext k
    simpa [Nat.add_assoc] using factorialInverse_ratio_eq_one_div_shift k
  rw [hratio]
  -- A shifted reciprocal sequence converges to `0`.
  convert
    (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2) :
      Tendsto ((fun n : ℕ => ((n : ℝ)⁻¹)) ∘ fun k : ℕ => k + 2) atTop (𝓝 0)) using 1
  -- Expand the composition and normalize the casted shift.
  ext k
  simp [Function.comp, one_div, Nat.cast_add]

/-
Exercise 2.15 | 20 | thm

Let (xₖ)_{k ∈ ℕ} be the sequence defined by xₖ = 1/(k!), ℕ = {1, 2, 3, …}, k! = 1 · 2 · … · k. Using
the definition ∃ M > 0 ∃ k₀ ∈ ℕ ∀ k ≥ k₀: |x_{k+1}| ≤ M|xₖ|² for Q-quadratic convergence to 0,
determine whether it converges Q-quadratically.
-/
theorem factorialInverse_not_qquadraticallyConverges :
    ¬ QQuadraticallyConverges (fun k : ℕ => ((k + 1).factorial : ℝ)⁻¹) 0 := by
  intro hquadratic
  rcases hquadratic with ⟨_, M, k₀, hM, hbound⟩
  let k : ℕ := max k₀ (Nat.ceil M + 2)
  have hk₀ : k₀ ≤ k := le_max_left _ _
  have hkceil : Nat.ceil M + 2 ≤ k := le_max_right _ _
  have hk_large : M < (k : ℝ) - 1 := by
    -- The chosen index is at least `⌈M⌉₊ + 2`, so `k - 1` is strictly larger than `M`.
    have hceil : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
    have hkreal : ((Nat.ceil M + 2 : ℕ) : ℝ) ≤ k := by
      exact_mod_cast hkceil
    have hkreal' : (Nat.ceil M : ℝ) + 2 ≤ (k : ℝ) := by
      simpa [Nat.cast_add] using hkreal
    linarith
  have hquadraticAtK := hbound k hk₀
  have hupper :
      (((k + 1).factorial : ℝ) / (k + 2)) ≤ M := by
    -- Remove norms from the quadratic estimate at the chosen index.
    have hquadraticAtK' :
        (((k + 2).factorial : ℝ)⁻¹) ≤ M * ((((k + 1).factorial : ℝ)⁻¹) ^ 2) := by
      simpa [sub_zero, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ (((k + 2).factorial : ℝ)⁻¹) by positivity),
        abs_of_nonneg (show 0 ≤ (((k + 1).factorial : ℝ)⁻¹) by positivity)] using
        hquadraticAtK
    let a : ℝ := ((k + 1).factorial : ℝ)
    have ha0 : a ≠ 0 := by
      dsimp [a]
      exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))
    have hk2 : ((k + 2 : ℕ) : ℝ) ≠ 0 := by
      positivity
    have hmul :
        (((k + 2).factorial : ℝ)⁻¹) * a ^ 2 ≤ (M * (a⁻¹ ^ 2)) * a ^ 2 := by
      exact mul_le_mul_of_nonneg_right hquadraticAtK' (sq_nonneg a)
    have hleft : (((k + 2).factorial : ℝ)⁻¹) * a ^ 2 = a / (k + 2) := by
      -- Rewrite `(k + 2)!` as `(k + 2) * (k + 1)!` and cancel the common positive factor.
      dsimp [a]
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 1)), hk2]
      norm_num [Nat.cast_add, Nat.add_assoc]
    have hsq : (a⁻¹ ^ 2) * a ^ 2 = 1 := by
      -- The square of a nonzero number cancels the square of its inverse.
      field_simp [ha0]
    calc
      (((k + 1).factorial : ℝ) / (k + 2)) = (((k + 2).factorial : ℝ)⁻¹) * a ^ 2 := by
        simpa [a] using hleft.symm
      _ ≤ (M * (a⁻¹ ^ 2)) * a ^ 2 := hmul
      _ = M := by
        rw [mul_assoc, hsq, mul_one]
  have hlower :
      (k : ℝ) - 1 ≤ (((k + 1).factorial : ℝ) / (k + 2)) := by
    -- Compare `(k + 1)!` with `(k + 1) * k` using the basic bound `k ≤ k!`.
    have hk2 : (0 : ℝ) < k + 2 := by positivity
    have hfactorial : (k : ℝ) ≤ ((k.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.self_le_factorial k
    have hbase : (k : ℝ) - 1 ≤ ((k : ℝ) * ((k : ℝ) + 1)) / (k + 2) := by
      have : ((k : ℝ) - 1) * (k + 2) ≤ (k : ℝ) * ((k : ℝ) + 1) := by
        nlinarith
      exact (le_div_iff₀ hk2).2 <| by simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hbase' : (k : ℝ) - 1 ≤ (((k : ℝ) + 1) * k) / (k + 2) := by
      simpa [mul_comm] using hbase
    calc
      (k : ℝ) - 1 ≤ (((k : ℝ) + 1) * k) / (k + 2) := hbase'
      _ ≤ (((k : ℝ) + 1) * (k.factorial : ℝ)) / (k + 2) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactorial (by positivity : 0 ≤ (k : ℝ) + 1))
          (by positivity)
      _ = (((k + 1).factorial : ℝ) / (k + 2)) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
        norm_num [Nat.cast_add, Nat.add_assoc, mul_comm, mul_left_comm, mul_assoc]
  exact (not_lt_of_ge (le_trans hlower hupper)) hk_large

end «problem-189»
