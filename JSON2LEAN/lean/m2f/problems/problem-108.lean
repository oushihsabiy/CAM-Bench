import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-108»
/-
For x ∈ ℝ^n and ω ∈ [0, 2π], define T(x, ω) = x₁ + x₂ cos ω + ··· + xₙ cos((n−1)ω). Let D = {x∈ℝ^n:
T(x,
ω) > 0 for all ω∈[0, 2π]}. Define f(x) = −∫_0^{2π} log T(x, ω) dω on D. Prove that f is convex on D.
-/
theorem f_convex_on_D_trigonometric_log_integral
    (n : ℕ) (hn : 0 < n) :
    ConvexOn ℝ
      {x : Fin n → ℝ | ∀ ω : ℝ, 0 ≤ ω → ω ≤ 2 * Real.pi →
        0 < ∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω)}
      (fun x =>
        -∫ ω in (0 : ℝ)..(2 * Real.pi),
          Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω))) := by
  let _ := hn
  -- The trigonometric form is affine in the vector variable.
  have htrigonometricLinear :
      ∀ (x y : Fin n → ℝ) (a b ω : ℝ),
        (∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω)) =
          a * (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω)) +
            b * (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω)) := by
    intro x y a b ω
    -- Expand the finite sum and distribute the scalar coefficients across each cosine term.
    calc
      ∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω) =
          ∑ i : Fin n,
            (a * (x i * Real.cos (((i : ℕ) : ℝ) * ω)) +
              b * (y i * Real.cos (((i : ℕ) : ℝ) * ω))) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ =
          (∑ i : Fin n, a * (x i * Real.cos (((i : ℕ) : ℝ) * ω))) +
            ∑ i : Fin n, b * (y i * Real.cos (((i : ℕ) : ℝ) * ω)) := by
        rw [Finset.sum_add_distrib]
      _ =
          a * (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω)) +
            b * (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- Positivity of the trigonometric form is preserved under convex combinations.
  have hpositiveCombination :
      ∀ {x y : Fin n → ℝ} {a b : ℝ},
        (∀ ω : ℝ, 0 ≤ ω → ω ≤ 2 * Real.pi →
          0 < ∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω)) →
        (∀ ω : ℝ, 0 ≤ ω → ω ≤ 2 * Real.pi →
          0 < ∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω)) →
        0 ≤ a → 0 ≤ b → a + b = 1 →
        ∀ ω : ℝ, 0 ≤ ω → ω ≤ 2 * Real.pi →
          0 < ∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω) := by
    intro x y a b hx hy ha hb hab ω hω0 hω2
    -- Rewrite the mixed trigonometric sum into a convex combination of positive values.
    rw [htrigonometricLinear x y a b ω]
    have hxω :
        0 < ∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω) :=
      hx ω hω0 hω2
    have hyω :
        0 < ∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω) :=
      hy ω hω0 hω2
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      subst ha0
      subst hb1
      simpa using hyω
    · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hax :
          0 < a * ∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω) :=
        mul_pos haPos hxω
      have hby :
          0 ≤ b * ∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω) :=
        mul_nonneg hb hyω.le
      exact add_pos_of_pos_of_nonneg hax hby
  -- Positivity on the closed interval makes the logarithmic integrand continuous there.
  have hlogIntervalIntegrable :
      ∀ {z : Fin n → ℝ},
        (∀ ω : ℝ, 0 ≤ ω → ω ≤ 2 * Real.pi →
          0 < ∑ i : Fin n, z i * Real.cos (((i : ℕ) : ℝ) * ω)) →
        IntervalIntegrable
          (fun ω : ℝ =>
            Real.log (∑ i : Fin n, z i * Real.cos (((i : ℕ) : ℝ) * ω)))
          MeasureTheory.volume 0 (2 * Real.pi) := by
    intro z hz
    have hsumContinuous :
        Continuous
          (fun ω : ℝ =>
            ∑ i : Fin n, z i * Real.cos (((i : ℕ) : ℝ) * ω)) := by
      refine continuous_finset_sum _ fun i _ => ?_
      fun_prop
    have hlogContinuous :
        ContinuousOn
          (fun ω : ℝ =>
            Real.log (∑ i : Fin n, z i * Real.cos (((i : ℕ) : ℝ) * ω)))
          (Set.Icc 0 (2 * Real.pi)) := by
      -- The domain hypothesis keeps the logarithm away from zero on the whole interval.
      apply ContinuousOn.log hsumContinuous.continuousOn
      intro ω hω
      exact ne_of_gt (hz ω hω.1 hω.2)
    have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    exact hlogContinuous.intervalIntegrable_of_Icc hpi
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab ω hω0 hω2
    -- The admissible domain is convex because the defining positivity inequality is convex.
    change
      0 < ∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω)
    exact hpositiveCombination hx hy ha hb hab ω hω0 hω2
  · intro x hx y hy a b ha hb hab
    -- Convert the convexity inequality to ordinary multiplication on the real codomain.
    have hcombo :
        ∀ ω : ℝ, 0 ≤ ω → ω ≤ 2 * Real.pi →
          0 < ∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω) :=
      hpositiveCombination hx hy ha hb hab
    have hxLog :
        IntervalIntegrable
          (fun ω : ℝ =>
            Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω)))
          MeasureTheory.volume 0 (2 * Real.pi) :=
      hlogIntervalIntegrable hx
    have hyLog :
        IntervalIntegrable
          (fun ω : ℝ =>
            Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω)))
          MeasureTheory.volume 0 (2 * Real.pi) :=
      hlogIntervalIntegrable hy
    have hcomboLog :
        IntervalIntegrable
          (fun ω : ℝ =>
            Real.log (∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω)))
          MeasureTheory.volume 0 (2 * Real.pi) :=
      hlogIntervalIntegrable hcombo
    have hpointwise :
        ∀ ω ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
          -Real.log (∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω)) ≤
            a * (-Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω))) +
              b * (-Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω))) := by
      intro ω hω
      have hxω :
          (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω)) ∈ Set.Ioi (0 : ℝ) :=
        hx ω hω.1 hω.2
      have hyω :
          (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω)) ∈ Set.Ioi (0 : ℝ) :=
        hy ω hω.1 hω.2
      have hlog :
          a * Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω)) +
              b * Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω)) ≤
            Real.log
              (∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω)) := by
        -- Concavity of `log` on `(0, ∞)` gives the needed pointwise inequality.
        simpa [smul_eq_mul, htrigonometricLinear x y a b ω] using
          (strictConcaveOn_log_Ioi.concaveOn.2 hxω hyω ha hb hab)
      -- Negating the concavity inequality turns it into the convexity inequality for `-log`.
      calc
        -Real.log (∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω)) ≤
            -(a * Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω)) +
              b * Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω))) := by
          exact neg_le_neg hlog
        _ =
            a * (-Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω))) +
              b * (-Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω))) := by
          ring
    have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hmono :
        ∫ ω in (0 : ℝ)..(2 * Real.pi),
            -Real.log (∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω)) ≤
          ∫ ω in (0 : ℝ)..(2 * Real.pi),
            a * (-Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω))) +
              b * (-Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω))) := by
      -- Integrate the pointwise inequality on the interval `[0, 2π]`.
      exact intervalIntegral.integral_mono_on hpi hcomboLog.neg
        ((hxLog.neg.const_mul a).add (hyLog.neg.const_mul b)) hpointwise
    -- Rewrite the integrated inequality back into the original functional.
    change
      -∫ ω in (0 : ℝ)..(2 * Real.pi),
          Real.log (∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω)) ≤
        a * (-∫ ω in (0 : ℝ)..(2 * Real.pi),
          Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω))) +
          b * (-∫ ω in (0 : ℝ)..(2 * Real.pi),
            Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω)))
    simpa [intervalIntegral.integral_neg] using
      (calc
        -∫ ω in (0 : ℝ)..(2 * Real.pi),
            Real.log (∑ i : Fin n, (a * x i + b * y i) * Real.cos (((i : ℕ) : ℝ) * ω)) ≤
          ∫ ω in (0 : ℝ)..(2 * Real.pi),
            a * (-Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω))) +
              b * (-Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω))) := by
          simpa [intervalIntegral.integral_neg] using hmono
        _ =
            a * (-∫ ω in (0 : ℝ)..(2 * Real.pi),
              Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω))) +
              b * (-∫ ω in (0 : ℝ)..(2 * Real.pi),
                Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω))) := by
          calc
            ∫ ω in (0 : ℝ)..(2 * Real.pi),
                a * (-Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω))) +
                  b * (-Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω))) =
              (∫ ω in (0 : ℝ)..(2 * Real.pi),
                  a * (-Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω)))) +
                ∫ ω in (0 : ℝ)..(2 * Real.pi),
                  b * (-Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω))) := by
              simpa using
                (intervalIntegral.integral_add
                  (f := fun ω : ℝ =>
                    a * (-Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω))))
                  (g := fun ω : ℝ =>
                    b * (-Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω))))
                  (hxLog.neg.const_mul a) (hyLog.neg.const_mul b))
            _ =
                a * (-∫ ω in (0 : ℝ)..(2 * Real.pi),
                  Real.log (∑ i : Fin n, x i * Real.cos (((i : ℕ) : ℝ) * ω))) +
                  b * (-∫ ω in (0 : ℝ)..(2 * Real.pi),
                    Real.log (∑ i : Fin n, y i * Real.cos (((i : ℕ) : ℝ) * ω))) := by
              rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
                intervalIntegral.integral_neg, intervalIntegral.integral_neg])

end «problem-108»
