import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-116»
/- [BLOCK Exercise 2.31-(b) | 49 | defn]
For a function g:ℝ^n	oℝ+∞, its convex conjugate is defined by
g*(y)=sup_{x∈ℝ^n}{yᵀ x-g(x)}, y∈ℝ^n.
For a function h:ℝ	oℝ+∞,
h*(s)=sup_{t∈ℝ}{st-h(t)}, s∈ℝ.
-/
open scoped BigOperators

def convexConjugate {n : ℕ} (g : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup {r | ∃ x : Fin n → ℝ, r = (∑ i, y i * x i) - g x}

def scalarConvexConjugate (h : ℝ → EReal) : ℝ → EReal :=
  fun s => sSup {r | ∃ t : ℝ, r = (s * t : ℝ) - h t}

/- [BLOCK Exercise 2.31-(b) | 50 | thm]
Let n ∈ ℕ. Let h:ℝ oℝ be convex and nondecreasing with dom h=ℝ, and assume h(t)=h(0) quad ext{for
all } t ≤ 0. Define f:ℝ^n oℝ by f(x)=h(‖x‖_2), where ‖x‖_2 is the Euclidean norm on ℝ^n. For g:ℝ^n
oℝ+∞, define its convex conjugate by g*(y)=sup_{x∈ℝ^n}igl(yᵀ x-g(x)igr), y∈ℝ^n. For h:ℝ oℝ, define
its convex conjugate by h*(s)=sup_{t∈ℝ}igl(st-h(t)igr), s∈ℝ. Show that the conjugate of f is
f*(y)=h*(‖y‖_2).
-/
theorem convexConjugate_radial_eq_scalarConvexConjugate_norm
    {n : ℕ} (h : ℝ → ℝ)
    (h_convex : ConvexOn ℝ Set.univ h)
    (h_monotone : Monotone h)
    (h_nonpos_const : ∀ t : ℝ, t ≤ 0 → h t = h 0) :
    convexConjugate
        (fun x : Fin n → ℝ => (h (Real.sqrt (dotProduct x x)) : EReal)) =
      fun y : Fin n → ℝ =>
        scalarConvexConjugate (fun t => (h t : EReal)) (Real.sqrt (dotProduct y y)) := by
  -- Route correction: compare the two supremum sets directly, and use the Euclidean-space
  -- norm identities on `Fin n → ℝ` instead of building a separate finite-sum theory.
  funext y
  let s : ℝ := Real.sqrt (dotProduct y y)
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hy_norm : ‖WithLp.toLp 2 y‖ = s := by
    dsimp [s]
    simpa [dotProduct, sq] using (EuclideanSpace.norm_eq (WithLp.toLp 2 y))
  have hconvex_unused := h_convex
  clear hconvex_unused
  unfold convexConjugate scalarConvexConjugate
  -- Rewrite both conjugates as suprema over explicit real-valued witnesses.
  change
    sSup {r : EReal | ∃ x : Fin n → ℝ,
      r = (((dotProduct y x) - h (Real.sqrt (dotProduct x x)) : ℝ) : EReal)} =
    sSup {r : EReal | ∃ t : ℝ, r = (((s * t) - h t : ℝ) : EReal)}
  apply le_antisymm
  · -- Every vector witness gives a scalar witness at its radius.
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, rfl⟩
    let t : ℝ := Real.sqrt (dotProduct x x)
    have hx_norm : ‖WithLp.toLp 2 x‖ = t := by
      dsimp [t]
      simpa [dotProduct, sq] using (EuclideanSpace.norm_eq (WithLp.toLp 2 x))
    -- Cauchy-Schwarz bounds the dot product by the product of the radii.
    have hxy : dotProduct y x ≤ s * t := by
      calc
        dotProduct y x = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
          simpa using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) x y)
        _ ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := real_inner_le_norm _ _
        _ = s * t := by rw [hx_norm, hy_norm, mul_comm]
    -- After subtracting the same `h t`, the scalar witness lies in the scalar supremum set.
    have hreal :
        ((((dotProduct y x) - h t : ℝ) : EReal)) ≤ ((((s * t) - h t : ℝ) : EReal)) := by
      exact_mod_cast sub_le_sub_right hxy (h t)
    simpa [t] using
      hreal.trans (le_sSup (show ((((s * t) - h t : ℝ) : EReal) ∈
        {r : EReal | ∃ t : ℝ, r = (((s * t) - h t : ℝ) : EReal)}) from ⟨t, rfl⟩))
  · -- Every scalar witness is dominated by an actual vector witness.
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨t, rfl⟩
    by_cases ht : t ≤ 0
    · -- For nonpositive `t`, the hypothesis makes `h t` constant and `x = 0` is enough.
      have hconst : h t = h 0 := h_nonpos_const t ht
      have hreal : (s * t) - h t ≤ (s * 0) - h 0 := by
        rw [hconst]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hs_nonneg ht]
      have hzero :
          ((((s * 0) - h 0 : ℝ) : EReal)) ≤
            sSup {r : EReal | ∃ x : Fin n → ℝ,
              r = (((dotProduct y x) - h (Real.sqrt (dotProduct x x)) : ℝ) : EReal)} := by
        refine le_sSup ?_
        refine ⟨0, ?_⟩
        simp [dotProduct]
      exact (show ((((s * t) - h t : ℝ) : EReal)) ≤ (((((s * 0) - h 0 : ℝ) : EReal))) by
          exact_mod_cast hreal).trans hzero
    · have h0t : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
      by_cases hy : y = 0
      · -- If `y = 0`, the scalar term is just `-h t`, still controlled by `x = 0`.
        have hs_zero : s = 0 := by
          dsimp [s]
          simp [hy, dotProduct]
        have hreal : (s * t) - h t ≤ (s * 0) - h 0 := by
          have hmono : h 0 ≤ h t := h_monotone h0t
          rw [hs_zero]
          linarith
        have hzero :
            ((((s * 0) - h 0 : ℝ) : EReal)) ≤
              sSup {r : EReal | ∃ x : Fin n → ℝ,
                r = (((dotProduct y x) - h (Real.sqrt (dotProduct x x)) : ℝ) : EReal)} := by
          refine le_sSup ?_
          refine ⟨0, ?_⟩
          simp [dotProduct]
        exact (show ((((s * t) - h t : ℝ) : EReal)) ≤ (((((s * 0) - h 0 : ℝ) : EReal))) by
            exact_mod_cast hreal).trans hzero
      · -- For `y ≠ 0` and `t ≥ 0`, take the aligned vector `x = (t / s) • y`.
        have hs_pos : 0 < s := by
          rw [← hy_norm]
          simpa using
            (norm_pos_iff.mpr (show WithLp.toLp 2 y ≠ 0 by simpa using hy))
        let x : Fin n → ℝ := (t / s) • y
        have hx_norm : ‖WithLp.toLp 2 x‖ = t := by
          calc
            ‖WithLp.toLp 2 x‖ = |t / s| * ‖WithLp.toLp 2 y‖ := by
              change ‖(t / s) • WithLp.toLp 2 y‖ = |t / s| * ‖WithLp.toLp 2 y‖
              rw [norm_smul, Real.norm_eq_abs, abs_div]
            _ = (t / s) * s := by
              rw [abs_of_nonneg (div_nonneg h0t hs_nonneg), hy_norm]
            _ = t := by
              field_simp [hs_pos.ne']
        have hx_radius : Real.sqrt (dotProduct x x) = t := by
          calc
            Real.sqrt (dotProduct x x) = ‖WithLp.toLp 2 x‖ := by
              simpa [dotProduct, sq] using (EuclideanSpace.norm_eq (WithLp.toLp 2 x)).symm
            _ = t := hx_norm
        have hxy : dotProduct y x = s * t := by
          calc
            dotProduct y x = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
              simpa using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) x y)
            _ = (t / s) * inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 y) := by
              simp [x, real_inner_smul_left]
            _ = (t / s) * (s * s) := by rw [real_inner_self_eq_norm_mul_norm, hy_norm]
            _ = s * t := by
              field_simp [hs_pos.ne']
        have hx_mem :
            ((((dotProduct y x) - h (Real.sqrt (dotProduct x x)) : ℝ) : EReal)) ≤
              sSup {r : EReal | ∃ x : Fin n → ℝ,
                r = (((dotProduct y x) - h (Real.sqrt (dotProduct x x)) : ℝ) : EReal)} := by
          refine le_sSup ?_
          exact ⟨x, rfl⟩
        simpa [hxy, hx_radius] using hx_mem

end «problem-116»
