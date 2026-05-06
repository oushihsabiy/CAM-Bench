import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-185»

/- [BLOCK Exercise 2.10 | 11 | defn]
Given weights α_1,dots,α_n ≥ 0, the weighted geometric mean on ℝ_{++}^n is the function
f(x)=prod_{k=1}^n xₖ^{α_k}.
-/
def weightedGeometricMean (n : ℕ) (α x : Fin n → ℝ) : ℝ :=
  ∏ k, Real.rpow (x k) (α k)

/-- The positive orthant in `Fin n → ℝ` is convex. -/
lemma convex_positiveOrthant (n : ℕ) :
    Convex ℝ {x : Fin n → ℝ | ∀ k, 0 < x k} := by
  -- Check convexity coordinatewise, using positivity of a convex combination in each coordinate.
  intro x hx y hy a b ha hb hab k
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1, hy k]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
    exact add_pos_of_pos_of_nonneg (mul_pos ha_pos (hx k)) (mul_nonneg hb (le_of_lt (hy k)))

/-- Nonnegative coordinates give a nonnegative weighted geometric mean. -/
lemma weightedGeometricMean_nonneg
    (n : ℕ) (α x : Fin n → ℝ)
    (hx : ∀ k, 0 ≤ x k) :
    0 ≤ weightedGeometricMean n α x := by
  -- Each factor is nonnegative because `rpow` preserves nonnegativity on nonnegative bases.
  unfold weightedGeometricMean
  exact Finset.prod_nonneg fun k _ => Real.rpow_nonneg (hx k) _

/-- The weighted geometric mean of positive coordinates is positive. -/
lemma weightedGeometricMean_pos
    (n : ℕ) (α x : Fin n → ℝ)
    (hx : ∀ k, 0 < x k) :
    0 < weightedGeometricMean n α x := by
  -- Each factor is positive on the positive orthant, so the whole finite product is positive.
  unfold weightedGeometricMean
  refine Finset.prod_pos ?_
  intro k hk
  exact Real.rpow_pos_of_pos (hx k) _

/-- Coordinatewise multiplication factors the weighted geometric mean. -/
lemma weightedGeometricMean_mul
    (n : ℕ) (α x y : Fin n → ℝ)
    (hx : ∀ k, 0 ≤ x k) (hy : ∀ k, 0 ≤ y k) :
    weightedGeometricMean n α (fun k => x k * y k) =
      weightedGeometricMean n α x * weightedGeometricMean n α y := by
  -- Rewrite each coordinate with `mul_rpow` and split the finite product.
  unfold weightedGeometricMean
  calc
    ∏ k, Real.rpow (x k * y k) (α k)
        = ∏ k, Real.rpow (x k) (α k) * Real.rpow (y k) (α k) := by
            refine Finset.prod_congr rfl ?_
            intro k hk
            simpa using (Real.mul_rpow (hx k) (hy k) (z := α k))
    _ = (∏ k, Real.rpow (x k) (α k)) * ∏ k, Real.rpow (y k) (α k) := by
          rw [Finset.prod_mul_distrib]

/-- If the nonnegative weights sum to `1`, scaling all coordinates scales the weighted
geometric mean by the same factor. -/
lemma weightedGeometricMean_smul_of_sum_eq_one
    (n : ℕ) (α x : Fin n → ℝ)
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum : ∑ k, α k = 1)
    {c : ℝ} (hc : 0 ≤ c)
    (hx : ∀ k, 0 ≤ x k) :
    weightedGeometricMean n α (fun k => c * x k) = c * weightedGeometricMean n α x := by
  -- The scalar contributes `c ^ (∑ α)`; the sum-one condition turns that factor into `c`.
  unfold weightedGeometricMean
  calc
    ∏ k, Real.rpow (c * x k) (α k)
        = ∏ k, Real.rpow c (α k) * Real.rpow (x k) (α k) := by
            refine Finset.prod_congr rfl ?_
            intro k hk
            simpa using (Real.mul_rpow hc (hx k) (z := α k))
    _ = (∏ k, Real.rpow c (α k)) * ∏ k, Real.rpow (x k) (α k) := by
          rw [Finset.prod_mul_distrib]
    _ = Real.rpow c (∑ k, α k) * ∏ k, Real.rpow (x k) (α k) := by
          have hc_sum : ∏ k, Real.rpow c (α k) = Real.rpow c (∑ k, α k) := by
            symm
            exact Real.rpow_sum_of_nonneg hc (s := Finset.univ) (f := α) fun k _ => hα_nonneg k
          rw [hc_sum]
    _ = c * ∏ k, Real.rpow (x k) (α k) := by
          simp [hα_sum]

/-- If the total nonnegative weight is zero, the weighted geometric mean is constantly `1`. -/
lemma weightedGeometricMean_eq_one_of_sum_eq_zero
    (n : ℕ) (α : Fin n → ℝ)
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum : ∑ k, α k = 0) :
    ∀ x, weightedGeometricMean n α x = 1 := by
  -- Zero total mass forces every weight to vanish, so every factor is `x_k ^ 0 = 1`.
  intro x
  have hα_zero : ∀ k, α k = 0 := by
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hα_nonneg i).mp hα_sum k (by simp)
  simp [weightedGeometricMean, hα_zero]

/-- Normalizing nonzero weights turns the weighted geometric mean into an `rpow`. -/
lemma weightedGeometricMean_eq_rpow_normalized
    (n : ℕ) (α : Fin n → ℝ) (x : Fin n → ℝ)
    (hx : ∀ k, 0 < x k) :
    ∀ s : ℝ, s = ∑ k, α k → s ≠ 0 →
      weightedGeometricMean n α x =
        (weightedGeometricMean n (fun k => α k / s) x) ^ s := by
  -- Rewrite the normalized product as a product of powered factors and collapse exponents.
  intro s hs hs_ne
  calc
    weightedGeometricMean n α x
        = ∏ k, Real.rpow (x k) (α k) := by
            rw [weightedGeometricMean]
    _ = ∏ k, Real.rpow (x k) ((α k / s) * s) := by
          refine Finset.prod_congr rfl ?_
          intro k hk
          congr 1
          field_simp [hs_ne]
    _ = ∏ k, (Real.rpow (x k) (α k / s)) ^ s := by
          refine Finset.prod_congr rfl ?_
          intro k hk
          exact Real.rpow_mul (le_of_lt (hx k)) (α k / s) s
    _ = (weightedGeometricMean n (fun k => α k / s) x) ^ s := by
          rw [weightedGeometricMean]
          exact Real.finset_prod_rpow Finset.univ
            (fun k => Real.rpow (x k) (α k / s))
            (fun k _ => Real.rpow_nonneg (le_of_lt (hx k)) _)
            s

/-- For weights summing to `1`, the weighted geometric mean is concave on the positive orthant. -/
lemma weightedGeometricMean_concaveOn_pos_of_sum_eq_one
    (n : ℕ) (α : Fin n → ℝ)
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum : ∑ k, α k = 1) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ k, 0 < x k} (weightedGeometricMean n α) := by
  refine ⟨convex_positiveOrthant n, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Step: package the coordinatewise convex combination and the AM-GM ratio variables.
  let z : Fin n → ℝ := fun k => a * x k + b * y k
  let u : Fin n → ℝ := fun k => a * x k / z k
  let v : Fin n → ℝ := fun k => b * y k / z k
  have hz_pos : ∀ k, 0 < z k := by
    intro k
    dsimp [z]
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simp [ha0, hb1, hy k]
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos ha_pos (hx k)) (mul_nonneg hb (le_of_lt (hy k)))
  have hu_nonneg : ∀ k, 0 ≤ u k := by
    intro k
    dsimp [u]
    exact div_nonneg (mul_nonneg ha (le_of_lt (hx k))) (le_of_lt (hz_pos k))
  have hv_nonneg : ∀ k, 0 ≤ v k := by
    intro k
    dsimp [v]
    exact div_nonneg (mul_nonneg hb (le_of_lt (hy k))) (le_of_lt (hz_pos k))
  have hu_amgm :
      weightedGeometricMean n α u ≤ ∑ k, α k * u k := by
    -- Apply weighted AM-GM to the normalized `x`-ratios.
    simpa [weightedGeometricMean] using Real.geom_mean_le_arith_mean_weighted
      (s := Finset.univ) α u (fun k _ => hα_nonneg k) (by simpa using hα_sum)
      (fun k _ => hu_nonneg k)
  have hv_amgm :
      weightedGeometricMean n α v ≤ ∑ k, α k * v k := by
    -- Apply weighted AM-GM to the normalized `y`-ratios.
    simpa [weightedGeometricMean] using Real.geom_mean_le_arith_mean_weighted
      (s := Finset.univ) α v (fun k _ => hα_nonneg k) (by simpa using hα_sum)
      (fun k _ => hv_nonneg k)
  have hz_nonneg : 0 ≤ weightedGeometricMean n α z :=
    weightedGeometricMean_nonneg n α z fun k => (hz_pos k).le
  have hu_mul : ∀ k, u k * z k = a * x k := by
    intro k
    have hz_ne : z k ≠ 0 := (hz_pos k).ne'
    dsimp [u]
    field_simp [hz_ne]
  have hv_mul : ∀ k, v k * z k = b * y k := by
    intro k
    have hz_ne : z k ≠ 0 := (hz_pos k).ne'
    dsimp [v]
    field_simp [hz_ne]
  have huv_one : ∀ k, u k + v k = 1 := by
    intro k
    have hz_ne : z k ≠ 0 := (hz_pos k).ne'
    calc
      u k + v k = (a * x k + b * y k) / z k := by
        dsimp [u, v]
        rw [← add_div]
      _ = z k / z k := by simp [z]
      _ = 1 := by exact div_self hz_ne
  have hx_factor :
      a * weightedGeometricMean n α x =
        weightedGeometricMean n α u * weightedGeometricMean n α z := by
    -- Factor the `x` contribution through the ratio variables and the midpoint `z`.
    rw [← weightedGeometricMean_smul_of_sum_eq_one n α x hα_nonneg hα_sum ha fun k => (hx k).le]
    have hpoint :
        (fun k => a * x k) = fun k => u k * z k := by
      ext k
      exact (hu_mul k).symm
    rw [hpoint]
    exact weightedGeometricMean_mul n α u z hu_nonneg fun k => (hz_pos k).le
  have hy_factor :
      b * weightedGeometricMean n α y =
        weightedGeometricMean n α v * weightedGeometricMean n α z := by
    -- Factor the `y` contribution through the second family of ratio variables.
    rw [← weightedGeometricMean_smul_of_sum_eq_one n α y hα_nonneg hα_sum hb fun k => (hy k).le]
    have hpoint :
        (fun k => b * y k) = fun k => v k * z k := by
      ext k
      exact (hv_mul k).symm
    rw [hpoint]
    exact weightedGeometricMean_mul n α v z hv_nonneg fun k => (hz_pos k).le
  have hx_le :
      a * weightedGeometricMean n α x ≤
        (∑ k, α k * u k) * weightedGeometricMean n α z := by
    -- Multiply the AM-GM bound for `u` by the common nonnegative factor `weightedGeometricMean z`.
    rw [hx_factor]
    exact mul_le_mul_of_nonneg_right hu_amgm hz_nonneg
  have hy_le :
      b * weightedGeometricMean n α y ≤
        (∑ k, α k * v k) * weightedGeometricMean n α z := by
    -- Multiply the AM-GM bound for `v` by the same nonnegative factor.
    rw [hy_factor]
    exact mul_le_mul_of_nonneg_right hv_amgm hz_nonneg
  have huv_sum :
      (∑ k, α k * u k) + (∑ k, α k * v k) = 1 := by
    -- The ratio families satisfy `u_k + v_k = 1`, so the weighted sums add up to `∑ α = 1`.
    calc
      (∑ k, α k * u k) + (∑ k, α k * v k)
          = ∑ k, (α k * u k + α k * v k) := by
              rw [← Finset.sum_add_distrib]
      _ = ∑ k, α k * (u k + v k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
      _ = ∑ k, α k * 1 := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [huv_one k]
      _ = 1 := by simp [hα_sum]
  have hz_eq : z = a • x + b • y := by
    -- Unfold the pointwise convex combination.
    ext k
    simp [z, smul_eq_mul]
  -- Combine the two AM-GM bounds and collapse the weighted sum to `1`.
  simpa [smul_eq_mul, hz_eq] using
    calc
      a * weightedGeometricMean n α x + b * weightedGeometricMean n α y
          ≤ (∑ k, α k * u k) * weightedGeometricMean n α z +
              (∑ k, α k * v k) * weightedGeometricMean n α z := by
                exact add_le_add hx_le hy_le
      _ = ((∑ k, α k * u k) + (∑ k, α k * v k)) * weightedGeometricMean n α z := by
            ring
      _ = weightedGeometricMean n α z := by rw [huv_sum, one_mul]

/- [BLOCK Exercise 2.10 | 12 | thm]
Let n ∈ ℕ, and let α_1,dots,α_n ∈ ℝ satisfy α_k ≥ 0 for k=1,dots,n and sum_{k=1}^n α_k ≤ 1. Define f
: ℝ_{++}^n o ℝ by f(x₁,dots,xₙ)=prod_{k=1}^n xₖ^{α_k}, where ℝ_{++}^n={x=(x₁,dots,xₙ)∈ ℝ^n | xₖ>0
ext{ for } k=1,dots,n}. Show that the weighted geometric mean f is concave on ℝ_{++}^n.
-/
theorem weightedGeometricMean_concaveOn_pos
    (n : ℕ) (α : Fin n → ℝ)
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum : ∑ k, α k ≤ 1) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ k, 0 < x k} (weightedGeometricMean n α) := by
  -- Route correction: prove the exact-sum-one case first, then normalize and compose with `rpow`.
  let s : ℝ := ∑ k, α k
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun k _ => hα_nonneg k
  have hs_le_one : s ≤ 1 := by
    simpa [s] using hα_sum
  by_cases hs_zero : s = 0
  · -- Step: zero total mass makes the function constant equal to `1`.
    have hfun : weightedGeometricMean n α = fun _ : Fin n → ℝ => 1 := by
      funext x
      exact weightedGeometricMean_eq_one_of_sum_eq_zero n α hα_nonneg (by simpa [s] using hs_zero) x
    simpa [hfun] using concaveOn_const (c := (1 : ℝ)) (convex_positiveOrthant n)
  · have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (by simpa [eq_comm] using hs_zero)
    let β : Fin n → ℝ := fun k => α k / s
    have hβ_nonneg : ∀ k, 0 ≤ β k := by
      intro k
      dsimp [β]
      exact div_nonneg (hα_nonneg k) hs_nonneg
    have hβ_sum : ∑ k, β k = 1 := by
      -- Normalize the weights by dividing by their positive total mass.
      calc
        ∑ k, β k = (∑ k, α k) / s := by
          simp [β, Finset.sum_div]
        _ = s / s := by simp [s]
        _ = 1 := by
          field_simp [hs_zero]
    have hβ_concave :
        ConcaveOn ℝ {x : Fin n → ℝ | ∀ k, 0 < x k} (weightedGeometricMean n β) :=
      weightedGeometricMean_concaveOn_pos_of_sum_eq_one n β hβ_nonneg hβ_sum
    refine ⟨hβ_concave.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxy_pos : a • x + b • y ∈ {x : Fin n → ℝ | ∀ k, 0 < x k} :=
      hβ_concave.1 hx hy ha hb hab
    have hβ_base :
        a * weightedGeometricMean n β x + b * weightedGeometricMean n β y ≤
          weightedGeometricMean n β (a • x + b • y) := by
      -- Use concavity for the normalized weights before applying `rpow`.
      simpa [smul_eq_mul] using hβ_concave.2 hx hy ha hb hab
    have hrpow :
        a * (weightedGeometricMean n β x) ^ s + b * (weightedGeometricMean n β y) ^ s ≤
          (a * weightedGeometricMean n β x + b * weightedGeometricMean n β y) ^ s := by
      -- The map `t ↦ t ^ s` is concave on `[0, ∞)` because `0 ≤ s ≤ 1`.
      simpa [smul_eq_mul] using
        (Real.concaveOn_rpow hs_nonneg hs_le_one).2
          (weightedGeometricMean_nonneg n β x fun k => (hx k).le)
          (weightedGeometricMean_nonneg n β y fun k => (hy k).le)
          ha hb hab
    have hmono :
        (a * weightedGeometricMean n β x + b * weightedGeometricMean n β y) ^ s ≤
          (weightedGeometricMean n β (a • x + b • y)) ^ s := by
      -- Monotonicity of `rpow` transfers the normalized concavity bound to the powered level.
      exact (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hs_nonneg)
        (by
          exact add_nonneg
            (mul_nonneg ha (weightedGeometricMean_nonneg n β x fun k => (hx k).le))
            (mul_nonneg hb (weightedGeometricMean_nonneg n β y fun k => (hy k).le)))
        (weightedGeometricMean_nonneg n β (a • x + b • y) fun k => (hxy_pos k).le)
        hβ_base
    have hx_norm :
        weightedGeometricMean n α x = (weightedGeometricMean n β x) ^ s := by
      -- Replace the original weights by normalized weights and an outer power.
      simpa [β, s] using
        weightedGeometricMean_eq_rpow_normalized n α x hx s rfl hs_zero
    have hy_norm :
        weightedGeometricMean n α y = (weightedGeometricMean n β y) ^ s := by
      -- The same normalization identity holds at `y`.
      simpa [β, s] using
        weightedGeometricMean_eq_rpow_normalized n α y hy s rfl hs_zero
    have hxy_norm :
        weightedGeometricMean n α (a • x + b • y) =
          (weightedGeometricMean n β (a • x + b • y)) ^ s := by
      -- And it also holds at the convex combination because the positive orthant is convex.
      simpa [β, s] using
        weightedGeometricMean_eq_rpow_normalized n α (a • x + b • y) hxy_pos s rfl hs_zero
    -- Combine concavity of the normalized mean with concavity and monotonicity of `rpow`.
    simpa [smul_eq_mul, hx_norm, hy_norm, hxy_norm] using le_trans hrpow hmono

end «problem-185»
