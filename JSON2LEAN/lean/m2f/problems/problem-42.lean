import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-42»
/-
Let C be a convex set. A function f: C → ℝ U {+ infinity} is quasiconvex if for all x, y in C and
all
θ in [0, 1], f(θ x + (1 - θ) y) < = max{f(x), f(y)}.
-/
def QuasiconvexOn {E : Type*} [AddCommMonoid E] [Module ℝ E] (C : Set E)
    (hC : Convex ℝ C) (f : C → WithTop ℝ) : Prop :=
  ∀ (x y : C) (θ : ℝ), ∀ hθ : θ ∈ Set.Icc (0 : ℝ) 1,
    f ⟨θ • (x : E) + (1 - θ) • (y : E), by
      exact hC x.property y.property hθ.1 (sub_nonneg.mpr hθ.2) (by ring)
    ⟩ ≤
      max (f x) (f y)

/-
Let c ∈ ℝ^n, d ∈ ℝ, A ∈ ℝ^(p x n), and b ∈ ℝ^p. Let f₀, f₁, ..., fₘ: ℝ^n → ℝ U {+ infinity} be
convex
functions, and let dom f₀ = {x ∈ ℝ^n | f₀(x) < + infinity}. Define S = {x ∈ ℝ^n | fᵢ(x) < = 0 for
all
i = 1, ..., m, Ax = b, x in dom f₀, cᵀ x + d > 0}. Show that S is convex.
-/
theorem convex_feasibleSet_of_quasiconvex_constraints
    {n p m : ℕ}
    (A : Matrix (Fin p) (Fin n) ℝ)
    (b : Fin p → ℝ)
    (c : Fin n → ℝ)
    (d : ℝ)
    (f0 : (Fin n → ℝ) → WithTop ℝ)
    (f : Fin m → (Fin n → ℝ) → WithTop ℝ)
    (hf0 : Convex ℝ {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)})
    (hf : ∀ i : Fin m,
      Convex ℝ {xt : (Fin n → ℝ) × ℝ | f i xt.1 ≤ (xt.2 : WithTop ℝ)}) :
    Convex ℝ
      {x : Fin n → ℝ |
        (∀ i : Fin m, f i x ≤ (0 : WithTop ℝ)) ∧
        Matrix.mulVec A x = b ∧
        f0 x < ⊤ ∧
        (∑ j : Fin n, c j * x j) + d > 0} := by
  simp only [Convex, StarConvex]
  intro x hx y hy a t ha ht hsum
  rcases hx with ⟨hx_sub, hx_eq, hx_fin, hx_pos⟩
  rcases hy with ⟨hy_sub, hy_eq, hy_fin, hy_pos⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Each inequality constraint is preserved because its epigraph is convex at height `0`.
    intro i
    have hx_epi : ((x, (0 : ℝ)) : (Fin n → ℝ) × ℝ) ∈
        {xt : (Fin n → ℝ) × ℝ | f i xt.1 ≤ (xt.2 : WithTop ℝ)} := by
      simpa using hx_sub i
    have hy_epi : ((y, (0 : ℝ)) : (Fin n → ℝ) × ℝ) ∈
        {xt : (Fin n → ℝ) × ℝ | f i xt.1 ≤ (xt.2 : WithTop ℝ)} := by
      simpa using hy_sub i
    -- Evaluating the convex combination in the epigraph gives the desired sublevel bound.
    simpa using (hf i hx_epi hy_epi ha ht hsum)
  · -- The affine equality constraint is preserved by linearity of `mulVec`.
    calc
      Matrix.mulVec A (a • x + t • y)
          = Matrix.mulVec A (a • x) + Matrix.mulVec A (t • y) := by
              rw [Matrix.mulVec_add]
      _ = a • Matrix.mulVec A x + t • Matrix.mulVec A y := by
            rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
      _ = a • b + t • b := by
            rw [hx_eq, hy_eq]
      _ = (a + t) • b := by
            rw [← add_smul]
      _ = b := by
            rw [hsum, one_smul]
  · -- Finite epigraph witnesses for `f0 x` and `f0 y` keep the convex combination in `dom f0`.
    have hx_ne : f0 x ≠ ⊤ := lt_top_iff_ne_top.mp hx_fin
    have hy_ne : f0 y ≠ ⊤ := lt_top_iff_ne_top.mp hy_fin
    obtain ⟨rx, hrx⟩ := WithTop.ne_top_iff_exists.mp hx_ne
    obtain ⟨ry, hry⟩ := WithTop.ne_top_iff_exists.mp hy_ne
    have hx_epi : ((x, rx) : (Fin n → ℝ) × ℝ) ∈
        {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)} := by
      change f0 x ≤ (rx : WithTop ℝ)
      rw [hrx]
    have hy_epi : ((y, ry) : (Fin n → ℝ) × ℝ) ∈
        {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)} := by
      change f0 y ≤ (ry : WithTop ℝ)
      rw [hry]
    have hcombo :
        f0 (a • x + t • y) ≤ (((a * rx) + (t * ry) : ℝ) : WithTop ℝ) := by
      simpa [hrx, hry] using (hf0 hx_epi hy_epi ha ht hsum)
    exact lt_of_le_of_lt hcombo (WithTop.coe_lt_top _)
  · -- The linear denominator becomes a weighted average, so strict positivity follows by `nlinarith`.
    have hlinear :
        (∑ j : Fin n, c j * (a • x + t • y) j) + d =
          a * ((∑ j : Fin n, c j * x j) + d) + t * ((∑ j : Fin n, c j * y j) + d) := by
      calc
        (∑ j : Fin n, c j * (a • x + t • y) j) + d
            = (∑ j : Fin n, (a * (c j * x j) + t * (c j * y j))) + d := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [Pi.smul_apply]
                ring
        _ = ((∑ j : Fin n, a * (c j * x j)) + ∑ j : Fin n, t * (c j * y j)) + d := by
              rw [Finset.sum_add_distrib]
        _ = (a * (∑ j : Fin n, c j * x j) + t * (∑ j : Fin n, c j * y j)) + d := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
        _ = a * (∑ j : Fin n, c j * x j) + t * (∑ j : Fin n, c j * y j) + d := by
              ring
        _ = a * (∑ j : Fin n, c j * x j) + t * (∑ j : Fin n, c j * y j) + (a + t) * d := by
              rw [hsum, one_mul]
        _ = a * ((∑ j : Fin n, c j * x j) + d) + t * ((∑ j : Fin n, c j * y j) + d) := by
              ring
    rw [hlinear]
    by_cases ha_zero : a = 0
    · have ht_one : t = 1 := by nlinarith [hsum, ha_zero]
      simpa [ha_zero, ht_one] using hy_pos
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_zero)
      have hleft : 0 < a * ((∑ j : Fin n, c j * x j) + d) := by
        exact mul_pos ha_pos hx_pos
      have hright : 0 ≤ t * ((∑ j : Fin n, c j * y j) + d) := by
        exact mul_nonneg ht (le_of_lt hy_pos)
      linarith

/-
Let c ∈ ℝ^n and d ∈ ℝ. Let f₀, f₁, ..., fₘ: ℝ^n → ℝ U {+ infinity} be convex functions, and let dom
f₀
= {x ∈ ℝ^n | f₀(x) < + infinity}. Show that the function x - > f₀(x) / (cᵀ x + d) is quasiconvex on
the domain {x in dom f₀ | cᵀ x + d > 0}.
-/
/-- The affine denominator respects convex combinations. -/
lemma denominator_convexCombination
    {n : ℕ}
    (c : Fin n → ℝ)
    (d : ℝ)
    (x y : Fin n → ℝ)
    (θ : ℝ) :
    (∑ j : Fin n, c j * (θ • x + (1 - θ) • y) j) + d =
      θ * ((∑ j : Fin n, c j * x j) + d) + (1 - θ) * ((∑ j : Fin n, c j * y j) + d) := by
  -- Expand the linear form coordinatewise, then regroup the scalar coefficients.
  calc
    (∑ j : Fin n, c j * (θ • x + (1 - θ) • y) j) + d
        = (∑ j : Fin n, (θ * (c j * x j) + (1 - θ) * (c j * y j))) + d := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Pi.smul_apply]
            ring
    _ = ((∑ j : Fin n, θ * (c j * x j)) + ∑ j : Fin n, (1 - θ) * (c j * y j)) + d := by
          rw [Finset.sum_add_distrib]
    _ = (θ * (∑ j : Fin n, c j * x j) + (1 - θ) * (∑ j : Fin n, c j * y j)) + d := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = θ * (∑ j : Fin n, c j * x j) + (1 - θ) * (∑ j : Fin n, c j * y j) + d := by
          ring
    _ = θ * (∑ j : Fin n, c j * x j) + (1 - θ) * (∑ j : Fin n, c j * y j) +
          (θ + (1 - θ)) * d := by
            ring
    _ = θ * ((∑ j : Fin n, c j * x j) + d) + (1 - θ) * ((∑ j : Fin n, c j * y j) + d) := by
          ring

/-- A finite `WithTop ℝ` value is the coercion of its `getD 0`. -/
lemma withTop_eq_coe_getD_of_lt_top
    {a : WithTop ℝ}
    (ha : a < ⊤) :
    a = (((a.getD 0 : ℝ)) : WithTop ℝ) := by
  -- Replace the finite `WithTop` value by an explicit real witness and reduce by reflexivity.
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (lt_top_iff_ne_top.mp ha)
  rw [← hr]
  rfl

/-- A ratio bound with positive denominator gives an epigraph point at the scaled height. -/
lemma epigraph_mem_of_div_le
    {n : ℕ}
    {f0 : (Fin n → ℝ) → WithTop ℝ}
    {x : Fin n → ℝ}
    {dx α : ℝ}
    (hx_fin : f0 x < ⊤)
    (hdx : 0 < dx)
    (hdiv : (f0 x).getD 0 / dx ≤ α) :
    ((x, α * dx) : (Fin n → ℝ) × ℝ) ∈
      {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)} := by
  -- Rewrite the finite `WithTop` value as a real and clear the positive denominator.
  change f0 x ≤ ((α * dx : ℝ) : WithTop ℝ)
  rw [withTop_eq_coe_getD_of_lt_top hx_fin]
  have hmul : (f0 x).getD 0 ≤ α * dx := (div_le_iff₀ hdx).mp hdiv
  have hmul' : ((((f0 x).getD 0 : ℝ)) : WithTop ℝ) ≤ (((α * dx : ℝ) : WithTop ℝ)) := by
    exact_mod_cast hmul
  simpa using hmul'

theorem quasiconvexOn_perspective_of_convex
    {n : ℕ}
    (c : Fin n → ℝ)
    (d : ℝ)
    (f0 : (Fin n → ℝ) → WithTop ℝ)
    (hf0 : Convex ℝ {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)})
    (hC :
      Convex ℝ
        {x : Fin n → ℝ | f0 x < ⊤ ∧ 0 < (∑ j : Fin n, c j * x j) + d}) :
    QuasiconvexOn
      {x : Fin n → ℝ | f0 x < ⊤ ∧ 0 < (∑ j : Fin n, c j * x j) + d}
      hC
      (fun x => ((f0 x.1).getD 0 / ((∑ j : Fin n, c j * x.1 j) + d) : ℝ)) := by
  -- Unfold quasiconvexity and name the three denominators together with the common height bound.
  intro x y θ hθ
  let z : Fin n → ℝ := θ • x.1 + (1 - θ) • y.1
  let dx : ℝ := (∑ j : Fin n, c j * x.1 j) + d
  let dy : ℝ := (∑ j : Fin n, c j * y.1 j) + d
  let dz : ℝ := (∑ j : Fin n, c j * z j) + d
  let M : ℝ := max ((f0 x.1).getD 0 / dx) ((f0 y.1).getD 0 / dy)
  have hx_fin : f0 x.1 < ⊤ := x.property.1
  have hy_fin : f0 y.1 < ⊤ := y.property.1
  have hx_pos : 0 < dx := by
    simpa [dx] using x.property.2
  have hy_pos : 0 < dy := by
    simpa [dy] using y.property.2
  have hz_mem : z ∈ {x : Fin n → ℝ | f0 x < ⊤ ∧ 0 < (∑ j : Fin n, c j * x j) + d} := by
    -- Convexity of the domain keeps the mixed point in the finite positive-denominator region.
    simpa [z] using
      (hC x.property y.property hθ.1 (sub_nonneg.mpr hθ.2) (by ring))
  have hz_fin : f0 z < ⊤ := hz_mem.1
  have hz_pos : 0 < dz := by
    simpa [dz] using hz_mem.2
  have hx_epi : ((x.1, M * dx) : (Fin n → ℝ) × ℝ) ∈
      {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)} := by
    -- The left endpoint lies below the common height `M * dx` because its ratio is one branch of `M`.
    apply epigraph_mem_of_div_le hx_fin hx_pos
    simp [M]
  have hy_epi : ((y.1, M * dy) : (Fin n → ℝ) × ℝ) ∈
      {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)} := by
    -- The same argument gives the right endpoint at height `M * dy`.
    apply epigraph_mem_of_div_le hy_fin hy_pos
    simp [M]
  have hz_epi : ((z, M * dz) : (Fin n → ℝ) × ℝ) ∈
      {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)} := by
    -- Convexity of the epigraph propagates the common height bound to the mixed point.
    convert (hf0 hx_epi hy_epi hθ.1 (sub_nonneg.mpr hθ.2) (by ring)) using 1
    ext
    · simp [z]
    · simp [dz, dx, dy, z, denominator_convexCombination]
      ring
  have hz_real : (f0 z).getD 0 ≤ M * dz := by
    -- Convert the finite epigraph inequality for `z` back to a real inequality.
    change f0 z ≤ ((M * dz : ℝ) : WithTop ℝ) at hz_epi
    rw [withTop_eq_coe_getD_of_lt_top hz_fin] at hz_epi
    have hz_epi' : ((((f0 z).getD 0 : ℝ)) : WithTop ℝ) ≤ (((M * dz : ℝ) : WithTop ℝ)) := by
      simpa using hz_epi
    exact_mod_cast hz_epi'
  have hz_div : (f0 z).getD 0 / dz ≤ M := by
    -- The mixed denominator stays positive, so we can divide through safely.
    exact (div_le_iff₀ hz_pos).2 hz_real
  -- Repackage the real inequality as the required `WithTop` comparison.
  simpa [z, dx, dy, dz, M, WithTop.coe_max] using hz_div

/-
Let D = {p ∈ ℝ_ + ^m | a_iᵀ p > 0 for i = 1, ..., n}. Define f(p) = max_{i = 1, ..., n} |log(a_iᵀ p)
-
log(I_des)| for p in D, where aᵢ ∈ ℝ^m for i = 1, ..., n and I_des > 0. Show that the function p - >
exp(f(p)) is convex on D.
-/
open scoped RealInnerProductSpace

theorem exp_max_log_deviation_convexOn
    {m n : ℕ} [NeZero n]
    (a : Fin n → EuclideanSpace ℝ (Fin m)) {I_des : ℝ} (hI_des : 0 < I_des) :
    ConvexOn ℝ
      {p : EuclideanSpace ℝ (Fin m) |
        (∀ j : Fin m, 0 ≤ p j) ∧ ∀ i : Fin n, 0 < ⟪a i, p⟫}
      (fun p =>
        Real.exp
          (Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin n => |Real.log ⟪a i, p⟫ - Real.log I_des|))) := by
  let D : Set (EuclideanSpace ℝ (Fin m)) :=
    {p | (∀ j : Fin m, 0 ≤ p j) ∧ ∀ i : Fin n, 0 < ⟪a i, p⟫}
  let g : Fin n → EuclideanSpace ℝ (Fin m) → ℝ :=
    fun i p => max (⟪a i, p⟫ / I_des) (I_des / ⟪a i, p⟫)
  have hD : Convex ℝ D := by
    -- The domain is closed under convex combinations because coordinates stay nonnegative
    -- and each required inner product stays a positive weighted average.
    intro x hx y hy α β hα hβ hαβ
    refine ⟨?_, ?_⟩
    · intro j
      have hxj : 0 ≤ x j := hx.1 j
      have hyj : 0 ≤ y j := hy.1 j
      simp
      nlinarith
    · intro i
      have hxi : 0 < ⟪a i, x⟫ := hx.2 i
      have hyi : 0 < ⟪a i, y⟫ := hy.2 i
      have hinner :
          ⟪a i, α • x + β • y⟫ = α * ⟪a i, x⟫ + β * ⟪a i, y⟫ := by
        rw [inner_add_right, inner_smul_right, inner_smul_right]
      rw [hinner]
      by_cases hα_zero : α = 0
      · have hβ_one : β = 1 := by nlinarith
        simpa [hα_zero, hβ_one] using hyi
      · have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα_zero)
        have hleft : 0 < α * ⟪a i, x⟫ := mul_pos hα_pos hxi
        have hright : 0 ≤ β * ⟪a i, y⟫ := mul_nonneg hβ hyi.le
        linarith
  have hg : ∀ i : Fin n, ConvexOn ℝ D (g i) := by
    intro i
    have hLinear : ConvexOn ℝ D (fun p : EuclideanSpace ℝ (Fin m) => ⟪a i, p⟫) := by
      -- The inner product with a fixed vector is linear, hence convex.
      simpa [innerSL_apply_apply] using (((innerSL ℝ (a i)).toLinearMap).convexOn hD)
    have hRatio : ConvexOn ℝ D (fun p : EuclideanSpace ℝ (Fin m) => ⟪a i, p⟫ / I_des) := by
      -- Scaling the linear branch by the nonnegative constant `I_des⁻¹` preserves convexity.
      simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        hLinear.smul (show 0 ≤ I_des⁻¹ by positivity)
    have hInv :
        ConvexOn ℝ {p : EuclideanSpace ℝ (Fin m) | 0 < ⟪a i, p⟫}
          (fun p => I_des / ⟪a i, p⟫) := by
      -- Compose the convex reciprocal function on `(0, ∞)` with the inner-product linear map.
      simpa [Function.comp, Set.preimage, innerSL_apply_apply, div_eq_mul_inv, smul_eq_mul] using
        ((convexOn_zpow (-1 : ℤ)).comp_linearMap ((innerSL ℝ (a i)).toLinearMap)).smul hI_des.le
    have hInvOnD : ConvexOn ℝ D (fun p : EuclideanSpace ℝ (Fin m) => I_des / ⟪a i, p⟫) := by
      -- The target domain sits inside the positive-inner-product domain for the chosen index.
      exact hInv.subset (fun p hp => hp.2 i) hD
    -- The maximum of the two convex ratio branches is convex.
    refine (hRatio.sup hInvOnD).congr ?_
    intro p hp
    simp [g, sup_eq_maxDefault, maxDefault]
  have hSup :
      ConvexOn ℝ D
        (fun p : EuclideanSpace ℝ (Fin m) =>
          Finset.univ.sup' Finset.univ_nonempty (fun i : Fin n => g i p)) := by
    -- Finite suprema preserve convexity because pointwise `sup` is pointwise `max`.
    classical
    have hSup' : ConvexOn ℝ D (Finset.univ.sup' Finset.univ_nonempty g) := by
      refine Finset.sup'_induction (s := Finset.univ) (H := Finset.univ_nonempty)
        (f := g) (p := fun f : EuclideanSpace ℝ (Fin m) → ℝ => ConvexOn ℝ D f) ?_ ?_
      · intro f hf f' hf'
        exact hf.sup hf'
      · intro i hi
        exact hg i
    convert hSup' using 1
    ext p
    exact
      (Finset.comp_sup'_eq_sup'_comp (s := Finset.univ) (H := Finset.univ_nonempty) (f := g)
        (fun h : EuclideanSpace ℝ (Fin m) → ℝ => h p) (fun h h' => rfl)).symm
  have hEq :
      Set.EqOn
        (fun p : EuclideanSpace ℝ (Fin m) =>
          Real.exp
            (Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin n => |Real.log ⟪a i, p⟫ - Real.log I_des|)))
        (fun p : EuclideanSpace ℝ (Fin m) =>
          Finset.univ.sup' Finset.univ_nonempty (fun i : Fin n => g i p))
        D := by
    intro p hp
    change
      Real.exp
          (Finset.univ.sup' Finset.univ_nonempty
            (fun i : Fin n => |Real.log ⟪a i, p⟫ - Real.log I_des|)) =
        Finset.univ.sup' Finset.univ_nonempty (fun i : Fin n => g i p)
    -- Rewrite `exp` of the finite supremum as the finite supremum of the exponential branches.
    rw [Finset.comp_sup'_eq_sup'_comp Finset.univ_nonempty Real.exp
      (fun x y => Real.exp_monotone.map_sup x y)]
    refine Finset.sup'_congr (s := Finset.univ) (H := Finset.univ_nonempty) (t := Finset.univ)
      rfl ?_
    intro i hi
    dsimp [g]
    have hInner : 0 < ⟪a i, p⟫ := hp.2 i
    by_cases hle : ⟪a i, p⟫ ≤ I_des
    · -- Below the target intensity, the deviation is `log (I_des / ⟪a i, p⟫)`.
      have hlog : Real.log ⟪a i, p⟫ - Real.log I_des ≤ 0 := by
        exact sub_nonpos.mpr (Real.log_le_log hInner hle)
      have hneg :
          -(Real.log ⟪a i, p⟫ - Real.log I_des) =
            Real.log I_des - Real.log ⟪a i, p⟫ := by
        ring
      rw [abs_of_nonpos hlog, hneg, ← Real.log_div hI_des.ne' hInner.ne',
        Real.exp_log (div_pos hI_des hInner), max_eq_right]
      field_simp [hInner.ne', hI_des.ne']
      nlinarith [hInner.le, hI_des.le, hle]
    · -- Above the target intensity, the deviation is `log (⟪a i, p⟫ / I_des)`.
      have hge : I_des ≤ ⟪a i, p⟫ := le_of_not_ge hle
      have hlog : 0 ≤ Real.log ⟪a i, p⟫ - Real.log I_des := by
        exact sub_nonneg.mpr (Real.log_le_log hI_des hge)
      rw [abs_of_nonneg hlog, ← Real.log_div hInner.ne' hI_des.ne',
        Real.exp_log (div_pos hInner hI_des), max_eq_left]
      field_simp [hInner.ne', hI_des.ne']
      nlinarith [hInner.le, hI_des.le, hge]
  -- Replace the original expression by the finite supremum of convex max-of-ratio terms.
  simpa [D] using
    (hSup.congr fun p hp => (hEq hp).symm)
end «problem-42»
