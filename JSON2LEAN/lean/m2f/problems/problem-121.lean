import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-121»
/-
For f: ℝ^n → ℝ, define epi f = {(x, t): f(x) ≤ t}. Define g(x) = \inf{t: (x, t)∈conv(epi f)}. Prove
that g is the largest convex underestimator of f: if h is convex and h ≤ f, then h ≤ g.
-/
open scoped Convex

theorem convex_underestimator_le_infConvEpigraph
    {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (hsection_nonempty :
      ∀ x : Fin n → ℝ,
        Set.Nonempty
          {t : ℝ | ((x, t) : (Fin n → ℝ) × ℝ) ∈
            convexHull ℝ {p | f p.1 ≤ p.2}})
    (hsection_bddBelow :
      ∀ x : Fin n → ℝ,
        BddBelow
          {t : ℝ | ((x, t) : (Fin n → ℝ) × ℝ) ∈
            convexHull ℝ {p | f p.1 ≤ p.2}})
    (hg :
      ∀ x,
        g x =
          sInf {t : ℝ | ((x, t) : (Fin n → ℝ) × ℝ) ∈ convexHull ℝ {p | f p.1 ≤ p.2}}) :
    ConvexOn ℝ Set.univ g ∧
      (∀ x, g x ≤ f x) ∧
      (∀ h : (Fin n → ℝ) → ℝ, ConvexOn ℝ Set.univ h → (∀ x, h x ≤ f x) → ∀ x, h x ≤ g x) := by
  let S : (Fin n → ℝ) → Set ℝ := fun x =>
    {t : ℝ | ((x, t) : (Fin n → ℝ) × ℝ) ∈ convexHull ℝ {p | f p.1 ≤ p.2}}
  -- Rewrite the section formula once so all later `sInf` arguments use the same set `S`.
  have hsection_nonempty' : ∀ x : Fin n → ℝ, Set.Nonempty (S x) := by
    intro x
    simpa [S] using hsection_nonempty x
  have hsection_bddBelow' : ∀ x : Fin n → ℝ, BddBelow (S x) := by
    intro x
    simpa [S] using hsection_bddBelow x
  have hgS : ∀ x, g x = sInf (S x) := by
    intro x
    simpa [S] using hg x
  -- Every graph point `(x, f x)` already lies in the original epigraph, hence in its convex hull.
  have hpoint_mem : ∀ x : Fin n → ℝ, f x ∈ S x := by
    intro x
    change ((x, f x) : (Fin n → ℝ) × ℝ) ∈
      convexHull ℝ {p : (Fin n → ℝ) × ℝ | f p.1 ≤ p.2}
    exact subset_convexHull ℝ {p : (Fin n → ℝ) × ℝ | f p.1 ≤ p.2} (by simp)
  have hgf : ∀ x, g x ≤ f x := by
    intro x
    rw [hgS x]
    exact csInf_le (hsection_bddBelow' x) (hpoint_mem x)
  -- Any convex underestimator has a convex epigraph containing the original epigraph and therefore its hull.
  have hunder_on_hull :
      ∀ {h : (Fin n → ℝ) → ℝ}, ConvexOn ℝ Set.univ h → (∀ x, h x ≤ f x) →
        ∀ {x t}, t ∈ S x → h x ≤ t := by
    intro h hh hle x t ht
    have hsub :
        {p : (Fin n → ℝ) × ℝ | f p.1 ≤ p.2} ⊆
          {p : (Fin n → ℝ) × ℝ | h p.1 ≤ p.2} := by
      intro p hp
      exact le_trans (hle p.1) hp
    have hconv : Convex ℝ {p : (Fin n → ℝ) × ℝ | h p.1 ≤ p.2} := by
      simpa using
        (hh.convex_epigraph :
          Convex ℝ {p : (Fin n → ℝ) × ℝ | p.1 ∈ Set.univ ∧ h p.1 ≤ p.2})
    exact (convexHull_min hsub hconv) ht
  have hmax :
      ∀ h : (Fin n → ℝ) → ℝ, ConvexOn ℝ Set.univ h → (∀ x, h x ≤ f x) → ∀ x, h x ≤ g x := by
    intro h hh hle x
    rw [hgS x]
    exact le_csInf (hsection_nonempty' x) (by
      intro t ht
      exact hunder_on_hull hh hle ht)
  -- Route correction: instead of identifying the whole epigraph of `g`, we prove convexity
  -- directly from the section infimum formula by approximating the infima from above.
  have hconvex : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hconvex_mul : g (a • x + b • y) ≤ a * g x + b * g y := by
      rw [le_iff_forall_pos_lt_add]
      intro ε hε
      -- Pick points in the two vertical sections that sit within `ε / 2` of the infima.
      have hxlt : sInf (S x) < g x + ε / 2 := by
        rw [← hgS x]
        linarith
      have hylt : sInf (S y) < g y + ε / 2 := by
        rw [← hgS y]
        linarith
      obtain ⟨t₁, ht₁mem, ht₁lt⟩ := exists_lt_of_csInf_lt (hsection_nonempty' x) hxlt
      obtain ⟨t₂, ht₂mem, ht₂lt⟩ := exists_lt_of_csInf_lt (hsection_nonempty' y) hylt
      -- Convexity of the hull keeps the convex combination of the two approximate section points inside.
      have hcombo_mem : a * t₁ + b * t₂ ∈ S (a • x + b • y) := by
        change ((a • x + b • y, a * t₁ + b * t₂) : (Fin n → ℝ) × ℝ) ∈
          convexHull ℝ {p : (Fin n → ℝ) × ℝ | f p.1 ≤ p.2}
        have hconv :
            Convex ℝ (convexHull ℝ {p : (Fin n → ℝ) × ℝ | f p.1 ≤ p.2}) :=
          convex_convexHull ℝ _
        simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_add, add_comm, add_left_comm,
          add_assoc, mul_comm, mul_left_comm, mul_assoc] using hconv ht₁mem ht₂mem ha hb hab
      have hglb : g (a • x + b • y) ≤ a * t₁ + b * t₂ := by
        rw [hgS (a • x + b • y)]
        exact csInf_le (hsection_bddBelow' (a • x + b • y)) hcombo_mem
      -- Scale the two approximation inequalities by the nonnegative coefficients and keep
      -- the remaining strictness for the final `ε / 2 < ε` step.
      have ht₁scaled : a * t₁ ≤ a * g x + a * (ε / 2) := by
        have hmul := mul_le_mul_of_nonneg_left ht₁lt.le ha
        nlinarith
      have ht₂scaled : b * t₂ ≤ b * g y + b * (ε / 2) := by
        have hmul := mul_le_mul_of_nonneg_left ht₂lt.le hb
        nlinarith
      have hsum_le : a * t₁ + b * t₂ ≤ a * g x + b * g y + ε / 2 := by
        nlinarith [ht₁scaled, ht₂scaled, hab]
      have hεhalf : a * g x + b * g y + ε / 2 < a * g x + b * g y + ε := by
        linarith
      exact lt_of_le_of_lt hglb (lt_of_le_of_lt hsum_le hεhalf)
    simpa [smul_eq_mul] using hconvex_mul
  exact ⟨hconvex, hgf, hmax⟩

end «problem-121»
