import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators
open scoped Pointwise

namespace «problem-124»
/-
Let V be a real vector space, f: V → ℝ convex, and g(x) = \inf_{α > 0} f(αx)/α (possibly −∞). Prove
that g is convex.
-/
theorem inf_rescaling_convex
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    let g : V → WithBot ℝ :=
      fun x => sInf {r : WithBot ℝ | ∃ α : ℝ, 0 < α ∧ r = ((f (α • x) / α : ℝ) : WithBot ℝ)}
    ∀ x y : V, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      g (t • x + (1 - t) • y) ≤
        ((t : ℝ) : WithBot ℝ) * g x + ((1 - t : ℝ) : WithBot ℝ) * g y := by
  classical
  dsimp
  let S : V → Set ℝ := fun x => {r : ℝ | ∃ α : ℝ, 0 < α ∧ r = f (α • x) / α}
  let g : V → WithBot ℝ := fun x => sInf ((fun r : ℝ => (r : WithBot ℝ)) '' S x)
  have hS_nonempty : ∀ x : V, (S x).Nonempty := by
    intro x
    refine ⟨f x, ?_⟩
    refine ⟨1, zero_lt_one, ?_⟩
    simp
  have hg_eq_bot_of_not_bddBelow : ∀ {x : V}, ¬ BddBelow (S x) → g x = ⊥ := by
    intro x hx
    -- If the real rescaling values are unbounded below, the corresponding `WithBot` infimum is `⊥`.
    change sInf ((fun r : ℝ => (r : WithBot ℝ)) '' S x) = ⊥
    exact (WithBot.eq_bot_iff_forall_le).2 (by
      intro m
      rcases (not_bddBelow_iff.1 hx) m with ⟨r, hr, hrm⟩
      have hmem : ((r : ℝ) : WithBot ℝ) ∈ (fun r : ℝ => (r : WithBot ℝ)) '' S x := ⟨r, hr, rfl⟩
      exact (csInf_le (OrderBot.bddBelow _) hmem).trans (WithBot.coe_le_coe.2 hrm.le))
  have hg_eq_coe_sInf : ∀ {x : V}, BddBelow (S x) → g x = ↑(sInf (S x)) := by
    intro x hx
    -- In the bounded-below case, the `WithBot` infimum is just the coerced real infimum.
    simpa [g] using (WithBot.coe_sInf' (s := S x) hx).symm
  have hcombo :
      ∀ {x y : V} {t α β : ℝ},
        0 ≤ t → t ≤ 1 → 0 < α → 0 < β →
          ∃ c ∈ S (t • x + (1 - t) • y),
            c ≤ t * (f (α • x) / α) + (1 - t) * (f (β • y) / β) := by
    intro x y t α β ht0 ht1 hα hβ
    let δ : ℝ := t * β + (1 - t) * α
    let γ : ℝ := α * β / δ
    have hδ : 0 < δ := by
      by_cases h0 : t = 0
      · subst h0
        dsimp [δ]
        simpa using hα
      by_cases h1 : t = 1
      · subst h1
        dsimp [δ]
        simpa using hβ
      have ht' : 0 < t := lt_of_le_of_ne ht0 (by simpa [eq_comm] using h0)
      have ht1' : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 (by simpa [eq_comm] using h1))
      dsimp [δ]
      nlinarith [mul_pos ht' hβ, mul_pos ht1' hα]
    have hγ : 0 < γ := by
      dsimp [γ]
      exact div_pos (mul_pos hα hβ) hδ
    have hu_nonneg : 0 ≤ t * β / δ := by
      exact div_nonneg (mul_nonneg ht0 hβ.le) hδ.le
    have hv_nonneg : 0 ≤ (1 - t) * α / δ := by
      exact div_nonneg (mul_nonneg (by linarith) hα.le) hδ.le
    have huv_sum : t * β / δ + (1 - t) * α / δ = 1 := by
      have hδ' : δ ≠ 0 := ne_of_gt hδ
      rw [← add_div, show t * β + (1 - t) * α = δ by rfl, div_self hδ']
    have hconv :=
      hf.2 (by simp : α • x ∈ Set.univ) (by simp : β • y ∈ Set.univ)
        hu_nonneg hv_nonneg huv_sum
    have hrewrite_left :
        (t * β / δ) • (α • x) + ((1 - t) * α / δ) • (β • y) =
          γ • (t • x + (1 - t) • y) := by
      have hcoef₁ : (t * β / δ) * α = γ * t := by
        have hδ' : δ ≠ 0 := ne_of_gt hδ
        dsimp [γ, δ]
        field_simp [hδ']
      have hcoef₂ : ((1 - t) * α / δ) * β = γ * (1 - t) := by
        have hδ' : δ ≠ 0 := ne_of_gt hδ
        dsimp [γ, δ]
        field_simp [hδ']
      calc
        (t * β / δ) • (α • x) + ((1 - t) * α / δ) • (β • y)
            = (((t * β / δ) * α) • x) + ((((1 - t) * α / δ) * β) • y) := by
                rw [smul_smul, smul_smul]
        _ = (γ * t) • x + (γ * (1 - t)) • y := by rw [hcoef₁, hcoef₂]
        _ = γ • (t • x) + γ • ((1 - t) • y) := by rw [smul_smul, smul_smul]
        _ = γ • (t • x + (1 - t) • y) := by rw [smul_add]
    have hrewrite_right :
        (t * β / δ) * f (α • x) + ((1 - t) * α / δ) * f (β • y) =
          γ * (t * (f (α • x) / α) + (1 - t) * (f (β • y) / β)) := by
      have hδ' : δ ≠ 0 := ne_of_gt hδ
      dsimp [γ, δ]
      field_simp [hα.ne', hβ.ne', hδ']
    refine ⟨f (γ • (t • x + (1 - t) • y)) / γ, ?_, ?_⟩
    · refine ⟨γ, hγ, rfl⟩
    · -- This is the core rescaling inequality coming from convexity after normalizing the weights.
      have hconv' :
          f (γ • (t • x + (1 - t) • y)) ≤
            γ * (t * (f (α • x) / α) + (1 - t) * (f (β • y) / β)) := by
        simpa [hrewrite_left, hrewrite_right] using hconv
      exact (div_le_iff₀ hγ).2 (by simpa [mul_comm] using hconv')
  have hunbounded_left :
      ∀ {x y : V} {t : ℝ},
        0 < t → t < 1 → ¬ BddBelow (S x) → ¬ BddBelow (S (t • x + (1 - t) • y)) := by
    intro x y t ht ht1 hx
    -- Route correction: instead of trying to compare infima directly in the `⊥` case,
    -- we propagate unboundedness by freezing the `y`-rescaling at `β = 1`.
    rw [not_bddBelow_iff]
    intro m
    have hy_mem : f y ∈ S y := by
      refine ⟨1, zero_lt_one, ?_⟩
      simp
    rcases (not_bddBelow_iff.1 hx) ((m - (1 - t) * f y) / t) with ⟨a, ha, hlt⟩
    rcases ha with ⟨α, hα, rfl⟩
    rcases hcombo (x := x) (y := y) (t := t) (α := α) (β := 1) ht.le ht1.le hα zero_lt_one with
      ⟨c, hc, hcle⟩
    refine ⟨c, hc, ?_⟩
    have hlt' : (f (α • x) / α) * t < m - (1 - t) * f y := by
      exact (lt_div_iff₀ ht).1 hlt
    have hmul : t * (f (α • x) / α) + (1 - t) * f y < m := by
      nlinarith [hlt']
    have hcle' : c ≤ t * (f (α • x) / α) + (1 - t) * f y := by
      simpa using hcle
    exact hcle'.trans_lt hmul
  have hfinite_bound :
      ∀ {x y : V} {t : ℝ},
        0 < t → t < 1 → BddBelow (S x) → BddBelow (S y) →
          g (t • x + (1 - t) • y) ≤
            ↑(t * sInf (S x) + (1 - t) * sInf (S y)) := by
    intro x y t ht ht1 hbx hby
    let z : V := t • x + (1 - t) • y
    let C : Set ℝ := t • S x + (1 - t) • S y
    have hC_nonempty : C.Nonempty := by
      rcases hS_nonempty x with ⟨a, ha⟩
      rcases hS_nonempty y with ⟨b, hb⟩
      exact ⟨t * a + (1 - t) * b, ⟨t * a, ⟨a, ha, rfl⟩, (1 - t) * b, ⟨b, hb, rfl⟩, rfl⟩⟩
    have hCx : BddBelow (t • S x) := hbx.smul_of_nonneg ht.le
    have hCy : BddBelow ((1 - t) • S y) := hby.smul_of_nonneg (by linarith)
    have hC_bdd : BddBelow C := by
      simpa [C] using hCx.add hCy
    have hg_le_C : g z ≤ ↑(sInf C) := by
      by_cases hzbot : g z = ⊥
      · simp [hzbot]
      · have hbz : BddBelow (S z) := by
          by_contra hbz
          exact hzbot (hg_eq_bot_of_not_bddBelow hbz)
        have hgz : g z = ↑(sInf (S z)) := hg_eq_coe_sInf hbz
        rw [hgz]
        apply WithBot.coe_le_coe.2
        refine le_csInf hC_nonempty ?_
        intro r hr
        rcases hr with ⟨a, ha, b, hb, rfl⟩
        rcases ha with ⟨a0, ha0, rfl⟩
        rcases hb with ⟨b0, hb0, rfl⟩
        rcases ha0 with ⟨α, hαpos, rfl⟩
        rcases hb0 with ⟨β, hβpos, rfl⟩
        rcases hcombo (x := x) (y := y) (t := t) (α := α) (β := β) ht.le ht1.le hαpos hβpos with
          ⟨c, hc, hcle⟩
        exact (csInf_le hbz hc).trans hcle
    have hCsInf :
        sInf C = t * sInf (S x) + (1 - t) * sInf (S y) := by
      have htx_nonempty : (t • S x).Nonempty := by
        rcases hS_nonempty x with ⟨a, ha⟩
        exact ⟨t * a, ⟨a, ha, rfl⟩⟩
      have hty_nonempty : ((1 - t) • S y).Nonempty := by
        rcases hS_nonempty y with ⟨b, hb⟩
        exact ⟨(1 - t) * b, ⟨b, hb, rfl⟩⟩
      calc
        sInf C = sInf (t • S x + (1 - t) • S y) := by rfl
        _ = sInf (t • S x) + sInf ((1 - t) • S y) := by
          exact csInf_add htx_nonempty hCx hty_nonempty hCy
        _ = t • sInf (S x) + (1 - t) • sInf (S y) := by
          rw [Real.sInf_smul_of_nonneg ht.le, Real.sInf_smul_of_nonneg (by linarith)]
        _ = t * sInf (S x) + (1 - t) * sInf (S y) := by
          simp [smul_eq_mul]
    simpa [hCsInf]
      using hg_le_C
  have hset :
      ∀ u : V,
        {r : WithBot ℝ | ∃ α : ℝ, 0 < α ∧ r = ((f (α • u) / α : ℝ) : WithBot ℝ)} =
          ((fun r : ℝ => (r : WithBot ℝ)) '' S u) := by
    intro u
    ext r
    constructor
    · intro hr
      rcases hr with ⟨α, hα, rfl⟩
      exact ⟨f (α • u) / α, ⟨α, hα, rfl⟩, rfl⟩
    · intro hr
      rcases hr with ⟨s, hs, rfl⟩
      rcases hs with ⟨α, hα, rfl⟩
      exact ⟨α, hα, rfl⟩
  intro x y t ht0 ht1
  rw [hset (t • x + (1 - t) • y), hset x, hset y]
  have hgoal :
      g (t • x + (1 - t) • y) ≤
        ((t : ℝ) : WithBot ℝ) * g x + ((1 - t : ℝ) : WithBot ℝ) * g y := by
    by_cases ht_eq0 : t = 0
    · -- At the left endpoint, the statement reduces to `g y ≤ g y`.
      subst ht_eq0
      simp [g]
    by_cases ht_eq1 : t = 1
    · -- At the right endpoint, the statement reduces to `g x ≤ g x`.
      subst ht_eq1
      simp [g]
    have ht : 0 < t := lt_of_le_of_ne ht0 (by simpa [eq_comm] using ht_eq0)
    have ht' : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 (by simpa [eq_comm] using ht_eq1))
    by_cases hbx : BddBelow (S x)
    · by_cases hby : BddBelow (S y)
      · -- In the finite case, we compare `g z` to the infimum of all convex combinations of values from `S x` and `S y`.
        have hgx : g x = ↑(sInf (S x)) := hg_eq_coe_sInf hbx
        have hgy : g y = ↑(sInf (S y)) := hg_eq_coe_sInf hby
        have hz :
            g (t • x + (1 - t) • y) ≤ ↑(t * sInf (S x) + (1 - t) * sInf (S y)) :=
          hfinite_bound ht (by linarith) hbx hby
        rw [hgx, hgy]
        simpa [WithBot.coe_mul, WithBot.coe_add] using hz
      · -- If `S y` is unbounded below, the right-hand side is `⊥`, so we propagate unboundedness to the left.
        have hgy : g y = ⊥ := hg_eq_bot_of_not_bddBelow hby
        have hzbot :
          g (t • x + (1 - t) • y) = ⊥ := by
          apply hg_eq_bot_of_not_bddBelow
          have := hunbounded_left (x := y) (y := x) (t := 1 - t) ht' (by linarith) hby
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, add_smul] using this
        simp [hgy, hzbot, ht'.ne']
    · -- If `S x` is unbounded below, the right-hand side is `⊥`, so the same is true on the left.
      have hgx : g x = ⊥ := hg_eq_bot_of_not_bddBelow hbx
      have hzbot :
          g (t • x + (1 - t) • y) = ⊥ := by
        apply hg_eq_bot_of_not_bddBelow
        exact hunbounded_left ht (by linarith) hbx
      simp [hgx, hzbot, ht.ne']
  simpa [g] using hgoal

end «problem-124»
