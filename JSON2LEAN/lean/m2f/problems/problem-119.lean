import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-119»
/-
Let f: ℝ^n → ℝ∪{+∞} be a proper convex function with no value equal to -∞. Define
f̄(x) = sup{g(x): g is affine and g(z) ≤ f(z) for all z}. Prove that f̄ is a global lower envelope
of f. Moreover, for every x in int(dom f), there exists an affine minorant g supporting f at x, so
g(x) = f(x), and consequently f(x) = f̄(x).
-/

/-- Reinterpret the convex `EReal` epigraph as convexity of the finite-valued real function on its
finite domain. -/
lemma dom_toReal_convexOn
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hconv : Convex ℝ {xt : (Fin n → ℝ) × ℝ | f xt.1 ≤ (xt.2 : EReal)})
    (hno_bot : ∀ x : Fin n → ℝ, f x ≠ ⊥) :
    let D : Set (Fin n → ℝ) := {z | f z < ⊤}
    let φ : (Fin n → ℝ) → ℝ := fun z => (f z).toReal
    Convex ℝ D ∧ ConvexOn ℝ D φ := by
  classical
  let D : Set (Fin n → ℝ) := {z | f z < ⊤}
  let φ : (Fin n → ℝ) → ℝ := fun z => (f z).toReal
  constructor
  · -- Finite epigraph points stay in the epigraph under convex combinations, so the domain is convex.
    intro x hx y hy a b ha hb hab
    have hx_epi : (x, φ x) ∈ {xt : (Fin n → ℝ) × ℝ | f xt.1 ≤ (xt.2 : EReal)} := by
      change f x ≤ (((f x).toReal : ℝ) : EReal)
      rw [EReal.coe_toReal hx.ne (hno_bot x)]
    have hy_epi : (y, φ y) ∈ {xt : (Fin n → ℝ) × ℝ | f xt.1 ≤ (xt.2 : EReal)} := by
      change f y ≤ (((f y).toReal : ℝ) : EReal)
      rw [EReal.coe_toReal hy.ne (hno_bot y)]
    have hmem : f (a • x + b • y) ≤ (((a * φ x + b * φ y : ℝ)) : EReal) :=
      hconv hx_epi hy_epi ha hb hab
    have : f (a • x + b • y) < ⊤ := lt_of_le_of_lt hmem (EReal.coe_lt_top _)
    simpa [D, φ, smul_eq_mul]
  · -- The same epigraph conversion gives convexity of the real-valued restriction `φ`.
    refine convexOn_iff_convex_epigraph.2 ?_
    intro p hp q hq a b ha hb hab
    rcases hp with ⟨hpD, hpφ⟩
    rcases hq with ⟨hqD, hqφ⟩
    have hp_epi : (p.1, p.2) ∈ {xt : (Fin n → ℝ) × ℝ | f xt.1 ≤ (xt.2 : EReal)} := by
      change f p.1 ≤ (p.2 : EReal)
      rw [← EReal.coe_toReal hpD.ne (hno_bot p.1)]
      exact_mod_cast hpφ
    have hq_epi : (q.1, q.2) ∈ {xt : (Fin n → ℝ) × ℝ | f xt.1 ≤ (xt.2 : EReal)} := by
      change f q.1 ≤ (q.2 : EReal)
      rw [← EReal.coe_toReal hqD.ne (hno_bot q.1)]
      exact_mod_cast hqφ
    have hmix_le0 : f (a • p.1 + b • q.1) ≤ ↑a * ↑p.2 + ↑b * ↑q.2 :=
      hconv hp_epi hq_epi ha hb hab
    have hmix_le : f (a • p.1 + b • q.1) ≤ ↑(a * p.2 + b * q.2) := by
      simpa [smul_eq_mul] using hmix_le0
    have hmixD : f (a • p.1 + b • q.1) < ⊤ := by
      exact lt_of_le_of_lt hmix_le (EReal.coe_lt_top _)
    refine ⟨hmixD, ?_⟩
    have hmix_coe : ((((f (a • p.1 + b • q.1)).toReal : ℝ) : EReal)) = f (a • p.1 + b • q.1) :=
      EReal.coe_toReal hmixD.ne (hno_bot _)
    have hrealE :
        ((((f (a • p.1 + b • q.1)).toReal : ℝ) : EReal)) ≤ (((a * p.2 + b * q.2 : ℝ)) : EReal) := by
      rw [hmix_coe]
      exact hmix_le
    exact_mod_cast hrealE

/-- A continuous linear functional on `Fin n → ℝ` is given by a dot product with a coefficient
vector. -/
lemma continuousLinearMap_eq_dotProduct
    {n : ℕ} (u : (Fin n → ℝ) →L[ℝ] ℝ) :
    ∃ a : Fin n → ℝ, ∀ z, u z = dotProduct a z := by
  classical
  refine ⟨fun i => u (Pi.single i 1), ?_⟩
  intro z
  rw [show u z = u.toLinearMap z by rfl, LinearMap.pi_apply_eq_sum_univ]
  unfold dotProduct
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [mul_comm]
  have harg : u (fun j => if i = j then 1 else 0) = u (Pi.single i 1) := by
    apply congrArg u
    funext j
    by_cases h : j = i
    · subst h
      simp [Pi.single]
    · simp [Pi.single, h, Ne.symm h]
  simpa using congrArg (fun t => z i * t) harg

/-- Separating a point from the strict epigraph over a ball yields a local affine support there. -/
lemma local_affine_support_on_ball
    {n : ℕ} {φ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hφconv : ConvexOn ℝ (Metric.ball x r) φ)
    (hφcont : ContinuousOn φ (Metric.ball x r)) :
    ∃ v : StrongDual ℝ (Fin n → ℝ), ∃ c : ℝ,
      v x + c = φ x ∧ ∀ z ∈ Metric.ball x r, v z + c ≤ φ z := by
  let T : Set ((Fin n → ℝ) × ℝ) := {p | p.1 ∈ Metric.ball x r ∧ φ p.1 < p.2}
  have hTconv : Convex ℝ T := by
    -- The strict epigraph of a convex function is convex.
    simpa [T] using hφconv.convex_strict_epigraph
  have hcont_prod : ContinuousOn (fun p : (Fin n → ℝ) × ℝ => φ p.1 - p.2)
      (Prod.fst ⁻¹' Metric.ball x r) := by
    -- Compose the continuity of `φ` on the ball with the first projection, then subtract the height.
    have hφfst : ContinuousOn (fun p : (Fin n → ℝ) × ℝ => φ p.1)
        (Prod.fst ⁻¹' Metric.ball x r) :=
      hφcont.comp continuous_fst.continuousOn (by intro p hp; exact hp)
    exact hφfst.sub continuous_snd.continuousOn
  have hTopen : IsOpen T := by
    -- Openness comes from continuity of `(z,t) ↦ φ z - t` on the open base `ball x r`.
    have hopen_base : IsOpen (Prod.fst ⁻¹' Metric.ball x r) :=
      (Metric.isOpen_ball : IsOpen (Metric.ball x r)).preimage
        (continuous_fst : Continuous (Prod.fst : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ)))
    have hopen_pre : IsOpen ((Prod.fst ⁻¹' Metric.ball x r) ∩
        (fun p : (Fin n → ℝ) × ℝ => φ p.1 - p.2) ⁻¹' Set.Iio 0) :=
      hcont_prod.isOpen_inter_preimage hopen_base isOpen_Iio
    have hT : T = ((Prod.fst ⁻¹' Metric.ball x r) ∩
        (fun p : (Fin n → ℝ) × ℝ => φ p.1 - p.2) ⁻¹' Set.Iio 0) := by
      ext p
      simp [T, Metric.ball, sub_lt_iff_lt_add, add_comm]
    rw [hT]
    exact hopen_pre
  have hxnot : (x, φ x) ∉ T := by
    -- The boundary point itself is not in the strict epigraph.
    simp [T]
  obtain ⟨L, hsep⟩ := geometric_hahn_banach_point_open (x := (x, φ x)) hTconv hTopen hxnot
  let u : StrongDual ℝ (Fin n → ℝ) := L.comp (.inl ℝ (Fin n → ℝ) ℝ)
  let α : ℝ := L (0, 1)
  have hzero (t : ℝ) : L (0, t) = t * α := by
    -- Evaluate the separator on the vertical line through the origin.
    have hsmul : ((0 : Fin n → ℝ), t) = t • ((0 : Fin n → ℝ), (1 : ℝ)) := by ext <;> simp
    rw [hsmul, map_smul]
    simp [α, smul_eq_mul]
  have happly (z : Fin n → ℝ) (t : ℝ) : L (z, t) = u z + α * t := by
    -- Split every point into its horizontal and vertical components.
    have hpair : (z, t) = (z, 0) + ((0 : Fin n → ℝ), t) := by ext <;> simp
    rw [hpair, map_add, hzero]
    simp [u, α, mul_comm]
  have hαpos : 0 < α := by
    -- Route correction: using the vertical test point avoids the old normalization dead-end.
    have hxsep : L (x, φ x) < L (x, φ x + 1) :=
      hsep _ ⟨Metric.mem_ball_self hr, by linarith⟩
    rw [happly, happly] at hxsep
    linarith
  let v : StrongDual ℝ (Fin n → ℝ) := (-α⁻¹ : ℝ) • u
  let c : ℝ := φ x + α⁻¹ * u x
  refine ⟨v, c, ?_, ?_⟩
  · -- The affine function is exact at the supporting point.
    simp [v, c]
  · intro z hz
    -- Separating `(x, φ x)` from `(z, φ z + ε)` gives the local inequality after dividing by `α`.
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    have hzsep : L (x, φ x) < L (z, φ z + ε) := hsep _ ⟨hz, by linarith⟩
    rw [happly, happly] at hzsep
    have hleft : α * (φ x + α⁻¹ * u x) = u x + α * φ x := by
      field_simp [hαpos.ne']
      ring_nf
    have hright : α * (φ z + ε + α⁻¹ * u z) = u z + α * (φ z + ε) := by
      field_simp [hαpos.ne']
      ring_nf
    have hdiv : φ x + α⁻¹ * u x < φ z + ε + α⁻¹ * u z := by
      apply lt_of_mul_lt_mul_left
      · rw [hleft, hright]
        exact hzsep
      · exact hαpos.le
    have hvz : v z + c = φ x + α⁻¹ * u x - α⁻¹ * u z := by
      simp [v, c, sub_eq_add_neg, smul_eq_mul, add_comm, add_assoc, mul_comm]
    rw [hvz]
    linarith

theorem convex_eq_sSup_affine_minorants_on_interior_dom
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hconv : Convex ℝ {xt : (Fin n → ℝ) × ℝ | f xt.1 ≤ (xt.2 : EReal)})
    (hproper : ∃ x : Fin n → ℝ, f x < ⊤)
    (hno_bot : ∀ x : Fin n → ℝ, f x ≠ ⊥) :
    let affineMinorants : Set ((Fin n → ℝ) → ℝ) :=
      {h : ((Fin n → ℝ) → ℝ) |
        (∃ a : Fin n → ℝ, ∃ b : ℝ, ∀ z : Fin n → ℝ, h z = dotProduct a z + b) ∧
        ∀ z : Fin n → ℝ, (h z : EReal) ≤ f z}
    let fBar : (Fin n → ℝ) → EReal :=
      fun x => sSup ((fun h : ((Fin n → ℝ) → ℝ) => ((h x : ℝ) : EReal)) '' affineMinorants)
    (∀ x : Fin n → ℝ, fBar x ≤ f x) ∧
      ∀ x ∈ interior {z | f z < ⊤},
        (∃ h : ((Fin n → ℝ) → ℝ),
          h ∈ affineMinorants ∧ ((h x : ℝ) : EReal) = f x) ∧
        f x = fBar x := by
  classical
  let _ := hproper
  let affineMinorants : Set ((Fin n → ℝ) → ℝ) :=
    {h : ((Fin n → ℝ) → ℝ) |
      (∃ a : Fin n → ℝ, ∃ b : ℝ, ∀ z : Fin n → ℝ, h z = dotProduct a z + b) ∧
      ∀ z : Fin n → ℝ, (h z : EReal) ≤ f z}
  let fBar : (Fin n → ℝ) → EReal :=
    fun x => sSup ((fun h : ((Fin n → ℝ) → ℝ) => ((h x : ℝ) : EReal)) '' affineMinorants)
  let D : Set (Fin n → ℝ) := {z | f z < ⊤}
  let φ : (Fin n → ℝ) → ℝ := fun z => (f z).toReal
  have hDconv : Convex ℝ D := (dom_toReal_convexOn f hconv hno_bot).1
  have hφconv : ConvexOn ℝ D φ := (dom_toReal_convexOn f hconv hno_bot).2
  have hφcont : ContinuousOn φ (interior D) := hφconv.continuousOn_interior
  have hlowerEnvelope : ∀ x : Fin n → ℝ, fBar x ≤ f x := by
    intro x
    -- Every affine minorant contributes a value below `f x`, so the supremum stays below `f x`.
    refine sSup_le ?_
    rintro _ ⟨h, hh, rfl⟩
    exact hh.2 x
  change (∀ x : Fin n → ℝ, fBar x ≤ f x) ∧
      ∀ x ∈ interior D,
        (∃ h : ((Fin n → ℝ) → ℝ),
          h ∈ affineMinorants ∧ ((h x : ℝ) : EReal) = f x) ∧
        f x = fBar x
  constructor
  · exact hlowerEnvelope
  · intro x hx
    have hxD : x ∈ D := interior_subset hx
    have hxNhds : interior D ∈ 𝓝 x := IsOpen.mem_nhds isOpen_interior hx
    obtain ⟨r, hr, hrsub⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ interior D :=
      Metric.nhds_basis_closedBall.mem_iff.1 hxNhds
    have hballInt : Metric.ball x r ⊆ interior D := fun y hy => hrsub (Metric.ball_subset_closedBall hy)
    have hballD : Metric.ball x r ⊆ D := fun y hy => interior_subset (hballInt hy)
    have hφconv_ball : ConvexOn ℝ (Metric.ball x r) φ := hφconv.subset hballD (convex_ball x r)
    have hφcont_ball : ContinuousOn φ (Metric.ball x r) := hφcont.mono hballInt
    obtain ⟨v, c, hvx, hvball⟩ := local_affine_support_on_ball hr hφconv_ball hφcont_ball
    let h : (Fin n → ℝ) → ℝ := fun z => v z + c
    have hhx : h x = φ x := hvx
    have hconc : ConcaveOn ℝ D h := (v.toLinearMap.concaveOn hDconv).add_const c
    have hgap_conv : ConvexOn ℝ D (fun z => φ z - h z) := hφconv.sub hconc
    have hlocalMin : IsLocalMinOn (fun z => φ z - h z) D x := by
      have hballNhds : Metric.ball x r ∈ 𝓝[D] x :=
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hr)
      have hmin_inter : IsMinOn (fun z => φ z - h z) (D ∩ Metric.ball x r) x := by
        intro z hz
        rcases hz with ⟨_, hzball⟩
        have hsub : 0 ≤ φ z - h z := sub_nonneg.mpr (hvball z hzball)
        simpa [h, hhx] using hsub
      have hlocal_inter : IsLocalMinOn (fun z => φ z - h z) (D ∩ Metric.ball x r) x :=
        hmin_inter.localize
      have hnhds_eq : 𝓝[D ∩ Metric.ball x r] x = 𝓝[D] x := nhdsWithin_inter_of_mem' hballNhds
      simpa [IsLocalMinOn, hnhds_eq] using hlocal_inter
    have hglobalMin : IsMinOn (fun z => φ z - h z) D x :=
      IsMinOn.of_isLocalMinOn_of_convexOn hxD hlocalMin hgap_conv
    have hminor_real : ∀ z ∈ D, h z ≤ φ z := by
      intro z hzD
      have hsub : 0 ≤ φ z - h z := by
        simpa [h, hhx] using hglobalMin hzD
      exact sub_nonneg.mp hsub
    have hminor_ereal : ∀ z : Fin n → ℝ, (h z : EReal) ≤ f z := by
      intro z
      by_cases hzTop : f z = ⊤
      · simp [hzTop]
      · have hzD : z ∈ D := lt_of_le_of_ne le_top hzTop
        rw [← EReal.coe_toReal hzTop (hno_bot z)]
        exact_mod_cast hminor_real z hzD
    obtain ⟨a, ha⟩ := continuousLinearMap_eq_dotProduct v
    have hmem : h ∈ affineMinorants := by
      refine ⟨?_, hminor_ereal⟩
      exact ⟨a, c, fun z => by simp [h, ha z]⟩
    have hxeq : ((h x : ℝ) : EReal) = f x := by
      rw [hhx, EReal.coe_toReal hxD.ne (hno_bot x)]
    have hxle : f x ≤ fBar x := by
      calc
        f x = ((h x : ℝ) : EReal) := hxeq.symm
        _ ≤ fBar x := le_sSup ⟨h, hmem, rfl⟩
    exact ⟨⟨h, hmem, hxeq⟩, le_antisymm hxle (hlowerEnvelope x)⟩

end «problem-119»
