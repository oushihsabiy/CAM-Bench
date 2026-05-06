import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-92»

/- [BLOCK Exercise 3.39-(d) | 24 | defn]
A function f : ℝ^n → ℝ ∪ {+∞} is a closed convex function if its epigraph is closed and convex.
-/
def IsClosedConvexFunction {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  IsClosed {p : (Fin n → ℝ) × ℝ | f p.1 ≤ (p.2 : EReal)} ∧
  Convex ℝ {p : (Fin n → ℝ) × ℝ | f p.1 ≤ (p.2 : EReal)}

/- [BLOCK Exercise 3.39-(d) | 26 | defn]
The convex conjugate of f : ℝ^n → ℝ cup {+∞} is the function f* : ℝ^n → ℝ cup {+∞} defined by
f*(y)=sup_x∈ ℝ^n(yᵀ x-f(x)).
-/
def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup {z : EReal | ∃ x : Fin n → ℝ, z = (∑ i, y i * x i : ℝ) - f x}

/- [BLOCK Exercise 3.39-(d) | 27 | defn]
The biconjugate of f is the convex conjugate of f*; equivalently, f** : ℝ^n → ℝ cup {+∞} is
defined by
f* * (x)=sup_y∈ ℝ^n(yᵀ x-f*(y)).
-/
def biconjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  convexConjugate (convexConjugate f)

/-- The affine function with slope `y` and offset `c`. -/
def affineEval {n : ℕ} (y : Fin n → ℝ) (c : ℝ) (z : Fin n → ℝ) : ℝ :=
  (∑ i, y i * z i : ℝ) - c

/-- A continuous linear functional on `Fin n → ℝ` is the sum of its coordinate values against the
standard basis. -/
lemma linear_apply_eq_sum {n : ℕ} (u : StrongDual ℝ (Fin n → ℝ)) (z : Fin n → ℝ) :
    u z = ∑ i, u (Pi.basisFun ℝ (Fin n) i) * z i := by
  -- Evaluate the dual-basis expansion at the point `z`.
  have hdual := (Pi.basisFun ℝ (Fin n)).sum_dual_apply_smul_coord u.toLinearMap
  have hz := congrArg (fun f : Module.Dual ℝ (Fin n → ℝ) => f z) hdual
  simpa [Pi.basisFun_repr, smul_eq_mul, mul_comm] using hz.symm

/-- The affine function attached to a scaled linear functional has the expected closed form. -/
lemma affineEval_of_scaledLinear {n : ℕ} (u : StrongDual ℝ (Fin n → ℝ)) (lam c : ℝ)
    (z : Fin n → ℝ) :
    affineEval (fun i => lam * u (Pi.basisFun ℝ (Fin n) i)) c z = lam * u z - c := by
  -- Rewrite the coordinate sum back into the linear functional itself.
  unfold affineEval
  calc
    (∑ i, (lam * u (Pi.basisFun ℝ (Fin n) i)) * z i : ℝ) - c
        = (lam * u z) - c := by
          congr 1
          calc
            (∑ i, (lam * u (Pi.basisFun ℝ (Fin n) i)) * z i : ℝ)
                = ∑ i, lam * (u (Pi.basisFun ℝ (Fin n) i) * z i) := by simp [mul_assoc]
            _ = lam * ∑ i, u (Pi.basisFun ℝ (Fin n) i) * z i := by rw [Finset.mul_sum]
            _ = lam * u z := by rw [linear_apply_eq_sum]

/-- Adding a scaled linear functional to an affine minorant updates the value by the corresponding
linear correction term. -/
lemma affineEval_add_scaledLinear {n : ℕ} (y : Fin n → ℝ) (c : ℝ)
    (u : StrongDual ℝ (Fin n → ℝ)) (lam s : ℝ) (z : Fin n → ℝ) :
    affineEval (fun i => y i + lam * u (Pi.basisFun ℝ (Fin n) i)) (c + lam * s) z =
      affineEval y c z + lam * (u z - s) := by
  -- Split the sum into the old affine part and the new linear correction.
  unfold affineEval
  rw [show (∑ i, (y i + lam * u (Pi.basisFun ℝ (Fin n) i)) * z i : ℝ) =
      (∑ i, y i * z i : ℝ) + ∑ i, (lam * u (Pi.basisFun ℝ (Fin n) i)) * z i by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]]
  rw [show (∑ i, (lam * u (Pi.basisFun ℝ (Fin n) i)) * z i : ℝ) = lam * u z by
      calc
        (∑ i, (lam * u (Pi.basisFun ℝ (Fin n) i)) * z i : ℝ)
            = ∑ i, lam * (u (Pi.basisFun ℝ (Fin n) i) * z i) := by simp [mul_assoc]
        _ = lam * ∑ i, u (Pi.basisFun ℝ (Fin n) i) * z i := by rw [Finset.mul_sum]
        _ = lam * u z := by rw [linear_apply_eq_sum]]
  ring

/-- Any affine minorant bounds the convex conjugate from above by its offset. -/
lemma convexConjugate_le_of_affine_minorant
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {y : Fin n → ℝ} {c : ℝ}
    (hminor : ∀ z, ((affineEval y c z : ℝ) : EReal) ≤ f z) :
    convexConjugate f y ≤ c := by
  -- Every witness in the defining supremum is bounded by the affine offset.
  unfold convexConjugate
  refine sSup_le ?_
  intro r hr
  rcases hr with ⟨z, rfl⟩
  have hsum : (((∑ i, y i * z i : ℝ) : EReal) ≤ (c : EReal) + f z) := by
    simpa [affineEval, add_comm] using
      (EReal.sub_le_iff_le_add (.inl (by simp : (c : EReal) ≠ ⊥))
        (.inl (by simp : (c : EReal) ≠ ⊤))).1 (hminor z)
  simpa [add_comm] using (EReal.sub_le_of_le_add hsum)

/-- A separator with negative vertical coefficient yields an affine minorant taking the prescribed
value at the distinguished point. -/
lemma affine_minorant_of_negative_separator
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hnoBot : ∀ z, f z ≠ ⊥)
    {x : Fin n → ℝ} {a : ℝ}
    (u : StrongDual ℝ (Fin n → ℝ)) (α : ℝ)
    (hαneg : α < 0)
    (hpoint : ∀ z, f z ≠ ⊤ → u z + α * (f z).toReal < u x + α * a) :
    ∃ y : Fin n → ℝ, ∃ c : ℝ,
      (∀ z, ((affineEval y c z : ℝ) : EReal) ≤ f z) ∧
      (((affineEval y c x : ℝ) : EReal) = a) := by
  let lam : ℝ := (-α)⁻¹
  have hlamα : lam * α = -1 := by
    -- Route correction: the negative-slope branch should divide by `-α`, not by `α`.
    have hαne : α ≠ 0 := ne_of_lt hαneg
    calc
      lam * α = ((-α)⁻¹ : ℝ) * α := by rfl
      _ = -1 := by field_simp [hαne]
  refine ⟨fun i => lam * u (Pi.basisFun ℝ (Fin n) i), lam * u x - a, ?_, ?_⟩
  · intro z
    -- If `f z` is finite, the negative-slope separator turns into a real inequality; if `f z = ⊤`,
    -- the affine bound is automatic.
    by_cases hzTop : f z = ⊤
    · simp [hzTop, affineEval]
    · have hrealMinor : lam * u z - (lam * u x - a) < (f z).toReal := by
        have hmul : lam * (u z + α * (f z).toReal) < lam * (u x + α * a) := by
          have hlam_pos : 0 < lam := by simp [lam, hαneg]
          exact mul_lt_mul_of_pos_left (hpoint z hzTop) hlam_pos
        have h1 : lam * (α * (f z).toReal) = -(f z).toReal := by
          calc
            lam * (α * (f z).toReal) = (lam * α) * (f z).toReal := by ring
            _ = -(f z).toReal := by rw [hlamα]; ring
        have h2 : lam * (α * a) = -a := by
          calc
            lam * (α * a) = (lam * α) * a := by ring
            _ = -a := by rw [hlamα]; ring
        rw [mul_add, mul_add, h1, h2] at hmul
        linarith
      have hsum : (((affineEval (fun i => lam * u (Pi.basisFun ℝ (Fin n) i)) (lam * u x - a) z :
          ℝ) : EReal) ≤ ((f z).toReal : EReal)) := by
        have hsum_real :
            affineEval (fun i => lam * u (Pi.basisFun ℝ (Fin n) i)) (lam * u x - a) z <
              (f z).toReal := by
          rw [affineEval_of_scaledLinear]
          exact hrealMinor
        exact_mod_cast hsum_real.le
      simpa [hzTop, EReal.coe_toReal hzTop (hnoBot z)] using hsum
  · -- Evaluate the constructed affine function at the distinguished point.
    have hxeq_real :
        affineEval (fun i => lam * u (Pi.basisFun ℝ (Fin n) i)) (lam * u x - a) x = a := by
      rw [affineEval_of_scaledLinear]
      ring
    exact_mod_cast hxeq_real

/-- A horizontal separator, combined with one global affine minorant, can be tilted into an affine
minorant that reaches any prescribed finite level at the distinguished point. -/
lemma affine_minorant_of_horizontal_separator
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hnoBot : ∀ z, f z ≠ ⊥)
    {x : Fin n → ℝ} {a s : ℝ}
    (u : StrongDual ℝ (Fin n → ℝ))
    (hsx : s < u x)
    {y₀ : Fin n → ℝ} {c₀ : ℝ}
    (hglobal : ∀ z, ((affineEval y₀ c₀ z : ℝ) : EReal) ≤ f z)
    (hu : ∀ z, f z ≠ ⊤ → u z < s) :
    ∃ y : Fin n → ℝ, ∃ c : ℝ,
      (∀ z, ((affineEval y c z : ℝ) : EReal) ≤ f z) ∧
      ((a : EReal) ≤ ((affineEval y c x : ℝ) : EReal)) := by
  let gx : ℝ := affineEval y₀ c₀ x
  let lam : ℝ := max 0 ((a - gx) / (u x - s)) + 1
  have huxs : 0 < u x - s := sub_pos.mpr hsx
  have hlam_pos : 0 < lam := by
    -- Choose `lam` strictly larger than the threshold needed to push the value at `x` past `a`.
    dsimp [lam]
    linarith [le_max_left 0 ((a - gx) / (u x - s))]
  have hlam_gt : ((a - gx) / (u x - s)) < lam := by
    dsimp [lam]
    linarith [le_max_right 0 ((a - gx) / (u x - s))]
  have hxvalue : a < gx + lam * (u x - s) := by
    have hmul' := mul_lt_mul_of_pos_right hlam_gt huxs
    have hne : u x - s ≠ 0 := ne_of_gt huxs
    have hdiv : ((a - gx) / (u x - s)) * (u x - s) = a - gx := by
      field_simp [hne]
    have hmul : a - gx < lam * (u x - s) := by
      simpa [hdiv] using hmul'
    linarith
  refine ⟨fun i => y₀ i + lam * u (Pi.basisFun ℝ (Fin n) i), c₀ + lam * s, ?_, ?_⟩
  · intro z
    -- Finite points sit strictly below the horizontal separator, so adding the correction term
    -- only pushes the global minorant downward.
    by_cases hzTop : f z = ⊤
    · simp [hzTop]
    · have hglobal_real : affineEval y₀ c₀ z ≤ (f z).toReal := by
        have htmp : (((affineEval y₀ c₀ z : ℝ) : EReal) ≤ ((f z).toReal : EReal)) := by
          simpa [EReal.coe_toReal hzTop (hnoBot z)] using hglobal z
        exact_mod_cast htmp
      have hreal : affineEval y₀ c₀ z + lam * (u z - s) < (f z).toReal := by
        have hu_lt : u z - s < 0 := sub_lt_zero.mpr (hu z hzTop)
        have hdrop : lam * (u z - s) < 0 := mul_neg_of_pos_of_neg hlam_pos hu_lt
        linarith
      have hfinal :
          (((affineEval y₀ c₀ z + lam * (u z - s) : ℝ) : EReal) ≤
            ((f z).toReal : EReal)) := by
        exact_mod_cast hreal.le
      rw [← affineEval_add_scaledLinear] at hfinal
      simpa [hzTop, EReal.coe_toReal hzTop (hnoBot z)] using hfinal
  · -- The chosen `lam` makes the corrected affine function reach the target level at `x`.
    have hxreal :
        a < affineEval (fun i => y₀ i + lam * u (Pi.basisFun ℝ (Fin n) i)) (c₀ + lam * s) x := by
      rw [affineEval_add_scaledLinear]
      simpa [gx] using hxvalue
    exact_mod_cast hxreal.le

/-- At a finite point, a strict epigraph separator produces an affine minorant with prescribed
value. -/
lemma finite_support
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hclosedConv : IsClosedConvexFunction f)
    (hnoBot : ∀ x, f x ≠ ⊥)
    {x : Fin n → ℝ} (hxTop : f x ≠ ⊤)
    {a : ℝ} (ha : (a : EReal) < f x) :
    ∃ y : Fin n → ℝ, ∃ c : ℝ,
      (∀ z, ((affineEval y c z : ℝ) : EReal) ≤ f z) ∧
      (((affineEval y c x : ℝ) : EReal) = a) := by
  let A : Set ((Fin n → ℝ) × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}
  have hnotin : (x, a) ∉ A := by
    -- The point lies strictly below the epigraph height at `x`.
    simp [A, ha.not_ge]
  obtain ⟨L, s, hsep, hsx⟩ :=
    geometric_hahn_banach_closed_point hclosedConv.2 hclosedConv.1 hnotin
  let u : StrongDual ℝ (Fin n → ℝ) := L.comp (.inl ℝ (Fin n → ℝ) ℝ)
  let α : ℝ := L (0, 1)
  have hzero (t : ℝ) : L (0, t) = t * α := by
    -- Decompose the separator along the vertical direction.
    have hsmul : ((0 : Fin n → ℝ), t) = t • ((0 : Fin n → ℝ), (1 : ℝ)) := by ext <;> simp
    rw [hsmul, map_smul]
    simp [α, smul_eq_mul]
  have happly (z : Fin n → ℝ) (t : ℝ) : L (z, t) = u z + α * t := by
    -- Every value of the separator splits into horizontal and vertical components.
    have hpair : (z, t) = (z, 0) + ((0 : Fin n → ℝ), t) := by ext <;> simp
    rw [hpair, map_add, hzero]
    simp [u, α, mul_comm]
  have hxmem : (x, (f x).toReal) ∈ A := by
    -- The finite point `(x, f x)` belongs to the epigraph.
    simp [A, EReal.coe_toReal hxTop (hnoBot x)]
  have hxlt : u x + α * (f x).toReal < s := by
    have htmp : L (x, (f x).toReal) < s := hsep _ hxmem
    rw [happly] at htmp
    exact htmp
  have hsx' : s < u x + α * a := by
    rw [happly] at hsx
    exact hsx
  have hrealE : (a : EReal) < ((f x).toReal : EReal) := by
    simpa [EReal.coe_toReal hxTop (hnoBot x)] using ha
  have hreal : a < (f x).toReal := by
    exact_mod_cast hrealE
  have hαneg : α < 0 := by
    -- Comparing the separator at `(x, a)` and `(x, f x)` forces a negative vertical coefficient.
    by_contra hαneg
    have hαnonneg : 0 ≤ α := le_of_not_gt hαneg
    have hmul : α * a ≤ α * (f x).toReal := mul_le_mul_of_nonneg_left hreal.le hαnonneg
    have hlt : α * (f x).toReal < α * a := by
      linarith
    exact (not_le_of_gt hlt) hmul
  have hpoint : ∀ z, f z ≠ ⊤ → u z + α * (f z).toReal < u x + α * a := by
    intro z hzTop
    have hzmem : (z, (f z).toReal) ∈ A := by
      simp [A, EReal.coe_toReal hzTop (hnoBot z)]
    have hzlt : u z + α * (f z).toReal < s := by
      have htmp : L (z, (f z).toReal) < s := hsep _ hzmem
      rw [happly] at htmp
      exact htmp
    exact lt_trans hzlt hsx'
  exact affine_minorant_of_negative_separator hnoBot u α hαneg hpoint

/- [BLOCK Exercise 3.39-(d) | 28 | thm]
Let f:ℝ^n → ℝ+∞ be a closed convex function, where closed means that epi(f)={(x,t)∈ ℝ^n× ℝ| f(x)≤ t}
is a closed subset of ℝ^n× ℝ. Define the convex conjugate f*:ℝ^n→ ℝ+∞ by f*(y)=sup_{x∈ ℝ^n}(yᵀ
x-f(x)), and define the biconjugate f^{ ** }:ℝ^n→ ℝ+∞ by f^{** }(x)=sup_{y∈ ℝ^n}(yᵀ x-f*(y)). Show
that
f=f^{**}.
-/
theorem closed_convex_function_eq_biconjugate {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hclosedConv : IsClosedConvexFunction f)
    (hnoBot : ∀ x, f x ≠ ⊥)
    (hproper : ∃ x, f x < ⊤) :
    f = biconjugate f := by
  -- Route correction: the proof must split finite points from `⊤`-valued points; the old single
  -- separator route implicitly assumed a positive vertical coefficient everywhere.
  ext x
  apply le_antisymm
  · by_cases hxTop : f x = ⊤
    · -- At a `⊤`-valued point, force arbitrarily large affine minorants and hence `f** x = ⊤`.
      have hglobal : ∃ y₀ : Fin n → ℝ, ∃ c₀ : ℝ,
          ∀ z, ((affineEval y₀ c₀ z : ℝ) : EReal) ≤ f z := by
        obtain ⟨x₀, hx₀fin⟩ := hproper
        have hx₀Top : f x₀ ≠ ⊤ := ne_of_lt hx₀fin
        have ha₀ : ((((f x₀).toReal - 1 : ℝ) : EReal) < f x₀) := by
          have hstep :
              ((((f x₀).toReal - 1 : ℝ) : EReal) < (((f x₀).toReal : ℝ) : EReal)) := by
            exact_mod_cast sub_lt_self ((f x₀).toReal) zero_lt_one
          simpa [EReal.coe_toReal hx₀Top (hnoBot x₀)] using hstep
        obtain ⟨y₀, c₀, hminor, _⟩ := finite_support hclosedConv hnoBot hx₀Top ha₀
        exact ⟨y₀, c₀, hminor⟩
      have hbicTop : biconjugate f x = ⊤ := by
        refine (EReal.eq_top_iff_forall_lt (biconjugate f x)).2 ?_
        intro a
        let b : ℝ := a + 1
        let A : Set ((Fin n → ℝ) × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}
        have hnotin : (x, b) ∉ A := by
          -- No finite height belongs to the epigraph above a `⊤`-valued point.
          simp [A, hxTop]
        obtain ⟨L, s, hsep, hsx⟩ :=
          geometric_hahn_banach_closed_point hclosedConv.2 hclosedConv.1 hnotin
        let u : StrongDual ℝ (Fin n → ℝ) := L.comp (.inl ℝ (Fin n → ℝ) ℝ)
        let α : ℝ := L (0, 1)
        have hzero (t : ℝ) : L (0, t) = t * α := by
          -- Decompose the separator along the vertical line.
          have hsmul : ((0 : Fin n → ℝ), t) = t • ((0 : Fin n → ℝ), (1 : ℝ)) := by ext <;> simp
          rw [hsmul, map_smul]
          simp [α, smul_eq_mul]
        have happly (z : Fin n → ℝ) (t : ℝ) : L (z, t) = u z + α * t := by
          -- Split the separator into horizontal and vertical parts.
          have hpair : (z, t) = (z, 0) + ((0 : Fin n → ℝ), t) := by ext <;> simp
          rw [hpair, map_add, hzero]
          simp [u, α, mul_comm]
        have hαnonpos : α ≤ 0 := by
          -- Upward closure of the epigraph forbids a positive vertical coefficient.
          obtain ⟨x₀, hx₀fin⟩ := hproper
          have hx₀Top : f x₀ ≠ ⊤ := ne_of_lt hx₀fin
          by_contra hαpos
          have hαpos' : 0 < α := lt_of_not_ge hαpos
          let t : ℝ := max (f x₀).toReal (((s - u x₀) / α) + 1)
          have ht_mem : (x₀, t) ∈ A := by
            change f x₀ ≤ (t : EReal)
            calc
              f x₀ = (((f x₀).toReal : ℝ) : EReal) := by rw [EReal.coe_toReal hx₀Top (hnoBot x₀)]
              _ ≤ (t : EReal) := by
                exact_mod_cast le_max_left (f x₀).toReal (((s - u x₀) / α) + 1)
          have hlt : u x₀ + α * t < s := by
            have htmp : L (x₀, t) < s := hsep _ ht_mem
            rw [happly] at htmp
            exact htmp
          have hthreshold : ((s - u x₀) / α) + 1 ≤ t := le_max_right _ _
          have hgt : s < u x₀ + α * t := by
            have hbase : s < u x₀ + α * (((s - u x₀) / α) + 1) := by
              have hαne : α ≠ 0 := ne_of_gt hαpos'
              field_simp [hαne]
              nlinarith
            have hmono : u x₀ + α * (((s - u x₀) / α) + 1) ≤ u x₀ + α * t := by
              gcongr
            exact lt_of_lt_of_le hbase hmono
          exact (not_lt_of_ge hlt.le) hgt
        rcases hglobal with ⟨y₀, c₀, hglobal_minorant⟩
        rcases lt_or_eq_of_le hαnonpos with hαneg | hαzero
        · -- A genuinely negative vertical coefficient gives an exact supporting affine function.
          have hsx' : s < u x + α * b := by
            rw [happly] at hsx
            exact hsx
          have hpoint : ∀ z, f z ≠ ⊤ → u z + α * (f z).toReal < u x + α * b := by
            intro z hzTop
            have hzmem : (z, (f z).toReal) ∈ A := by
              simp [A, EReal.coe_toReal hzTop (hnoBot z)]
            have hzlt : u z + α * (f z).toReal < s := by
              have htmp : L (z, (f z).toReal) < s := hsep _ hzmem
              rw [happly] at htmp
              exact htmp
            exact lt_trans hzlt hsx'
          obtain ⟨y, c, hminor, hxeq⟩ :=
            affine_minorant_of_negative_separator hnoBot u α hαneg hpoint
          have hconj : convexConjugate f y ≤ c := convexConjugate_le_of_affine_minorant hminor
          have hvalue :
              (((affineEval y c x : ℝ) : EReal) ≤
                (((∑ i, y i * x i : ℝ) : EReal) - convexConjugate f y)) := by
            simpa [affineEval] using EReal.sub_le_sub le_rfl hconj
          have hbic :
              (((∑ i, y i * x i : ℝ) : EReal) - convexConjugate f y) ≤ biconjugate f x := by
            -- Insert this affine function's slope into the outer supremum.
            unfold biconjugate convexConjugate
            exact le_sSup ⟨y, by simp [mul_comm]⟩
          have hb_le : (b : EReal) ≤ biconjugate f x := by
            calc
              (b : EReal) = ((affineEval y c x : ℝ) : EReal) := hxeq.symm
              _ ≤ (((∑ i, y i * x i : ℝ) : EReal) - convexConjugate f y) := hvalue
              _ ≤ biconjugate f x := hbic
          have hab : (a : EReal) < (b : EReal) := by
            exact_mod_cast (show a < b by simp [b])
          exact lt_of_lt_of_le hab hb_le
        · -- If the separator is horizontal, add a scaled copy of it to a global affine minorant.
          have hsx0 : s < u x := by
            rw [happly] at hsx
            simpa [hαzero] using hsx
          have hu0 : ∀ z, f z ≠ ⊤ → u z < s := by
            intro z hzTop
            have hzmem : (z, (f z).toReal) ∈ A := by
              simp [A, EReal.coe_toReal hzTop (hnoBot z)]
            have htmp : L (z, (f z).toReal) < s := hsep _ hzmem
            rw [happly] at htmp
            simpa [hαzero] using htmp
          obtain ⟨y, c, hminor, hxle⟩ :=
            affine_minorant_of_horizontal_separator hnoBot (x := x) (a := b) u hsx0
              hglobal_minorant hu0
          have hconj : convexConjugate f y ≤ c := convexConjugate_le_of_affine_minorant hminor
          have hvalue :
              (((affineEval y c x : ℝ) : EReal) ≤
                (((∑ i, y i * x i : ℝ) : EReal) - convexConjugate f y)) := by
            simpa [affineEval] using EReal.sub_le_sub le_rfl hconj
          have hbic :
              (((∑ i, y i * x i : ℝ) : EReal) - convexConjugate f y) ≤ biconjugate f x := by
            unfold biconjugate convexConjugate
            exact le_sSup ⟨y, by simp [mul_comm]⟩
          have hab : (a : EReal) < (b : EReal) := by
            exact_mod_cast (show a < b by simp [b])
          exact lt_of_lt_of_le hab (hxle.trans (hvalue.trans hbic))
      rw [hxTop]
      simp [hbicTop]
    · -- At a finite point, a supporting affine minorant forces the reverse inequality.
      by_contra hlt
      have hlt' : biconjugate f x < f x := lt_of_not_ge hlt
      obtain ⟨a, ha₁, ha₂⟩ := EReal.exists_between_coe_real hlt'
      obtain ⟨y, c, hminor, hxeq⟩ := finite_support hclosedConv hnoBot hxTop ha₂
      have hconj : convexConjugate f y ≤ c := convexConjugate_le_of_affine_minorant hminor
      have hvalue :
          (((affineEval y c x : ℝ) : EReal) ≤
            (((∑ i, y i * x i : ℝ) : EReal) - convexConjugate f y)) := by
        simpa [affineEval] using EReal.sub_le_sub le_rfl hconj
      have hbic :
          (((∑ i, y i * x i : ℝ) : EReal) - convexConjugate f y) ≤ biconjugate f x := by
        -- Insert the supporting slope into the defining supremum of `f** x`.
        unfold biconjugate convexConjugate
        exact le_sSup ⟨y, by simp [mul_comm]⟩
      have : (a : EReal) ≤ biconjugate f x := by
        calc
          (a : EReal) = ((affineEval y c x : ℝ) : EReal) := hxeq.symm
          _ ≤ (((∑ i, y i * x i : ℝ) : EReal) - convexConjugate f y) := hvalue
          _ ≤ biconjugate f x := hbic
      exact ha₁.not_ge this
  · -- Fenchel-Young gives the universal upper bound `f** x ≤ f x`.
    unfold biconjugate convexConjugate
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨y, rfl⟩
    by_cases hxTop : f x = ⊤
    · simp [hxTop]
    · have hw : (((∑ i, y i * x i : ℝ) : EReal) - f x) ≤ convexConjugate f y := by
        -- Use `x` itself as a witness in the supremum defining the conjugate.
        unfold convexConjugate
        exact le_sSup ⟨x, by simp [mul_comm]⟩
      have hsum : (((∑ i, y i * x i : ℝ) : EReal) ≤ convexConjugate f y + f x) := by
        exact (EReal.sub_le_iff_le_add (.inl (hnoBot x)) (.inl hxTop)).1 hw
      simpa [add_comm, convexConjugate, mul_comm] using (EReal.sub_le_of_le_add' hsum)

end «problem-92»
