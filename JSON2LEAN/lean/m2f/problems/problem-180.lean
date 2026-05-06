import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-180»
/- [BLOCK Exercise 2.24 | 7 | defn]
The domain of a function φ : ℝ^n → ℝ cup {+∞} is
domφ = {x ∈ ℝ^n | φ(x) < +∞}.
-/
def dom {n : ℕ} (φ : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | φ x < ⊤}

/- [BLOCK Exercise 2.24 | 8 | defn]
The epigraph of a function φ : ℝ^n → ℝ is
epi(φ) = {(x,t) ∈ ℝ^n × ℝ | φ(x) ≤ t}.
-/
def epi {n : ℕ} (φ : (Fin n → ℝ) → ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  {(x, t) | φ x ≤ t}

/-- The candidate values used to define the infimal convolution at a point `x`. -/
def infimalWitnessSet {n : ℕ} (g h : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Set ℝ :=
  {r : ℝ |
    ∃ (theta : ℝ) (y z : Fin n → ℝ),
      0 ≤ theta ∧ theta ≤ 1 ∧ theta • y + (1 - theta) • z = x ∧
      r = theta * g y + (1 - theta) * h z}

/-- Lower bounds on `g` and `h` give a uniform lower bound on every witness value. -/
lemma infimalWitnessSet_bddBelow
    {n : ℕ} {g h : (Fin n → ℝ) → ℝ}
    (g_bdd : BddBelow (Set.range g)) (h_bdd : BddBelow (Set.range h))
    (x : Fin n → ℝ) :
    BddBelow (infimalWitnessSet g h x) := by
  -- Extract concrete lower bounds for the two input functions.
  rcases g_bdd with ⟨ag, hag⟩
  rcases h_bdd with ⟨ah, hah⟩
  refine ⟨min ag ah, ?_⟩
  intro r hr
  rcases hr with ⟨theta, y, z, hθ₀, hθ₁, -, hr⟩
  have hθ' : 0 ≤ 1 - theta := sub_nonneg.mpr hθ₁
  have hgy : ag ≤ g y := hag (Set.mem_range_self y)
  have hhz : ah ≤ h z := hah (Set.mem_range_self z)
  have hmin_g : min ag ah ≤ g y := (min_le_left _ _).trans hgy
  have hmin_h : min ag ah ≤ h z := (min_le_right _ _).trans hhz
  have hcombo :
      theta * min ag ah + (1 - theta) * min ag ah ≤
        theta * g y + (1 - theta) * h z := by
    gcongr
  rw [hr]
  calc
    min ag ah = theta * min ag ah + (1 - theta) * min ag ah := by ring
    _ ≤ theta * g y + (1 - theta) * h z := hcombo

/-- Unfolding `convexJoin` for epigraphs gives the explicit five-variable description. -/
lemma mem_convexJoin_epi_iff
    {n : ℕ} {g h : (Fin n → ℝ) → ℝ} {p : (Fin n → ℝ) × ℝ} :
    p ∈ convexJoin ℝ (epi g) (epi h) ↔
      ∃ (theta : ℝ) (y z : Fin n → ℝ) (s u : ℝ),
        0 ≤ theta ∧ theta ≤ 1 ∧
        (y, s) ∈ epi g ∧
        (z, u) ∈ epi h ∧
        p = (theta • y + (1 - theta) • z, theta * s + (1 - theta) * u) := by
  constructor
  · intro hp
    -- Rewrite the segment witness so the coefficient `theta` multiplies the `epi g` endpoint.
    rcases mem_convexJoin.mp hp with ⟨a, ha, b, hb, hpseg⟩
    rcases a with ⟨y, s⟩
    rcases b with ⟨z, u⟩
    rw [segment_symm, segment_eq_image] at hpseg
    rcases hpseg with ⟨theta, htheta, hp_eq⟩
    have hθ₀ : 0 ≤ theta := htheta.1
    have hθ₁ : theta ≤ 1 := htheta.2
    have hp_eq' :
        p = (theta • y + (1 - theta) • z, theta * s + (1 - theta) * u) := by
      simpa [Prod.smul_mk, Prod.mk_add_mk, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using hp_eq.symm
    exact ⟨theta, y, z, s, u, hθ₀, hθ₁, ha, hb, hp_eq'⟩
  · rintro ⟨theta, y, z, s, u, hθ₀, hθ₁, hy_epi, hz_epi, hp_eq⟩
    -- Build the corresponding segment point in the product space.
    refine mem_convexJoin.mpr ⟨(y, s), hy_epi, (z, u), hz_epi, ?_⟩
    rw [segment_eq_image]
    refine ⟨1 - theta, ⟨sub_nonneg.mpr hθ₁, by linarith⟩, ?_⟩
    simpa [Prod.smul_mk, Prod.mk_add_mk, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hp_eq.symm

/-- The epigraph of `f` is the convex join of the epigraphs of `g` and `h`. -/
lemma epi_eq_convexJoin_epi
    {n : ℕ} {g h f : (Fin n → ℝ) → ℝ}
    (g_bdd : BddBelow (Set.range g)) (h_bdd : BddBelow (Set.range h))
    (hf : f =
      fun x =>
        sInf (infimalWitnessSet g h x))
    (hf_attained :
      ∀ x : Fin n → ℝ,
        ∃ (theta : ℝ) (y z : Fin n → ℝ),
          0 ≤ theta ∧ theta ≤ 1 ∧ theta • y + (1 - theta) • z = x ∧
          f x = theta * g y + (1 - theta) * h z) :
    epi f = convexJoin ℝ (epi g) (epi h) := by
  ext p
  rcases p with ⟨x, t⟩
  constructor
  · intro hp
    -- Use an attained minimizing witness and add the remaining slack to both heights.
    rcases hf_attained x with ⟨theta, y, z, hθ₀, hθ₁, hxyz, hfx⟩
    let δ : ℝ := t - f x
    have hδ : 0 ≤ δ := by
      dsimp [δ]
      exact sub_nonneg.mpr hp
    have hy_epi : (y, g y + δ) ∈ epi g := by
      change g y ≤ g y + δ
      linarith
    have hz_epi : (z, h z + δ) ∈ epi h := by
      change h z ≤ h z + δ
      linarith
    have hheight :
        theta * (g y + δ) + (1 - theta) * (h z + δ) = t := by
      dsimp [δ]
      calc
        theta * (g y + (t - f x)) + (1 - theta) * (h z + (t - f x))
            = (theta * g y + (1 - theta) * h z) + (t - f x) := by ring
        _ = f x + (t - f x) := by rw [hfx]
        _ = t := by ring
    have hp_eq :
        ((x, t) : (Fin n → ℝ) × ℝ) =
          (theta • y + (1 - theta) • z,
            theta * (g y + δ) + (1 - theta) * (h z + δ)) := by
      exact Prod.ext hxyz.symm hheight.symm
    rw [mem_convexJoin_epi_iff]
    exact ⟨theta, y, z, g y + δ, h z + δ, hθ₀, hθ₁, hy_epi, hz_epi, hp_eq⟩
  · intro hp
    rw [mem_convexJoin_epi_iff] at hp
    rcases hp with ⟨theta, y, z, s, u, hθ₀, hθ₁, hy_epi, hz_epi, hp_eq⟩
    -- Rewrite the point coordinates, then compare `f x` with the displayed witness value.
    have hx : x = theta • y + (1 - theta) • z := by
      simpa using congrArg Prod.fst hp_eq
    have ht : t = theta * s + (1 - theta) * u := by
      simpa using congrArg Prod.snd hp_eq
    have hwitness :
        theta * g y + (1 - theta) * h z ∈ infimalWitnessSet g h x := by
      exact ⟨theta, y, z, hθ₀, hθ₁, hx.symm, rfl⟩
    have hfx_le :
        f x ≤ theta * g y + (1 - theta) * h z := by
      rw [hf]
      exact csInf_le (infimalWitnessSet_bddBelow g_bdd h_bdd x) hwitness
    have hmono :
        theta * g y + (1 - theta) * h z ≤ theta * s + (1 - theta) * u := by
      have hθ' : 0 ≤ 1 - theta := sub_nonneg.mpr hθ₁
      have hys : g y ≤ s := hy_epi
      have hzu : h z ≤ u := hz_epi
      nlinarith
    rw [ht]
    exact hfx_le.trans hmono

/- [BLOCK Exercise 2.24 | 9 | thm]
Let g,h:ℝ^n → ℝ be convex functions bounded below, with dom g=dom h=ℝ^n. Define f:ℝ^n → ℝ by
f(x)=∈f ≤ft{ θ g(y)+(1-θ)h(z)\ |dle|\ θ y+(1-θ)z=x,\ 0≤ θ ≤ 1,\ y,z∈ ℝ^n }.
For φ:ℝ^n→ ℝ, define
epi(φ)={(x,t)∈ ℝ^n× ℝ| φ(x)≤ t}.
Prove that f is convex and that
epi(f)={(θ y+(1-θ)z,θ s+(1-θ)u)| (y,s)∈ epi(g),\ (z,u)∈ epi(h),\ 0≤ θ≤ 1}.
-/
theorem infimal_convolution_epigraph_eq_and_convex
    {n : ℕ} {g h f : (Fin n → ℝ) → ℝ}
    (hg : ConvexOn ℝ Set.univ g) (hh : ConvexOn ℝ Set.univ h)
    (g_bdd : BddBelow (Set.range g)) (h_bdd : BddBelow (Set.range h))
    (hdomg : dom (fun x => (g x : EReal)) = Set.univ)
    (hdomh : dom (fun x => (h x : EReal)) = Set.univ)
    (hf : f =
      fun x =>
        sInf
          {r : ℝ |
            ∃ (theta : ℝ) (y z : Fin n → ℝ),
              0 ≤ theta ∧ theta ≤ 1 ∧ theta • y + (1 - theta) • z = x ∧
              r = theta * g y + (1 - theta) * h z})
    (hf_attained :
      ∀ x : Fin n → ℝ,
        ∃ (theta : ℝ) (y z : Fin n → ℝ),
          0 ≤ theta ∧ theta ≤ 1 ∧ theta • y + (1 - theta) • z = x ∧
          f x = theta * g y + (1 - theta) * h z) :
    ConvexOn ℝ Set.univ f ∧
      epi f =
        {(p : (Fin n → ℝ) × ℝ) |
          ∃ (theta : ℝ) (y z : Fin n → ℝ) (s u : ℝ),
            0 ≤ theta ∧ theta ≤ 1 ∧
            (y, s) ∈ epi g ∧
            (z, u) ∈ epi h ∧
            p = (theta • y + (1 - theta) • z, theta * s + (1 - theta) * u)} := by
  -- Route correction: prove convexity by identifying `epi f` with a convex join of known epigraphs.
  have h_epi :
      epi f = convexJoin ℝ (epi g) (epi h) := by
    -- The attained infimum plus a slack variable gives the forward inclusion, and `csInf_le`
    -- handles the reverse inequality from any displayed epigraph witness.
    exact epi_eq_convexJoin_epi g_bdd h_bdd hf hf_attained
  have h_conv_g : Convex ℝ (epi g) := by
    -- The custom `epi` is exactly the usual epigraph over `Set.univ`.
    simpa [epi] using
      (hg.convex_epigraph : Convex ℝ {p : (Fin n → ℝ) × ℝ | p.1 ∈ Set.univ ∧ g p.1 ≤ p.2})
  have h_conv_h : Convex ℝ (epi h) := by
    -- The same epigraph conversion applies to `h`.
    simpa [epi] using
      (hh.convex_epigraph : Convex ℝ {p : (Fin n → ℝ) × ℝ | p.1 ∈ Set.univ ∧ h p.1 ≤ p.2})
  have h_conv_epi_f : Convex ℝ (epi f) := by
    -- Convexity is preserved by taking the convex join of two convex sets.
    rw [h_epi]
    exact h_conv_g.convexJoin h_conv_h
  have h_conv_f : ConvexOn ℝ Set.univ f := by
    -- Convert convexity of the epigraph back into convexity of the function.
    refine convexOn_of_convex_epigraph ?_
    simpa [epi] using h_conv_epi_f
  have h_explicit :
      epi f =
        {(p : (Fin n → ℝ) × ℝ) |
          ∃ (theta : ℝ) (y z : Fin n → ℝ) (s u : ℝ),
            0 ≤ theta ∧ theta ≤ 1 ∧
            (y, s) ∈ epi g ∧
            (z, u) ∈ epi h ∧
            p = (theta • y + (1 - theta) • z, theta * s + (1 - theta) * u)} := by
    -- Unfold the convex join description into the exact epigraph formula requested in the statement.
    calc
      epi f = convexJoin ℝ (epi g) (epi h) := h_epi
      _ =
          {(p : (Fin n → ℝ) × ℝ) |
            ∃ (theta : ℝ) (y z : Fin n → ℝ) (s u : ℝ),
              0 ≤ theta ∧ theta ≤ 1 ∧
              (y, s) ∈ epi g ∧
              (z, u) ∈ epi h ∧
              p = (theta • y + (1 - theta) • z, theta * s + (1 - theta) * u)} := by
            ext p
            rw [mem_convexJoin_epi_iff]
            rfl
  exact ⟨h_conv_f, h_explicit⟩

end «problem-180»
