import Mathlib

noncomputable section
open scoped Topology
open scoped Pointwise
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-186»

def SeparatingHyperplane (n : ℕ) (a : Fin n → ℝ) (b : ℝ)
    (C D : Set (Fin n → ℝ)) : Prop :=
  a ≠ 0 ∧
    (∀ x, x ∈ C → (∑ i, a i * x i) ≤ b) ∧
    (∀ y, y ∈ D → b ≤ (∑ i, a i * y i))

/-- A continuous linear functional on `Fin n → ℝ` is the sum of its values on the standard basis. -/
lemma strongDual_apply_eq_sum_pi_single {n : ℕ} (f : StrongDual ℝ (Fin n → ℝ))
    (x : Fin n → ℝ) :
    f x = ∑ i, f (Pi.single i 1) * x i := by
  -- Expand the functional in the coordinate basis.
  rw [show f x = f.toLinearMap x by rfl, LinearMap.pi_apply_eq_sum_univ]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [smul_eq_mul, mul_comm]
  congr 1
  apply congrArg f
  funext j
  by_cases h : i = j
  · subst h
    simp [Pi.single]
  · simp [Pi.single, h, Ne.symm h]

/-- A nonempty convex subset of `ℝⁿ` avoiding the origin admits a nonzero functional that is
nonnegative on the set. -/
lemma exists_nonnegative_functional_of_zero_not_mem {n : ℕ} {S : Set (Fin n → ℝ)}
    (hSconv : Convex ℝ S) (hSne : S.Nonempty) (h0notS : (0 : Fin n → ℝ) ∉ S) :
    ∃ f : StrongDual ℝ (Fin n → ℝ), f ≠ 0 ∧ ∀ z ∈ S, 0 ≤ f z := by
  by_cases h0span : (0 : Fin n → ℝ) ∈ affineSpan ℝ S
  · let p : Submodule ℝ (Fin n → ℝ) := vectorSpan ℝ S
    have hAff : affineSpan ℝ S = p.toAffineSubspace := by
      -- When `0` belongs to the affine span, that affine span is the underlying vector subspace.
      refine (AffineSubspace.eq_iff_direction_eq_of_mem h0span ?_).2 ?_
      · simp [p]
      · rw [direction_affineSpan, Submodule.toAffineSubspace_direction]
    have hPreConv : Convex ℝ ((↑) ⁻¹' S : Set p) := by
      -- Restrict the convex set to its ambient span.
      simpa [p] using hSconv.linear_preimage p.subtype
    have hPreIntNonempty : (interior ((↑) ⁻¹' S : Set p)).Nonempty := by
      -- Intrinsic interior becomes ordinary interior inside the span.
      have hIntAff : (interior ((↑) ⁻¹' S : Set (affineSpan ℝ S))).Nonempty := by
        simpa [intrinsicInterior, Set.image_nonempty] using
          (Set.Nonempty.intrinsicInterior hSconv hSne)
      rw [hAff] at hIntAff
      simpa [p] using hIntAff
    have h0notPreInt : (0 : p) ∉ interior ((↑) ⁻¹' S : Set p) := by
      -- The origin cannot enter the interior because it does not belong to the set itself.
      intro h
      exact h0notS (by simpa using interior_subset h)
    obtain ⟨g, hgpos⟩ :=
      geometric_hahn_banach_point_open (x := (0 : p)) hPreConv.interior isOpen_interior h0notPreInt
    obtain ⟨f, hfext, _⟩ := Real.exists_extension_norm_eq p g
    have hclosure : closure (interior ((↑) ⁻¹' S : Set p)) = closure ((↑) ⁻¹' S : Set p) := by
      -- A nonempty convex set equals the closure of its interior inside the span.
      exact hPreConv.closure_interior_eq_closure_of_nonempty_interior hPreIntNonempty
    have hnonneg_pre : ∀ z ∈ ((↑) ⁻¹' S : Set p), 0 ≤ g z := by
      intro z hz
      have hsubset : interior ((↑) ⁻¹' S : Set p) ⊆ {w : p | 0 ≤ g w} := by
        -- Positivity on the interior implies membership in the nonnegative half-space.
        intro w hw
        simpa using (hgpos w hw).le
      have hclosed : IsClosed {w : p | 0 ≤ g w} := isClosed_Ici.preimage g.continuous
      have hzclosure : z ∈ closure (interior ((↑) ⁻¹' S : Set p)) := by
        rw [hclosure]
        exact subset_closure hz
      exact closure_minimal hsubset hclosed hzclosure
    have hnonneg : ∀ z ∈ S, 0 ≤ f z := by
      intro z hz
      have hzP : z ∈ p := by
        -- Move the point into the span so that the extension identity applies.
        have hzAff : z ∈ affineSpan ℝ S := subset_affineSpan ℝ S hz
        rw [hAff] at hzAff
        simpa [p] using hzAff
      have hzPre : (⟨z, hzP⟩ : p) ∈ ((↑) ⁻¹' S : Set p) := by
        simpa using hz
      have hgz : 0 ≤ g ⟨z, hzP⟩ := hnonneg_pre _ hzPre
      simpa [hfext ⟨z, hzP⟩] using hgz
    have hne : f ≠ 0 := by
      -- A separator positive on a nonempty interior cannot be the zero functional.
      rcases hPreIntNonempty with ⟨z, hz⟩
      have hzpos : 0 < g z := by
        simpa using hgpos z hz
      intro hfzero
      have hzext := hfext z
      simp [hfzero] at hzext
      exact hzpos.ne' hzext.symm
    exact ⟨f, hne, hnonneg⟩
  · obtain ⟨f, u, hfu, huS⟩ :=
      geometric_hahn_banach_point_closed
        (t := (affineSpan ℝ S : Set (Fin n → ℝ))) (x := (0 : Fin n → ℝ))
        (affineSpan ℝ S).convex (affineSpan ℝ S).closed_of_finiteDimensional h0span
    have hu_pos : 0 < u := by
      -- Separating the origin from the affine span yields a positive offset.
      simpa using hfu
    have hnonneg : ∀ z ∈ S, 0 ≤ f z := by
      intro z hz
      exact (hu_pos.trans (huS z (subset_affineSpan ℝ S hz))).le
    have hne : f ≠ 0 := by
      -- A strictly positive value on a point of `S` rules out the zero functional.
      rcases hSne with ⟨z, hz⟩
      have hzpos : 0 < f z := hu_pos.trans (huS z (subset_affineSpan ℝ S hz))
      intro hfzero
      simpa [hfzero] using hzpos.ne'
    exact ⟨f, hne, hnonneg⟩

/-- Two disjoint convex sets admit a separating hyperplane. -/
theorem exists_separating_hyperplane_of_disjoint_convex
    (n : ℕ) (C D : Set (Fin n → ℝ))
    (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hdisj : Disjoint C D) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ,
      SeparatingHyperplane n a b C D := by
  let S : Set (Fin n → ℝ) := D - C
  have hSne : S.Nonempty := by
    -- Pick one point from each set to produce a point in the difference set.
    rcases hDne with ⟨y, hy⟩
    rcases hCne with ⟨x, hx⟩
    refine ⟨y - x, ?_⟩
    exact ⟨y, hy, x, hx, rfl⟩
  have hSconv : Convex ℝ S := by
    -- The difference of two convex sets is convex.
    simpa [S] using hD.sub hC
  have h0notS : (0 : Fin n → ℝ) ∉ S := by
    -- Disjointness means no difference `y - x` can vanish.
    simpa [S] using hdisj.symm.zero_notMem_sub_set
  obtain ⟨f, hfnz, hfnonneg⟩ :=
    exists_nonnegative_functional_of_zero_not_mem hSconv hSne h0notS
  have hpair : ∀ x ∈ C, ∀ y ∈ D, f x ≤ f y := by
    intro x hx y hy
    -- Apply nonnegativity to the difference `y - x`.
    have hyx : y - x ∈ S := by
      exact ⟨y, hy, x, hx, rfl⟩
    have hnonneg : 0 ≤ f (y - x) := hfnonneg _ hyx
    simpa [S, map_sub, sub_eq_add_neg, sub_nonneg] using hnonneg
  have hCimgBdd : BddAbove (f '' C) := by
    -- Any fixed point of `D` gives a common upper bound on `f '' C`.
    rcases hDne with ⟨y0, hy0⟩
    refine ⟨f y0, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    exact hpair x hx y0 hy0
  have hCimgNonempty : (f '' C).Nonempty := hCne.image f
  let a : Fin n → ℝ := fun i => f (Pi.single i 1)
  let b : ℝ := sSup (f '' C)
  refine ⟨a, b, ?_⟩
  constructor
  · -- If all coordinate coefficients vanished, then the functional itself would vanish.
    intro ha0
    apply hfnz
    have ha0' : ∀ i, f (Pi.single i 1) = 0 := by
      intro i
      have hi := congrArg (fun v : Fin n → ℝ => v i) ha0
      simpa [a] using hi
    ext x
    rw [strongDual_apply_eq_sum_pi_single]
    simp [ha0']
  constructor
  · intro x hx
    -- Rewrite the functional bound on `C` in coordinates.
    calc
      ∑ i, a i * x i = f x := by
        simpa [a] using (strongDual_apply_eq_sum_pi_single f x).symm
      _ ≤ b := by
        exact le_csSup hCimgBdd (Set.mem_image_of_mem f hx)
  · intro y hy
    -- The supremum over `f '' C` lies below every value of `f` on `D`.
    have hyUpper : ∀ r ∈ f '' C, r ≤ f y := by
      rintro r ⟨x, hx, rfl⟩
      exact hpair x hx y hy
    calc
      b = sSup (f '' C) := rfl
      _ ≤ f y := csSup_le hCimgNonempty hyUpper
      _ = ∑ i, a i * y i := by
        simpa [a] using (strongDual_apply_eq_sum_pi_single f y)

end «problem-186»
