import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-52»
/-
Let f: ℝ^n times ℝ^m o ℝ be differentiable, and suppose that for any fixed z ∈ ℝ^m, the mapping x
mapsto f(x, z) is convex on ℝ^n, and for any fixed x ∈ ℝ^n, the mapping z mapsto f(x, z) is concave
on ℝ^m. That is, f is a convex--concave function with respect to (x, z). It is known that there
exists (ar x, ar z) ∈ ℝ^n times ℝ^m such that abla f(ar x, ar z) = 0, where abla f(ar x, ar z)
denotes the ∇of f with respect to all variables (x, z). Prove that (ar x, ar z) is a saddle point
of f, that is, for any x ∈ ℝ^n and any z ∈ ℝ^m, we have f(ar x, z) ≤ f(ar x, ar z) ≤ f(x, ar z).
-/
open scoped BigOperators

theorem convex_concave_gradient_zero_is_saddle_point
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    {xBar : EuclideanSpace ℝ (Fin n)}
    {zBar : EuclideanSpace ℝ (Fin m)}
    (hconv :
      ∀ z : EuclideanSpace ℝ (Fin m),
        ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => f (x, z)))
    (hconc :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ConcaveOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    (hdiff : DifferentiableAt ℝ f (xBar, zBar))
    (hgrad : fderiv ℝ f (xBar, zBar) = 0) :
    ∀ x : EuclideanSpace ℝ (Fin n), ∀ z : EuclideanSpace ℝ (Fin m),
      f (xBar, z) ≤ f (xBar, zBar) ∧ f (xBar, zBar) ≤ f (x, zBar) := by
  intro x z
  constructor
  · -- Restrict to the `z`-line through `(xBar, zBar)` and use concavity at the stationary point.
    let gz : ℝ → ℝ := fun t => f (xBar, AffineMap.lineMap zBar z t)
    have hgzconc : ConcaveOn ℝ Set.univ gz := by
      simpa [gz] using (hconc xBar).comp_affineMap (AffineMap.lineMap zBar z)
    -- The chain rule turns the vanishing full derivative into a vanishing derivative of `gz` at `0`.
    have hgzderiv : HasDerivAt gz 0 0 := by
      have hline : HasDerivAt (fun t : ℝ => (xBar, AffineMap.lineMap zBar z t)) (0, z - zBar) 0 := by
        simpa using (hasDerivAt_const (0 : ℝ) xBar).prodMk
          (AffineMap.hasDerivAt_lineMap (a := zBar) (b := z) (x := (0 : ℝ)))
      have hcomp : HasDerivAt gz ((fderiv ℝ f (xBar, zBar)) (0, z - zBar)) 0 := by
        simpa [gz] using
          HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hdiff.hasFDerivAt hline (by simp)
      simpa [hgrad] using hcomp
    -- Concavity bounds the secant slope above by the derivative, so the endpoint value cannot exceed `gz 0`.
    have hslope : slope gz 0 1 ≤ 0 :=
      hgzconc.slope_le_of_hasDerivAt (by simp) (by simp) zero_lt_one hgzderiv
    have hslope' : f (xBar, z) - f (xBar, zBar) ≤ 0 := by
      simpa [gz, slope, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hslope
    linarith
  · -- Restrict to the `x`-line through `(xBar, zBar)` and use convexity at the stationary point.
    let gx : ℝ → ℝ := fun t => f (AffineMap.lineMap xBar x t, zBar)
    have hgxconv : ConvexOn ℝ Set.univ gx := by
      simpa [gx] using (hconv zBar).comp_affineMap (AffineMap.lineMap xBar x)
    -- The same chain-rule computation shows that the line derivative at `0` is zero.
    have hgxderiv : HasDerivAt gx 0 0 := by
      have hline : HasDerivAt (fun t : ℝ => (AffineMap.lineMap xBar x t, zBar)) (x - xBar, 0) 0 := by
        simpa using (AffineMap.hasDerivAt_lineMap (a := xBar) (b := x) (x := (0 : ℝ))).prodMk
          (hasDerivAt_const (0 : ℝ) zBar)
      have hcomp : HasDerivAt gx ((fderiv ℝ f (xBar, zBar)) (x - xBar, 0)) 0 := by
        simpa [gx] using
          HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hdiff.hasFDerivAt hline (by simp)
      simpa [hgrad] using hcomp
    -- Convexity bounds the secant slope below by the derivative, forcing the endpoint value above `gx 0`.
    have hslope : 0 ≤ slope gx 0 1 :=
      hgxconv.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hgxderiv
    have hslope' : 0 ≤ f (x, zBar) - f (xBar, zBar) := by
      simpa [gx, slope, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hslope
    linarith

/-
Let f: ℝ^n times ℝ^m o ℝ be differentiable, and suppose that for any fixed z ∈ ℝ^m, the mapping x
mapsto f(x, z) is convex on ℝ^n, and for any fixed x ∈ ℝ^n, the mapping z mapsto f(x, z) is concave
on ℝ^m. That is, f is a convex--concave function with respect to (x, z). It is known that there
exists (ar x, ar z) ∈ ℝ^n times ℝ^m such that abla f(ar x, ar z) = 0, where abla f(ar x, ar z)
denotes the ∇of f with respect to all variables (x, z). Assume additionally that for every
fixed x the set of values {f(x, z) | z ∈ ℝ^m} is bounded above, and for every fixed z the
set of values {f(x, z) | x ∈ ℝ^n} is bounded below, so that the real-valued `sSup` and
`sInf` below are meaningful. Prove that f satisfies the minimax relation
min_{x ∈ ℝ^n} sup_{z ∈ ℝ^m} f(x, z) = sup_{z ∈ ℝ^m} inf_{x ∈ ℝ^n} f(x, z).
-/
theorem convex_concave_gradient_zero_implies_minimax
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    (hdiff : Differentiable ℝ f)
    (hconv :
      ∀ z : EuclideanSpace ℝ (Fin m),
        ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => f (x, z)))
    (hconc :
      ∀ x : EuclideanSpace ℝ (Fin n),
        ConcaveOn ℝ Set.univ (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    (hex :
      ∃ xBar : EuclideanSpace ℝ (Fin n), ∃ zBar : EuclideanSpace ℝ (Fin m),
        fderiv ℝ f (xBar, zBar) = 0)
    (hbounded_sup :
      ∀ x : EuclideanSpace ℝ (Fin n),
        BddAbove (Set.range fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
    (hbounded_inf :
      ∀ z : EuclideanSpace ℝ (Fin m),
        BddBelow (Set.range fun x : EuclideanSpace ℝ (Fin n) => f (x, z))) :
    sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) =>
      sSup (Set.range fun z : EuclideanSpace ℝ (Fin m) => f (x, z))) =
    sSup (Set.range fun z : EuclideanSpace ℝ (Fin m) =>
      sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) => f (x, z))) := by
  rcases hex with ⟨xBar, zBar, hgrad⟩
  let v : ℝ := f (xBar, zBar)
  -- Reuse the saddle-point theorem at the stationary point and record the two-sided bounds.
  have hsaddle :
      ∀ x : EuclideanSpace ℝ (Fin n), ∀ z : EuclideanSpace ℝ (Fin m),
        f (xBar, z) ≤ v ∧ v ≤ f (x, zBar) := by
    intro x z
    simpa [v] using
      convex_concave_gradient_zero_is_saddle_point hconv hconc (hdiff (xBar, zBar)) hgrad x z
  -- The inner supremum at the saddle `xBar` is attained at `zBar`, so it equals the saddle value.
  have hsup_xBar : sSup (Set.range fun z : EuclideanSpace ℝ (Fin m) => f (xBar, z)) = v := by
    refine le_antisymm ?_ ?_
    · refine csSup_le (Set.range_nonempty _) ?_
      -- Every value along the `z`-slice is bounded above by the saddle value.
      rintro _ ⟨z, rfl⟩
      exact (hsaddle xBar z).1
    · -- The witness `zBar` shows that the saddle value lies below this supremum.
      simpa [v] using
        (le_csSup (hbounded_sup xBar)
          (Set.mem_range_self zBar) :
          f (xBar, zBar) ≤ sSup (Set.range fun z : EuclideanSpace ℝ (Fin m) => f (xBar, z)))
  -- The inner infimum at the saddle `zBar` is attained at `xBar`, so it equals the same value.
  have hinf_zBar : sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) => f (x, zBar)) = v := by
    refine le_antisymm ?_ ?_
    · -- The witness `xBar` places the infimum below the saddle value.
      simpa [v] using
        (csInf_le (hbounded_inf zBar)
          (Set.mem_range_self xBar) :
          sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) => f (x, zBar)) ≤ f (xBar, zBar))
    · refine le_csInf (Set.range_nonempty _) ?_
      -- Every value along the `x`-slice is bounded below by the saddle value.
      rintro _ ⟨x, rfl⟩
      exact (hsaddle x zBar).2
  let Φ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => sSup (Set.range fun z : EuclideanSpace ℝ (Fin m) => f (x, z))
  -- Each outer candidate `Φ x` dominates the saddle value because `zBar` is an admissible witness.
  have hPhi_ge : ∀ x : EuclideanSpace ℝ (Fin n), v ≤ Φ x := by
    intro x
    exact (hsaddle x zBar).2.trans <|
      (le_csSup (hbounded_sup x) (Set.mem_range_self zBar))
  -- Therefore the outer infimum of the suprema is exactly the saddle value.
  have houter_inf : sInf (Set.range Φ) = v := by
    refine le_antisymm ?_ ?_
    · -- The point `xBar` attains the outer infimum at the already identified inner supremum.
      simpa [Φ, hsup_xBar] using
        (csInf_le
          (by
            refine ⟨v, ?_⟩
            rintro _ ⟨x, rfl⟩
            exact hPhi_ge x)
          (Set.mem_range_self xBar) :
          sInf (Set.range Φ) ≤ Φ xBar)
    · refine le_csInf (Set.range_nonempty _) ?_
      -- The saddle value is a lower bound for all outer candidates.
      rintro _ ⟨x, rfl⟩
      exact hPhi_ge x
  let Ψ : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun z => sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) => f (x, z))
  -- Each outer candidate `Ψ z` lies below the saddle value because `xBar` is an admissible witness.
  have hPsi_le : ∀ z : EuclideanSpace ℝ (Fin m), Ψ z ≤ v := by
    intro z
    exact
      (show Ψ z ≤ f (xBar, z) by
        simpa [Ψ] using
          (csInf_le (hbounded_inf z)
            (Set.mem_range_self xBar) :
            sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) => f (x, z)) ≤ f (xBar, z))).trans
        ((hsaddle xBar z).1)
  -- Therefore the outer supremum of the infima is also the saddle value.
  have houter_sup : sSup (Set.range Ψ) = v := by
    refine le_antisymm ?_ ?_
    · refine csSup_le (Set.range_nonempty _) ?_
      -- The saddle value is an upper bound for all outer candidates.
      rintro _ ⟨z, rfl⟩
      exact hPsi_le z
    · -- The point `zBar` attains the outer supremum at the already identified inner infimum.
      simpa [Ψ, hinf_zBar] using
        (le_csSup
          (by
            refine ⟨v, ?_⟩
            rintro _ ⟨z, rfl⟩
            exact hPsi_le z)
          (Set.mem_range_self zBar) :
          Ψ zBar ≤ sSup (Set.range Ψ))
  -- Both minimax expressions have been identified with the same saddle value.
  calc
    sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) =>
      sSup (Set.range fun z : EuclideanSpace ℝ (Fin m) => f (x, z)))
        = sInf (Set.range Φ) := by rfl
    _ = v := houter_inf
    _ = sSup (Set.range Ψ) := houter_sup.symm
    _ = sSup (Set.range fun z : EuclideanSpace ℝ (Fin m) =>
        sInf (Set.range fun x : EuclideanSpace ℝ (Fin n) => f (x, z))) := by rfl

end «problem-52»
