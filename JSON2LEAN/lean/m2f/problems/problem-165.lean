import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-165»
/-
A map psi: ℝ^n → ℝ^n is monotone if for all x, y ∈ ℝ^n, (psi(x) - psi(y))ᵀ(x - y) ≥ 0.
-/
def MonotoneMap (ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x y, 0 ≤ ⟪ψ x - ψ y, x - y⟫

/-
Let f: ℝⁿ → ℝ be differentiable and convex, meaning that for all x, y ∈ ℝⁿ and all θ ∈ [0, 1], f(θx
+ (1 - θ)y) ≤ θf(x) + (1 - θ)f(y). A mapping ψ: ℝⁿ → ℝⁿ is called monotone if for all x, y ∈ ℝⁿ,
(ψ(x) - ψ(y))ᵀ(x - y) ≥ 0, where uᵀv denotes the standard Euclidean inner product on ℝⁿ. Show that
∇f: ℝⁿ → ℝⁿ is monotone.
-/
open scoped RealInnerProductSpace

theorem gradient_monotone_of_convex_differentiable
    {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hfdiff : Differentiable ℝ f) :
    MonotoneMap (fun x => gradient f x) := by
  intro x y
  let g : ℝ → ℝ := fun t => f (AffineMap.lineMap y x t)
  -- Restrict the convex function to the affine line from `y` to `x`.
  have hgconv : ConvexOn ℝ Set.univ g := by
    simpa [g] using (hconv.comp_affineMap (AffineMap.lineMap y x))
  -- The restricted scalar function is differentiable because both factors are differentiable.
  have hgdiff : ∀ t : ℝ, DifferentiableAt ℝ g t := by
    intro t
    simpa [g] using
      (hfdiff (AffineMap.lineMap y x t)).comp t
        (AffineMap.hasDerivAt_lineMap (a := y) (b := x) (x := t)).differentiableAt
  -- The derivative along the line is the gradient paired with the direction `x - y`.
  have hgderiv :
      ∀ t : ℝ, deriv g t = ⟪gradient f (AffineMap.lineMap y x t), x - y⟫ := by
    intro t
    have hcomp :
        HasDerivAt g (fderiv ℝ f (AffineMap.lineMap y x t) (x - y)) t := by
      simpa [g] using
        ((hfdiff (AffineMap.lineMap y x t)).hasFDerivAt.comp_hasDerivAt t
          (AffineMap.hasDerivAt_lineMap (a := y) (b := x) (x := t)))
    calc
      deriv g t = fderiv ℝ f (AffineMap.lineMap y x t) (x - y) := hcomp.deriv
      _ = ⟪gradient f (AffineMap.lineMap y x t), x - y⟫ := by
        simpa using
          ((hfdiff (AffineMap.lineMap y x t)).hasGradientAt.fderiv_apply (y := x - y))
  -- Monotonicity of the one-variable derivative gives the endpoint inequality.
  have hendpoint : ⟪gradient f y, x - y⟫ ≤ ⟪gradient f x, x - y⟫ := by
    have hmono := hgconv.monotoneOn_deriv (fun t _ => hgdiff t)
    have h01 := hmono (by simp) (by simp) zero_le_one
    simpa [hgderiv, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using h01
  -- Rewriting the endpoint inequality gives the standard monotonicity form.
  calc
    0 ≤ ⟪gradient f x, x - y⟫ - ⟪gradient f y, x - y⟫ := sub_nonneg.mpr hendpoint
    _ = ⟪gradient f x - gradient f y, x - y⟫ := by
      rw [inner_sub_left]

/-
Let f: ℝ^n → ℝ^n be differentiable and convex, meaning that for all x, y ∈ ℝ^n and all θ ∈ [0, 1],
f(θ x + (1 - θ)y) ≤ θ f(x) + (1 - θ)f(y). A mapping psi: ℝ^n → ℝ^n is called monotone if for all x,
y ∈
ℝ^n, (psi(x) - psi(y))ᵀ(x - y) ≥ 0, where uᵀ v denotes the standard Euclidean inner product on ℝ^n.
Show
also that the converse is false by proving that there exists a monotone mapping psi: ℝ^n → ℝ^n that
is not equal to ∇ g for any differentiable convex function g: ℝ^n → ℝ.
-/
theorem exists_monotone_map_not_gradient_of_convex
    {n : ℕ} [Fact (1 < n)] :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      MonotoneMap ψ ∧
        ¬ ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
          Differentiable ℝ g ∧ ConvexOn ℝ Set.univ g ∧
            ψ = fun x => gradient g x := by
  sorry

end «problem-165»
