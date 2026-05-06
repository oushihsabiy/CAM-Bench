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
  sorry

end «problem-121»
