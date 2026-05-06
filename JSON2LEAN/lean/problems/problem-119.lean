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
  sorry

end «problem-119»
