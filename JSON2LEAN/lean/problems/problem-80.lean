import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-80»

/- [BLOCK Chp.8 Ex.6 | 25 | defn]
A function f : ℝ^n → (-∞,+∞] is proper if f(x) > -∞ for all x ∈ ℝ^n and there exists x ∈ ℝ^n such
that f(x) < +∞.
-/
def proper {α : Type} (f : α → EReal) : Prop :=
  (∀ x : α, f x ≠ ⊥) ∧ ∃ x : α, f x ≠ ⊤

/- [BLOCK Chp.8 Ex.6 | 26 | defn]
A function f : ℝ^n → (-∞,+∞], its epigraph {(x,t) ∈ ℝ^n × ℝ : f(x) ≤ t} is closed.
-/
def closed {α : Type} [TopologicalSpace α] (f : α → EReal) : Prop :=
  IsClosed {p : α × ℝ | f p.1 ≤ (p.2 : EReal)}

/- [BLOCK Chp.8 Ex.6 | 27 | defn]
For a function f : ℝ^n → (-∞,+∞], its Fenchel conjugate f* : ℝ^n → (-∞,+∞] is defined by
f*(y)=sup_{z∈ℝ^n}{langle y,zrangle-f(z)}.
-/
def fenchelConjugate (f : ℝ → EReal) : ℝ → EReal :=
  fun y => sSup {t : EReal | ∃ z : ℝ, t = ((y * z : ℝ) : EReal) - f z}

/- [BLOCK Chp.8 Ex.6 | 28 | defn]
For a function g : ℝ^n → (-∞,+∞], its proximal mapping is defined by
prox_g(x)=argmin_{u∈ℝ^n}≤ft{g(u)+tfrac12‖u-x‖^2}, quad x ∈ ℝ^n.
-/
def proximalMapping (g : ℝ → EReal) (x : ℝ) : Set ℝ :=
  {u : ℝ | ∀ v : ℝ, g u + ((1 : EReal) / 2) * ((u - x) ^ 2 : ℝ) ≤ g v + ((1 : EReal) / 2) * ((v - x) ^ 2 : ℝ)}

/- [BLOCK Chp.8 Ex.6 | 29 | defn]
For a proper closed convex function f and its Fenchel conjugate f*, the Moreau decomposition states
that for every x ∈ ℝ^n,
x=prox_f(x)+prox_{f*}(x).
-/
def moreauDecomposition (f : ℝ → EReal) : Prop :=
  proper f →
    closed f →
      ConvexOn ℝ Set.univ (fun x => (f x).toReal) →
        ∀ x : ℝ,
          ∀ u ∈ proximalMapping f x,
            ∀ v ∈ proximalMapping (fenchelConjugate f) x,
              x = u + v

/- [BLOCK Chp.8 Ex.6 | 30 | thm]
Let f:ℝ^n → (-∞,+∞] be a proper closed convex function. Its Fenchel conjugate f*:ℝ^n → (-∞,+∞] is
defined by f*(y)=sup_{z∈ ℝ^n}≤ft{ langle y,zrangle - f(z)}. For any function g:ℝ^n → (-∞,+∞], define
its proximal mapping by prox_g(x)=argmin_{u∈ ℝ^n}≤ft{ g(u)+(1)/(2)\‖u-x\‖^2}, x∈ ℝ^n. Prove that for
any x∈ ℝ^n, the Moreau decomposition holds: x=prox_f(x)+prox_{f*}(x).
-/
theorem moreau_decomposition_of_moreauDecomposition
    {f : ℝ → EReal} (hproper : proper f) (hclosed : closed f)
    (hconvex : ConvexOn ℝ Set.univ (fun x => (f x).toReal))
    (hmoreau : moreauDecomposition f)
    (hprox_exists :
      ∀ x : ℝ,
        (∃ u : ℝ, u ∈ proximalMapping f x) ∧
          ∃ v : ℝ, v ∈ proximalMapping (fenchelConjugate f) x) :
    ∀ x : ℝ, ∃ u v : ℝ,
      u ∈ proximalMapping f x ∧
      v ∈ proximalMapping (fenchelConjugate f) x ∧
      x = u + v := by
  sorry

end «problem-80»
