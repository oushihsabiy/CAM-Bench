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
  sorry

end «problem-180»
