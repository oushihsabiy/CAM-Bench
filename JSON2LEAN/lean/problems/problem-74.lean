import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-74»

/- [BLOCK Exercise 8.14-(b) | 15 | defn]
An ellipsoid ∈ ℝ^n is a set of the form E = {c + Pu | ‖u‖_2 ≤ 1}, where c ∈ ℝ^n and P ∈ ℝ^{n×n} is
invertible.
-/
def ellipsoid (n : ℕ) (c : EuclideanSpace ℝ (Fin n)) (P : Matrix (Fin n) (Fin n) ℝ)
    (_hP : IsUnit P.det) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ 1 ∧ x = c + (P.mulVec u)}

/- [BLOCK Exercise 8.14-(b) | 16 | defn]
An ellipsoid E is inscribed in a set C if E ⊆ C.
-/
def inscribed {α : Type*} (E C : Set α) : Prop :=
  E ⊆ C

/- [BLOCK Exercise 8.14-(b) | 17 | defn]
Given a family F of ellipsoids, an ellipsoid E* ∈ F is a maximum-volume ellipsoid if vol(E*) ≥
vol(E) for all E ∈ F.
-/
def maximumVolumeEllipsoid
    {α : Type*}
    (vol : Set α → ℝ)
    (F : Set (Set α))
    (E_star : Set α) : Prop :=
  E_star ∈ F ∧ ∀ E ∈ F, vol E_star ≥ vol E

/- [BLOCK Exercise 8.14-(b) | 18 | thm]
Let C={x∈ ℝ^n| -1preceq Axpreceq 1}, where A∈ ℝ^{m× n}, 1∈ ℝ^m is the all-ones vector, and for u,v∈
ℝ^m, upreceq v means uᵢ≤ vᵢ for all i=1,dots,m, while uprec v means uᵢ<vᵢ for all i=1,dots,m. Assume
{x∈ ℝ^n| -1prec Axprec 1}ne emptyset. An ellipsoid ∈ ℝ^n means a set of the form E={c+Pu| ‖u‖_2≤ 1},
where c∈ ℝ^n and P∈ ℝ^{n×n} is invertible. If E⊆ C, we say that E is inscribed in C. For t>0, the
ellipsoid obtained by scaling E by the factor t about its center c is {c+tPu| ‖u‖_2≤ 1}. Show that
if E is a maximum-volume ellipsoid among all ellipsoids inscribed in C, then the ellipsoid obtained
by scaling E by the factor n about its center contains C.
-/
open scoped Matrix

theorem john_ellipsoid_scaling_contains_polytope
    {m n : ℕ}
    (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : EuclideanSpace ℝ (Fin n))
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : IsUnit P.det)
    (hnonempty :
      ∃ x : EuclideanSpace ℝ (Fin n),
        (∀ i : Fin m, (-1 : ℝ) < (A.mulVec x) i) ∧
        (∀ i : Fin m, (A.mulVec x) i < (1 : ℝ)))
    (hinscribed :
      inscribed (ellipsoid n c P hP)
        {x : EuclideanSpace ℝ (Fin n) |
          ∀ i : Fin m, (-1 : ℝ) ≤ (A.mulVec x) i ∧ (A.mulVec x) i ≤ (1 : ℝ)})
    (hmax :
      ∀ (c' : EuclideanSpace ℝ (Fin n)) (P' : Matrix (Fin n) (Fin n) ℝ)
        (hP' : IsUnit P'.det),
        inscribed (ellipsoid n c' P' hP')
          {x : EuclideanSpace ℝ (Fin n) |
            ∀ i : Fin m, (-1 : ℝ) ≤ (A.mulVec x) i ∧ (A.mulVec x) i ≤ (1 : ℝ)} →
        |P'.det| ≤ |P.det|) :
    {x : EuclideanSpace ℝ (Fin n) |
      ∀ i : Fin m, (-1 : ℝ) ≤ (A.mulVec x) i ∧ (A.mulVec x) i ≤ (1 : ℝ)} ⊆
      {x : EuclideanSpace ℝ (Fin n) |
        ∃ u : EuclideanSpace ℝ (Fin n),
          ‖u‖ ≤ 1 ∧ x = c + ((n : ℝ) • (P.mulVec u))} := by
  sorry

end «problem-74»
