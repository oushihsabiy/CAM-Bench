import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-125»

def SPDMatrix (n : ℕ) :=
  {A : Matrix (Fin n) (Fin n) ℝ //
    A.IsSymm ∧
      (∀ y : Fin n → ℝ, y ≠ 0 → 0 < dotProduct y (A.mulVec y)) ∧
      Nonempty (Invertible A)}

/- [BLOCK Exercise 8.12 | 14 | defn]
An ellipsoid ∈ ℝ^n is a set of the form E = {x ∈ ℝ^n : (x-c)ᵀ A^(-1) (x-c) <= 1}, where c ∈ ℝ^n and
A is symmetric positive definite.
-/
def ellipsoid (n : ℕ) (c : Fin n → ℝ) (A : SPDMatrix n) :
    Set (Fin n → ℝ) :=
  {x |
    let v : Fin n → ℝ := fun i => x i - c i
    dotProduct v ((A.1⁻¹).mulVec v) ≤ 1}

/- [BLOCK Exercise 8.12 | 15 | defn]
For S subset of ℝ^n, a Loewner-John ellipsoid of S is an ellipsoid contained in S with maximal
n-dimensional Lebesgue measure among all ellipsoids contained in S.
-/
def isLoewnerJohnEllipsoid (n : ℕ) (S : Set (Fin n → ℝ))
    (c : Fin n → ℝ) (A : SPDMatrix n) : Prop :=
  ellipsoid n c A ⊆ S ∧
    ∀ c' : Fin n → ℝ,
      ∀ A' : SPDMatrix n,
        ellipsoid n c' A' ⊆ S →
          MeasureTheory.volume (ellipsoid n c' A') ≤
            MeasureTheory.volume (ellipsoid n c A)

/- [BLOCK Exercise 8.12 | 16 | thm]
Let S be a subset of ℝ^n. Prove that if there exists an ellipsoid E contained in S with maximal
volume among all ellipsoids contained in S, then this maximal ellipsoid is unique.
-/
theorem loewnerJohnEllipsoid_unique
    (n : ℕ) (S : Set (Fin n → ℝ))
    (hS_convex : Convex ℝ S) :
    (∃ c : Fin n → ℝ, ∃ A : SPDMatrix n,
      isLoewnerJohnEllipsoid n S c A) →
    ∀ c₁ c₂ : Fin n → ℝ,
      ∀ A₁ A₂ : SPDMatrix n,
      isLoewnerJohnEllipsoid n S c₁ A₁ →
      isLoewnerJohnEllipsoid n S c₂ A₂ →
      ellipsoid n c₁ A₁ = ellipsoid n c₂ A₂ := by
  sorry

/- [BLOCK Exercise 8.12 | 17 | thm]
Let S be a subset of ℝ^n. Prove that whenever the Loewner-John ellipsoid of S exists, it is unique.
-/
theorem loewnerJohnEllipsoid_unique_of_exists
    (n : ℕ) (S : Set (Fin n → ℝ))
    (c₁ c₂ : Fin n → ℝ)
    (A₁ A₂ : SPDMatrix n)
    (hS_convex : Convex ℝ S)
    (h₁ : isLoewnerJohnEllipsoid n S c₁ A₁)
    (h₂ : isLoewnerJohnEllipsoid n S c₂ A₂) :
    ellipsoid n c₁ A₁ = ellipsoid n c₂ A₂ := by
  sorry

end «problem-125»
