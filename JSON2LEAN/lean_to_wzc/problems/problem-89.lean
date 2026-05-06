import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-89»

-- Exercise_2_10__b_

/- [BLOCK Exercise 2.10-(b) | 5 | thm]
Let C be the quadratic sublevel set {x ∈ ℝ^n | xᵀ A x + bᵀ x + c ≤ 0}, and let H be the affine
hyperplane {x ∈ ℝ^n | gᵀ x + h = 0}, with g ≠ 0. Assume there exists λ ∈ ℝ such that A + λ g gᵀ is
positive semidefinite. Prove that C ∩ H is convex.
-/
theorem quadratic_sublevel_inter_affine_hyperplane_convex
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b g : n → ℝ) (c h : ℝ)
    (hA_symm : A.IsSymm)
    (hg : g ≠ 0)
    (hlam : ∃ lam : ℝ,
      ∀ x : n → ℝ,
        0 ≤ x ⬝ᵥ (((A + lam • Matrix.of fun i j => g i * g j) *ᵥ x))) :
    Convex ℝ
      ({x : n → ℝ |
          x ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ x + c ≤ 0} ∩
        {x : n → ℝ | g ⬝ᵥ x + h = 0}) := by
  sorry

/- [BLOCK Exercise 2.10-(b) | 6 | thm]
Show that the converse of the preceding statement is false in general. That is, give data n, A, b,
c, g, and h with g ≠ 0 such that C ∩ H is convex, but A + λ g gᵀ is not positive semidefinite for
every λ ∈ ℝ.
-/
theorem converse_quadratic_hyperplane_convexity_false :
    ∃ (n : Type*) (_ : Fintype n) (_ : DecidableEq n)
      (A : Matrix n n ℝ) (b g : n → ℝ) (c h : ℝ),
      A.IsSymm ∧
      g ≠ 0 ∧
      Convex ℝ
        ({x : n → ℝ |
            x ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ x + c ≤ 0} ∩
          {x : n → ℝ | g ⬝ᵥ x + h = 0}) ∧
      ∀ lam : ℝ,
        ¬ ∀ x : n → ℝ,
            0 ≤ x ⬝ᵥ (((A + lam • Matrix.of fun i j => g i * g j) *ᵥ x)) := by
  sorry

end «problem-89»