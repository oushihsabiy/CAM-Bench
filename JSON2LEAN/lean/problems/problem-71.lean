import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-71»

-- Exercise_3_8

/- [BLOCK Exercise 3.8 | 1 | thm]
Let C⊆ ℝ^n and let f:C→ ℝ be twice differentiable. For a symmetric matrix A, Asucceq 0 means that zᵀ
A z≥ 0 for all z∈ℝ^n. Prove that f is convex on C if and only if C is convex and ∇^2 f(x)succeq 0
for all x∈ C.
-/
open scoped BigOperators
theorem convexOn_iff_convex_and_hessian_posSemidef
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hCconv : Convex ℝ C)
    (hCopen : IsOpen C)
    (_hC2 : ∀ x ∈ C, ContDiffAt ℝ 2 f x) :
    ConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ z : Fin n → ℝ,
        0 ≤
          ∑ i : Fin n, z i *
            ∑ j : Fin n,
              z j *
                ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
                  (Pi.single i (1 : ℝ))) := by
  sorry

end «problem-71»