import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-103»
/-
Let A ⊆ ℝ^n and B ⊆ ℝ^m be convex. Let f: ℝ^n × ℝ^m → ℝ be differentiable, convex in x for each
fixed z, and concave in z for each fixed x. If (x̃, z̃) ∈ A × B satisfies ∇f(x̃, z̃) = 0, prove that
for all x ∈ A and z ∈ B, f(x̃, z) ≤ f(x̃, z̃) ≤ f(x, z̃).
-/


theorem saddle_inequalities_of_gradient_zero
    {n m : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ}
    {xtilde : EuclideanSpace ℝ (Fin n)}
    {ztilde : EuclideanSpace ℝ (Fin m)}
    (hA : Convex ℝ A)
    (hB : Convex ℝ B)
    (hxz : xtilde ∈ A ∧ ztilde ∈ B)
    (hconvex : ∀ z ∈ B, ConvexOn ℝ A (fun x => f (x, z)))
    (hconcave : ∀ x ∈ A, ConvexOn ℝ B (fun z => -f (x, z)))
    (hinf_bddBelow :
      ∀ z ∈ B, BddBelow {s : ℝ | ∃ x ∈ A, s = f (x, z)})
    (hsup_bddAbove :
      ∀ x ∈ A, BddAbove {s : ℝ | ∃ z ∈ B, s = f (x, z)})
    (hleft_bddAbove :
      BddAbove {r : ℝ | ∃ z ∈ B, r = sInf {s : ℝ | ∃ x ∈ A, s = f (x, z)}})
    (hright_bddBelow :
      BddBelow {r : ℝ | ∃ x ∈ A, r = sSup {s : ℝ | ∃ z ∈ B, s = f (x, z)}})
    (hgrad_zero :
      HasFDerivAt f
        (0 :
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ)
        (xtilde, ztilde)) :
    ∀ x ∈ A, ∀ z ∈ B, f (xtilde, z) ≤ f (xtilde, ztilde) ∧ f (xtilde, ztilde) ≤ f (x, ztilde) := by
  sorry

/-
Under the same assumptions, prove sup_{z∈B} \inf_{x∈A} f(x, z) = \inf_{x∈A} sup_{z∈B} f(x, z), and
that the common value equals f(x̃, z̃).
-/
theorem minimax_eq_of_gradient_zero
    {n m : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ}
    {xtilde : EuclideanSpace ℝ (Fin n)}
    {ztilde : EuclideanSpace ℝ (Fin m)}
    (hA : Convex ℝ A)
    (hB : Convex ℝ B)
    (hxz : xtilde ∈ A ∧ ztilde ∈ B)
    (hconvex : ∀ z ∈ B, ConvexOn ℝ A (fun x => f (x, z)))
    (hconcave : ∀ x ∈ A, ConvexOn ℝ B (fun z => -f (x, z)))
    (hinf_bddBelow :
      ∀ z ∈ B, BddBelow {s : ℝ | ∃ x ∈ A, s = f (x, z)})
    (hsup_bddAbove :
      ∀ x ∈ A, BddAbove {s : ℝ | ∃ z ∈ B, s = f (x, z)})
    (hleft_bddAbove :
      BddAbove {r : ℝ | ∃ z ∈ B, r = sInf {s : ℝ | ∃ x ∈ A, s = f (x, z)}})
    (hright_bddBelow :
      BddBelow {r : ℝ | ∃ x ∈ A, r = sSup {s : ℝ | ∃ z ∈ B, s = f (x, z)}})
    (hgrad_zero :
      HasFDerivAt f
        (0 :
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ)
        (xtilde, ztilde)) :
    sSup {r : ℝ | ∃ z ∈ B, r = sInf {s : ℝ | ∃ x ∈ A, s = f (x, z)}} =
      sInf {r : ℝ | ∃ x ∈ A, r = sSup {s : ℝ | ∃ z ∈ B, s = f (x, z)}} ∧
    sSup {r : ℝ | ∃ z ∈ B, r = sInf {s : ℝ | ∃ x ∈ A, s = f (x, z)}} =
      f (xtilde, ztilde) := by
  sorry

end «problem-103»
