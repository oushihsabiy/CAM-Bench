import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-134»
/-
Let f: ℝ^n o ℝ be twice differentiable, and assume that dom f ⊆ ℝ^n is convex. Let F ∈ ℝ^{n \times
m}
and x ∈ ℝ^n. Define ilde f: ℝ^m o ℝ by ilde f(z) = f(Fz + x), dom ilde f = {z∈ℝ^m| Fz + x∈dom f}.
For a
symmetric matrix M, write Msucceq 0 if uᵀ M u ≥ 0 for all u∈ℝ^m. Prove that ilde f is convex on dom
ilde f if and only if for every z∈dom ilde f, Fᵀ abla^2 f(Fz + x)Fsucceq 0.
-/
open scoped Matrix
theorem affine_precomp_convexOn_iff_hessian_pullback_psd
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (domf : Set (n → ℝ)) (f : (n → ℝ) → ℝ) (F : Matrix n m ℝ) (xhat : n → ℝ)
    (hconvex : Convex ℝ domf)
    (hdomf_open : IsOpen domf)
    (hC2 : ∀ x : n → ℝ, x ∈ domf → ContDiffAt ℝ 2 f x) :
    (let dom_tilde : Set (m → ℝ) := {z : m → ℝ | (fun i => (∑ j, F i j * z j) + xhat i) ∈ domf}
     let tilde_f : {z : m → ℝ // z ∈ dom_tilde} → ℝ :=
       fun z => f (fun i => (∑ j, F i j * z.1 j) + xhat i)
     ConvexOn ℝ dom_tilde
       (fun z => f (fun i => (∑ j, F i j * z j) + xhat i)))
      ↔
    (let dom_tilde : Set (m → ℝ) := {z : m → ℝ | (fun i => (∑ j, F i j * z j) + xhat i) ∈ domf}
     let hess : (m → ℝ) → Matrix n n ℝ :=
       fun z =>
         Matrix.of (fun i j : n =>
           fderiv ℝ
             (fun y : n → ℝ => (fderiv ℝ f y) (Pi.single j (1 : ℝ)))
             (fun k => (∑ l, F k l * z l) + xhat k)
             (Pi.single i (1 : ℝ)))
     ∀ z : m → ℝ,
       z ∈ dom_tilde →
       ∀ u : m → ℝ, 0 ≤ ∑ i, u i * ∑ j, ((F.transpose * hess z * F) i j) * u j) := by
  sorry

end «problem-134»
