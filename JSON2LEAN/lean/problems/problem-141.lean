import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-141»

/- [BLOCK Exercise 11.16-(d) | 39 | defn]
A cone K ⊆ ℝ^n is called proper if it is convex, closed, has nonempty interior, and is pointed,
i.e., K cap (-K) = {0}.
-/
def IsProperCone {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  (∀ ⦃x : Fin n → ℝ⦄, x ∈ K → ∀ ⦃a : ℝ⦄, 0 ≤ a → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  (Set.Nonempty (interior K)) ∧
  K ∩ (-K) = ({0} : Set (Fin n → ℝ))

/- [BLOCK Exercise 11.16-(d) | 40 | defn]
Let K ⊆ ℝ^n be a proper cone. A function psi : int K → ℝ is called a generalized logarithm for
K of degree θ if psi ∈ C^2(int K), ∇^2 psi(y) is invertible for every y ∈ int K, and
psi(ty)=psi(y)+θ log t for all y ∈ int K and all t>0.
-/
def IsGeneralizedLogarithmOfDegree
    {n : ℕ}
    (K : Set (Fin n → ℝ))
    (ψ : interior K → ℝ)
    (θ : ℝ) : Prop :=
  IsProperCone K ∧
  (∃ ψext : (Fin n → ℝ) → ℝ,
    ContDiffOn ℝ 2 ψext (interior K) ∧
    (∀ y : interior K, ψ y = ψext y) ∧
    (∀ y : interior K,
      IsUnit
        ((Matrix.of fun i j : Fin n =>
            (fderiv ℝ
                (fun x : Fin n → ℝ =>
                  (fderiv ℝ ψext x) (Pi.single j (1 : ℝ)))
                (y : Fin n → ℝ))
              (Pi.single i (1 : ℝ))).det)) ∧
    (∀ (y : interior K) {t : ℝ}, 0 < t →
      ∃ hy' : t • (y : Fin n → ℝ) ∈ interior K,
        ψ ⟨t • (y : Fin n → ℝ), hy'⟩ = ψ y + θ * Real.log t))

/- [BLOCK Exercise 11.16-(d) | 41 | defn]
For a generalized logarithm psi : int K → ℝ, the degree is the scalar θ ∈ ℝ such that
psi(ty)=psi(y)+θ log t for all y ∈ int K and all t>0.
-/
def GeneralizedLogarithmDegree
    {n : ℕ}
    (K : Set (Fin n → ℝ))
    (ψ : interior K → ℝ)
    (θ : ℝ) : Prop :=
  ∀ (y : interior K) {t : ℝ}, 0 < t →
    ∃ hy' : t • (y : Fin n → ℝ) ∈ interior K,
      ψ ⟨t • (y : Fin n → ℝ), hy'⟩ = ψ y + θ * Real.log t

/- [BLOCK Exercise 11.16-(d) | 42 | thm]
Let K ⊆ ℝ^n be a proper cone, and write y succ_K 0 for y ∈ int K. Let psi : int K → ℝ be a
generalized logarithm for K of degree θ, meaning that psi is twice continuously differentiable on
int K, ∇^2 psi(y) is invertible for every y ∈ int K, and
psi(ty)=psi(y)+θ log t for all y ∈ int K,\ t>0.
Prove that for every y succ_K 0,
∇ psi(y)ᵀ (∇^2 psi(y))^{-1} ∇ psi(y) = -θ.
-/
theorem generalizedLogarithm_gradient_hessian_inverse_quadratic_form_eq_neg_degree
    {n : ℕ}
    {K : Set (Fin n → ℝ)}
    {ψ : interior K → ℝ}
    {θ : ℝ}
    (hψ : IsGeneralizedLogarithmOfDegree K ψ θ) :
    ∀ y : interior K,
      let ψext : (Fin n → ℝ) → ℝ := Classical.choose hψ.2
      let g : Fin n → ℝ := fun i =>
        (fderiv ℝ ψext (y : Fin n → ℝ)) (Pi.single i (1 : ℝ))
      let H : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j : Fin n =>
        (fderiv ℝ
            (fun x : Fin n → ℝ =>
              (fderiv ℝ ψext x) (Pi.single j (1 : ℝ)))
            (y : Fin n → ℝ))
          (Pi.single i (1 : ℝ))
      dotProduct g (H⁻¹.mulVec g) = -θ := by
  sorry

end «problem-141»