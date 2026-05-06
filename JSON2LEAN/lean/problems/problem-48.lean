import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-48»
/-
Let A ∈ S_{+ +}^n and B ∈ S^n. Consider the optimization problem minimize & xᵀ B x; subject
toquad & xᵀ A x ≤ 1, with variable x ∈ ℝ^n.
-/
structure QuadraticInequalityConstrainedProblem (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  B : Matrix (Fin n) (Fin n) ℝ
  A_symm : A.IsSymm
  A_pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (A.mulVec x)
  B_symm : B.IsSymm

def QuadraticInequalityConstrainedProblem.objective
    {n : ℕ} (p : QuadraticInequalityConstrainedProblem n) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (p.B.mulVec x)

def QuadraticInequalityConstrainedProblem.isFeasible
    {n : ℕ} (p : QuadraticInequalityConstrainedProblem n) (x : Fin n → ℝ) : Prop :=
  dotProduct x (p.A.mulVec x) ≤ 1

/-
Let A ∈ S_{+ +}^n and B ∈ S^n, and consider the quadratic inequality - constrained problem. Let M =
A^{- 1/2} B A^{- 1/2}, and let λ_{min}(M) denote the smallest eigenvalue of M. Prove that the
optimal
value is p^star = min(0, λ_{min}(M)).
-/
theorem quadraticInequalityConstrainedProblem_optimalValue_eq_min_zero_minEigenvalue
    {n : ℕ} (p : QuadraticInequalityConstrainedProblem n)
    (AinvSqrt M : Matrix (Fin n) (Fin n) ℝ) (lamMin : ℝ)
    (hAinvSqrt : AinvSqrt * AinvSqrt = p.A⁻¹)
    (hM : M = AinvSqrt * p.B * AinvSqrt)
    (hAinvSqrt_bijective : Function.Bijective AinvSqrt.mulVec)
    (hConstraintTransform :
      ∀ y : Fin n → ℝ,
        QuadraticInequalityConstrainedProblem.isFeasible p (AinvSqrt.mulVec y) ↔
          dotProduct y y ≤ 1)
    (hObjectiveTransform :
      ∀ y : Fin n → ℝ,
        QuadraticInequalityConstrainedProblem.objective p (AinvSqrt.mulVec y) =
          dotProduct y (M.mulVec y))
    (hM_symm : M.IsSymm)
    (hRayleighLower :
      ∀ y : Fin n → ℝ, lamMin * dotProduct y y ≤ dotProduct y (M.mulVec y))
    (hLamMin :
      (∃ v : Fin n → ℝ, v ≠ 0 ∧ M.mulVec v = lamMin • v) ∧
      ∀ μ : ℝ, (∃ v : Fin n → ℝ, v ≠ 0 ∧ M.mulVec v = μ • v) → lamMin ≤ μ) :
    sInf
        (QuadraticInequalityConstrainedProblem.objective p ''
          {x : Fin n → ℝ | QuadraticInequalityConstrainedProblem.isFeasible p x}) =
      min 0 lamMin := by
  sorry

/-
Let A ∈ S_{+ +}^n and B ∈ S^n, and consider the quadratic inequality - constrained problem. Let M =
A^{- 1/2} B A^{- 1/2}, and let λ_{min}(M) denote the smallest eigenvalue of M. If B ∈ S_ + ^n, then
p^star = 0 and x* = 0 is an optimal solution.
-/
theorem quadraticInequalityConstrainedProblem_optimalValue_zero_and_zero_optimal
    {n : ℕ} (p : QuadraticInequalityConstrainedProblem n)
    (hBpsd : ∀ x : Fin n → ℝ, 0 ≤ QuadraticInequalityConstrainedProblem.objective p x) :
    sInf
        (QuadraticInequalityConstrainedProblem.objective p ''
          {x : Fin n → ℝ | QuadraticInequalityConstrainedProblem.isFeasible p x}) = 0 ∧
      QuadraticInequalityConstrainedProblem.isFeasible p 0 ∧
      QuadraticInequalityConstrainedProblem.objective p 0 = 0 := by
  sorry

/-
Let A ∈ S_{+ +}^n and B ∈ S^n, and consider the quadratic inequality - constrained problem. Let M =
A^{- 1/2} B A^{- 1/2}, and let λ_{min}(M) denote the smallest eigenvalue of M. If λ_{min}(M) < 0,
then
for any unit eigenvector y of M with eigenvalue λ_{min}(M), the vector x* = A^{- 1/2} y is feasible
and optimal, and (x*)ᵀ B x* = λ_{min}(M).
-/
theorem quadraticInequalityConstrainedProblem_negative_minEigenvalue_eigenvector_gives_optimal_solution
    {n : ℕ} (p : QuadraticInequalityConstrainedProblem n)
    (AinvSqrt M : Matrix (Fin n) (Fin n) ℝ) (lamMin : ℝ)
    (hAinvSqrt : AinvSqrt * AinvSqrt = p.A⁻¹)
    (hM : M = AinvSqrt * p.B * AinvSqrt)
    (hAinvSqrt_bijective : Function.Bijective AinvSqrt.mulVec)
    (hConstraintTransform :
      ∀ y : Fin n → ℝ,
        QuadraticInequalityConstrainedProblem.isFeasible p (AinvSqrt.mulVec y) ↔
          dotProduct y y ≤ 1)
    (hObjectiveTransform :
      ∀ y : Fin n → ℝ,
        QuadraticInequalityConstrainedProblem.objective p (AinvSqrt.mulVec y) =
          dotProduct y (M.mulVec y))
    (hM_symm : M.IsSymm)
    (hRayleighLower :
      ∀ y : Fin n → ℝ, lamMin * dotProduct y y ≤ dotProduct y (M.mulVec y))
    (hLamMin :
      (∃ v : Fin n → ℝ, v ≠ 0 ∧ M.mulVec v = lamMin • v) ∧
      ∀ μ : ℝ, (∃ v : Fin n → ℝ, v ≠ 0 ∧ M.mulVec v = μ • v) → lamMin ≤ μ)
    (hLamMinNeg : lamMin < 0)
    (y : Fin n → ℝ)
    (hyEigen : M.mulVec y = lamMin • y)
    (hyUnit : dotProduct y y = 1) :
    QuadraticInequalityConstrainedProblem.isFeasible p (AinvSqrt.mulVec y) ∧
      QuadraticInequalityConstrainedProblem.objective p (AinvSqrt.mulVec y) = lamMin ∧
      QuadraticInequalityConstrainedProblem.objective p (AinvSqrt.mulVec y) =
        sInf
          (QuadraticInequalityConstrainedProblem.objective p ''
            {x : Fin n → ℝ | QuadraticInequalityConstrainedProblem.isFeasible p x}) := by
  sorry

end «problem-48»
