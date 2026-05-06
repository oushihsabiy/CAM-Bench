import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-10»
/- [BLOCK Exercise 3.11-(d) | 35 | defn]
A semidefinite program is an optimization problem in which the decision variable is constrained by
linear equalities together with a linear matrix inequality of the form A₀ + sum_{i=1}^k yᵢ Aᵢ succeq
0, and the objective is linear in the decision variable.
-/
structure SemidefiniteProgram (n k m : ℕ) where
  A0 : Matrix (Fin n) (Fin n) ℝ
  A0_symm : A0.IsSymm
  A : Fin k → Matrix (Fin n) (Fin n) ℝ
  A_symm : ∀ i, (A i).IsSymm
  F : Fin m → (Fin k → ℝ)
  g : Fin m → ℝ
  c : Fin k → ℝ

def SemidefiniteProgram.lmiMatrix {n k m : ℕ} (p : SemidefiniteProgram n k m) (y : Fin k → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  p.A0 + ∑ i, y i • p.A i

def SemidefiniteProgram.satisfiesLinearEqualities {n k m : ℕ} (p : SemidefiniteProgram n k m)
    (y : Fin k → ℝ) : Prop :=
  ∀ j, ∑ i, (p.F j) i * y i = p.g j

def SemidefiniteProgram.objective {n k m : ℕ} (p : SemidefiniteProgram n k m) (y : Fin k → ℝ) : ℝ :=
  ∑ i, p.c i * y i

def SemidefiniteProgram.isFeasible {n k m : ℕ} (p : SemidefiniteProgram n k m) (y : Fin k → ℝ) : Prop :=
  p.satisfiesLinearEqualities y ∧
    Matrix.PosSemidef (p.lmiMatrix y)

/-
Exercise 3.11-(d) | 36 | opt_prob

minimize cᵀF(x)⁻¹c over x ∈ ℝⁿ
subject to F(x) ≻ 0
-/
structure StochasticMatrixInverseMinimization (n m : ℕ) where
  Ω : Type
  instMeasurableSpace : MeasurableSpace Ω
  probabilityMeasure : MeasureTheory.Measure Ω
  isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure probabilityMeasure
  F : (Fin n → ℝ) → Matrix (Fin m) (Fin m) ℝ
  cRandom : Ω → Fin m → ℝ
  cRandom_measurable : Measurable cRandom

def StochasticMatrixInverseMinimization.objective {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m) : (Fin n → ℝ) → ℝ :=
  fun x =>
    ∫ ω, dotProduct (p.cRandom ω) (((p.F x)⁻¹).mulVec (p.cRandom ω)) ∂p.probabilityMeasure

def StochasticMatrixInverseMinimization.isFeasible {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m) : (Fin n → ℝ) → Prop :=
  fun x => Matrix.PosDef (p.F x)

attribute [instance] StochasticMatrixInverseMinimization.instMeasurableSpace
attribute [instance] StochasticMatrixInverseMinimization.isProbabilityMeasure

/-
Exercise 3.11-(d) | 37 | opt_prob

minimize t over x ∈ ℝ^n, t ∈ ℝ, Z ∈ S^m

subject to
F(x) ≻ 0,
Z ≽ 0,
\[
\begin{pmatrix}
F(x) & Q^{1/2} \\
Q^{1/2} & Z
\end{pmatrix}
\ ≽ 0,
\]
t = tr(Z).
-/
structure SemidefiniteReformulation (n m : ℕ) where
  F : (Fin n → ℝ) → Matrix (Fin m) (Fin m) ℝ
  F_symm : ∀ x, (F x).IsSymm
  Qsqrt : Matrix (Fin m) (Fin m) ℝ
  Qsqrt_symm : Qsqrt.IsSymm
  x : Fin n → ℝ
  t : ℝ
  Z : Matrix (Fin m) (Fin m) ℝ
  Z_symm : Z.IsSymm
  posDef_F : Matrix.PosDef (F x)
  posSemidef_Z : Matrix.PosSemidef Z
  posSemidef_block :
    Matrix.PosSemidef
      (Matrix.fromBlocks (F x) Qsqrt Qsqrt Z)

def SemidefiniteReformulation.objective {n m : ℕ} (p : SemidefiniteReformulation n m) : ℝ :=
  p.t

def SemidefiniteReformulation.isFeasible {n m : ℕ} (p : SemidefiniteReformulation n m) : Prop :=
  Matrix.PosDef (p.F p.x) ∧
    Matrix.PosSemidef p.Z ∧
    Matrix.PosSemidef (Matrix.fromBlocks (p.F p.x) p.Qsqrt p.Qsqrt p.Z) ∧
    p.t = Matrix.trace p.Z

/- [BLOCK Exercise 3.11-(d) | 38 | thm]
Let n,m ∈ ℕ, let F₀,F₁,dots,Fₙ ∈ S^m, and define F(x)=F₀+sum_{i=1}^n xᵢ Fᵢ for x=(x₁,dots,xₙ)∈ ℝ^n,
where S^m is the set of real symmetric m× m matrices. Let bar c ∈ ℝ^m and S ∈ S^m, and let c be an
m-dimensional random vector satisfying Ec=bar c and E[(c-bar c)(c-bar c)ᵀ]=S. Define Q=S+bar cbar
cᵀ. Prove that for every x ∈ ℝ^n with F(x)succ 0, Ebig[cᵀ F(x)^{-1} cbig]=tr(QF(x)^{-1}).
-/
theorem expected_quadratic_form_eq_trace
    {n m : ℕ}
    (F0 : Matrix (Fin m) (Fin m) ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (cbar : Fin m → ℝ)
    (S : Matrix (Fin m) (Fin m) ℝ)
    (μ : MeasureTheory.Measure (Fin m → ℝ))
    (x : Fin n → ℝ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (hF0_symm : F0.IsSymm)
    (hF_symm : ∀ i, (F i).IsSymm)
    (hS_symm : S.IsSymm)
    (h_integrable_c : MeasureTheory.Integrable (fun c : Fin m → ℝ => c) μ)
    (h_integrable_cov :
      MeasureTheory.Integrable
        (fun c : Fin m → ℝ => Matrix.of fun i j => (c i - cbar i) * (c j - cbar j)) μ)
    (hx :
      Matrix.PosDef
        (F0 + ∑ i, x i • F i))
    (hmean : ∫ c, c ∂μ = cbar)
    (hcov :
      ∫ c, Matrix.of fun i j => (c i - cbar i) * (c j - cbar j) ∂μ = S) :
    ∫ c, dotProduct c (fun i =>
      ((F0 + ∑ j, x j • F j)⁻¹.mulVec c) i) ∂μ
      =
    Matrix.trace
      ((S + Matrix.of fun i j => cbar i * cbar j) *
        (F0 + ∑ j, x j • F j)⁻¹) := by
  sorry

/- [BLOCK Exercise 3.11-(d) | 39 | thm]
Let n,m ∈ ℕ, let F₀,F₁,dots,Fₙ ∈ S^m, and define F(x)=F₀+sum_{i=1}^n xᵢ Fᵢ for x=(x₁,dots,xₙ)∈ ℝ^n,
where S^m is the set of real symmetric m× m matrices. Let bar c ∈ ℝ^m and S ∈ S^m, and let c be an
m-dimensional random vector satisfying Ec=bar c and E[(c-bar c)(c-bar c)ᵀ]=S. Define Q=S+bar cbar
cᵀ. Prove further that the optimization problem stochastic matrix inverse minimization is equivalent
to the semidefinite program semidefinite reformulation.
-/
theorem stochastic_matrix_inverse_minimization_equivalent_to_semidefinite_reformulation
    {n m : ℕ}
    (p : StochasticMatrixInverseMinimization n m)
    (Qsqrt : Matrix (Fin m) (Fin m) ℝ)
    (hQsqrt_symm : Qsqrt.IsSymm)
    (h_objective_trace : ∀ x : Fin n → ℝ,
      p.isFeasible x →
        p.objective x = Matrix.trace ((Qsqrt * Qsqrt) * (p.F x)⁻¹)) :
    (∃ x : Fin n → ℝ,
        p.isFeasible x ∧
        ∀ x' : Fin n → ℝ, p.isFeasible x' → p.objective x ≤ p.objective x') ↔
    (∃ r : SemidefiniteReformulation n m,
        r.F = p.F ∧
        r.Qsqrt = Qsqrt ∧
        SemidefiniteReformulation.isFeasible r ∧
        p.objective r.x = r.objective ∧
        ∀ r' : SemidefiniteReformulation n m,
          r'.F = p.F →
          r'.Qsqrt = Qsqrt →
          SemidefiniteReformulation.isFeasible r' →
          r.objective ≤ r'.objective) := by
  sorry

end «problem-10»
