import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-169»
/-
For a matrix B ∈ ℝ^n × m, the induced ell_∞ - operator norm is ‖B‖_∞ = sup_z ≠ 0 (‖Bz‖_∞)/(‖z‖_∞) =
max_1 ≤ i ≤ n sum_j = 1^m |B_ij|.
-/
open Matrix

def inducedLInfOperatorNorm {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (B : Matrix n m ℝ) : ℝ :=
  sSup (Set.range fun i : n => ∑ j, |B i j|)

/-
A linear estimator hat x = By is minimax if its worst - case estimation error over the prescribed
uncertainty set is minimal; that is, if φ(B) ≤ φ(wideB̃) for every admissible linear estimator hat x
= wideB̃ y.
-/
structure MinimumInfinityNormLeftInverseProblemData
    (n m : Type*) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n] where
  A : Matrix m n ℝ

def MinimumInfinityNormLeftInverseProblemData.standard
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (A : Matrix m n ℝ) : MinimumInfinityNormLeftInverseProblemData n m where
  A := A

abbrev MinimumInfinityNormLeftInverseProblem
    (n m : Type*) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n] :=
  MinimumInfinityNormLeftInverseProblemData n m

def MinimumInfinityNormLeftInverseProblem.standard
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (A : Matrix m n ℝ) : MinimumInfinityNormLeftInverseProblem n m :=
  ⟨A⟩

def MinimumInfinityNormLeftInverseProblem.isFeasible
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (P : MinimumInfinityNormLeftInverseProblem n m) (B : Matrix n m ℝ) : Prop :=
  B * P.A = 1

def MinimumInfinityNormLeftInverseProblem.isOptimal
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (P : MinimumInfinityNormLeftInverseProblem n m) (B : Matrix n m ℝ) : Prop :=
  (B * P.A = 1) ∧
    ∀ B' : Matrix n m ℝ, B' * P.A = 1 → inducedLInfOperatorNorm B ≤ inducedLInfOperatorNorm B'

/-
Consider the linear measurement model y = Ax + v, where A ∈ ℝ^{m × n} has rank n with m ≥ n, x ∈
ℝ^n, y, v ∈ ℝ^m, and the noise satisfies ‖v‖_{∞} ≤ ε, ε ≥ 0, with ‖z‖_{∞} = max_{1 ≤ i ≤ k} |zᵢ| for
z = (z₁, ..., zₖ) ∈ ℝ^k. Restrict the estimator to the linear form x = By, where B ∈ ℝ^{n × m}, and
define the estimation error by e = x - x. For each B, define φ(B) = sup{‖By - x‖_{∞} | y = Ax + v, x
∈
ℝ^n, v ∈ ℝ^m, ‖v‖_{∞} ≤ ε}. Prove that φ(B) = cases ε ‖B‖_{∞}, & if BA = Iₙ,; + ∞, & if BA ≠ Iₙ,
cases where ‖B‖_{∞} = max_{1 ≤ i ≤ n} \sum_{j = 1}^m |B_{ij}| is the induced ell_∞ - operator norm.
-/
theorem phi_eq_epsilon_mul_inducedLInfOperatorNorm_or_top
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (A : Matrix m n ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : Function.Injective fun x : n → ℝ => A *ᵥ x) :
    ∀ B : Matrix n m ℝ,
      (let φ : Matrix n m ℝ → EReal := fun B =>
        sSup
          ((fun p : (n → ℝ) × (m → ℝ) × (m → ℝ) =>
            let x := p.1
            let y := p.2.1
            let v := p.2.2
            (((sSup (Set.range fun i : n => |(B *ᵥ y) i - x i|)) : ℝ) : EReal)) ''
            {p : (n → ℝ) × (m → ℝ) × (m → ℝ) |
              let x := p.1
              let y := p.2.1
              let v := p.2.2
              y = A *ᵥ x + v ∧ sSup (Set.range fun i : m => |v i|) ≤ ε})
      φ B) ≤
        if B * A = 1 then
          ((ε * inducedLInfOperatorNorm B : ℝ) : EReal)
        else
          ⊤ := by
  sorry

/-
Consider the linear measurement model y = Ax + v, where A ∈ ℝ^{m × n} has rank n with m ≥ n, x ∈
ℝ^n, y, v ∈ ℝ^m, and the noise satisfies ‖v‖_{∞} ≤ ε, ε ≥ 0, with ‖z‖_{∞} = max_{1 ≤ i ≤ k} |zᵢ| for
z = (z₁, ..., zₖ) ∈ ℝ^k. Restrict the estimator to the linear form x = By, where B ∈ ℝ^{n × m}, and
define the estimation error by e = x - x. For each B, define φ(B) = sup{‖By - x‖_{∞} | y = Ax + v, x
∈
ℝ^n, v ∈ ℝ^m, ‖v‖_{∞} ≤ ε}. Consequently, prove that the minimax linear estimator is obtained by
solving minimum infinity - norm left inverse.
-/
theorem minimax_linear_estimator_iff_optimal_minimum_infinity_norm_left_inverse
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Nonempty n]
    (A : Matrix m n ℝ) (ε : ℝ)
    (hε : 0 < ε)
    (hA : Function.Injective fun x : n → ℝ => A *ᵥ x)
    (B : Matrix n m ℝ) :
    (let φ : Matrix n m ℝ → EReal := fun B' =>
      sSup
        ((fun p : (n → ℝ) × (m → ℝ) × (m → ℝ) =>
          let x := p.1
          let y := p.2.1
          let v := p.2.2
          (((sSup (Set.range fun i : n => |(B' *ᵥ y) i - x i|)) : ℝ) : EReal)) ''
          {p : (n → ℝ) × (m → ℝ) × (m → ℝ) |
            let x := p.1
            let y := p.2.1
            let v := p.2.2
            y = A *ᵥ x + v ∧ sSup (Set.range fun i : m => |v i|) ≤ ε});
      (∀ Btilde : Matrix n m ℝ, φ B ≤ φ Btilde)) →
    MinimumInfinityNormLeftInverseProblem.isOptimal
      (MinimumInfinityNormLeftInverseProblem.standard A) B := by
  sorry

end «problem-169»
