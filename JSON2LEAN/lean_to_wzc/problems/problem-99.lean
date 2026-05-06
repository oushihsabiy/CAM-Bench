import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-99»
/-
Consider the optimization problem min_{x∈ℝ^n} x^→p A x + 2b^→p x, s. t. ‖x‖_2 ≤ 1, where A∈S^n and
b∈ℝ^n.
-/
structure QuadraticUnitBallProblem (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  b : Fin n → ℝ
  A_symm : Matrix.IsSymm A

def QuadraticUnitBallProblem.objective {n : ℕ} (p : QuadraticUnitBallProblem n) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (fun i => ∑ j, p.A i j * x j) + 2 * dotProduct p.b x

def QuadraticUnitBallProblem.isFeasible {n : ℕ} (p : QuadraticUnitBallProblem n) (x : Fin n → ℝ) : Prop :=
  dotProduct x x ≤ (1 : ℝ)

/-
min_{X∈S^n, x∈ℝ^n} &langle A, Xrangle + 2b^→p x; s. t. &tr(X) ≤ 1,; &(X & x; x^→p & 1)succeq 0.
-/
structure ShorLiftingSDP (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  A_symm : Matrix.IsSymm A
  b : Fin n → ℝ

def ShorLiftingSDP.objective {n : ℕ} (sdp : ShorLiftingSDP n) :
    (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) → ℝ :=
  fun p =>
    let X := p.1
    let x := p.2
    Matrix.trace (sdp.A * X) + 2 * dotProduct sdp.b x

def ShorLiftingSDP.feasible {n : ℕ} (sdp : ShorLiftingSDP n) :
    Set (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) :=
  {p |
    let X := p.1
    let x := p.2
    Matrix.IsSymm X ∧
    Matrix.trace X ≤ 1 ∧
    Matrix.PosSemidef
      (Matrix.fromBlocks X (fun i _ => x i) (fun _ j => x j)
        (![![1]] : Matrix (Fin 1) (Fin 1) ℝ))}

def ShorLiftingSDP.isFeasible {n : ℕ} (sdp : ShorLiftingSDP n) : Prop :=
  ∃ z, z ∈ sdp.feasible

/-
Consider the quadratic unit - ball problem. In addition, prove that the dual of this dual problem
can
be represented as the following SDP (Shor lifting): min_{X∈S^n, x∈ℝ^n} &langle A, Xrangle + 2b^→p x;
s. t. &tr(X) ≤ 1,; &(X & x; x^→p & 1)succeq 0.
-/
theorem quadraticUnitBallProblem_dual_of_dual_eq_shor_lifting
    {n : ℕ} (p : QuadraticUnitBallProblem n) :
    ∃ sdp : ShorLiftingSDP n,
      sdp.A = p.A ∧
      sdp.A.IsSymm ∧
      sdp.b = p.b ∧
      sdp.objective =
        (fun q =>
          let X := q.1
          let x := q.2
          Matrix.trace (p.A * X) + 2 * dotProduct p.b x) ∧
      sdp.feasible =
        {q |
          let X := q.1
          let x := q.2
          Matrix.IsSymm X ∧
          Matrix.trace X ≤ 1 ∧
          Matrix.PosSemidef
            (Matrix.fromBlocks X (fun i _ => x i) (fun _ j => x j)
              (![![1]] : Matrix (Fin 1) (Fin 1) ℝ))} := by
  sorry

end «problem-99»
