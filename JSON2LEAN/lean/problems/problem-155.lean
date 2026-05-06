import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-155»
/-
A semidefinite program is an optimization problem of the form langle C, Xrangle: langle Aᵢ, Xrangle
= bᵢ (i = 1, ..., m), X succeq 0, where the variable X is symmetric and langle U, Vrangle = tr(Uᵀ
V).
-/
open scoped Matrix

structure SemidefiniteProgram (n m : ℕ) where
  C : Matrix (Fin n) (Fin n) ℝ
  A : Fin m → Matrix (Fin n) (Fin n) ℝ
  b : Fin m → ℝ
  C_symm : C.IsSymm
  A_symm : ∀ i, (A i).IsSymm

/-
⟨U, V⟩ = tr(UᵀV).
-/
def SemidefiniteProgram.matrixInner {n : ℕ}
    (U V : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (U.transpose * V)

def SemidefiniteProgram.isFeasible {n m : ℕ} (P : SemidefiniteProgram n m)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsSymm ∧
    X.PosSemidef ∧
    (∀ i : Fin m, SemidefiniteProgram.matrixInner (P.A i) X = P.b i)

def SemidefiniteProgram.objective {n m : ℕ} (P : SemidefiniteProgram n m)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  SemidefiniteProgram.matrixInner P.C X

/-
Exercise 3.14

maximize tr(X)

subject to [A X X B] ⪰ 0,

where the variable is X ∈ Sⁿ.
-/
structure TraceMaximizationSemidefiniteProgram (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  B : Matrix (Fin n) (Fin n) ℝ
  A_symm : A.IsSymm
  B_symm : B.IsSymm

def TraceMaximizationSemidefiniteProgram.blockMatrix {n : ℕ}
    (P : TraceMaximizationSemidefiniteProgram n)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks P.A X X P.B

def TraceMaximizationSemidefiniteProgram.isFeasible {n : ℕ}
    (P : TraceMaximizationSemidefiniteProgram n)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsSymm ∧
    (TraceMaximizationSemidefiniteProgram.blockMatrix P X).PosSemidef

def TraceMaximizationSemidefiniteProgram.objective {n : ℕ}
    (_P : TraceMaximizationSemidefiniteProgram n)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace X

def TraceMaximizationSemidefiniteProgram.interp {n : ℕ}
    (t : ℝ)
    (P₁ P₂ : TraceMaximizationSemidefiniteProgram n) :
    TraceMaximizationSemidefiniteProgram n where
  A := t • P₁.A + (1 - t) • P₂.A
  B := t • P₁.B + (1 - t) • P₂.B
  A_symm := (P₁.A_symm.smul t).add (P₂.A_symm.smul (1 - t))
  B_symm := (P₁.B_symm.smul t).add (P₂.B_symm.smul (1 - t))

/-
Let S^n be the set of real symmetric n × n matrices, and let S_{+ +}^n be the set of real symmetric
positive definite n × n matrices. For U, V ∈ S^n, write U preceq V when V - U succeq 0. For M ∈
S_{+ +}^n, let M^{1/2} denote its unique symmetric positive definite square root, and let M^{- 1/2}
denote the inverse of M^{1/2}. Assume that if U, V ∈ S^n satisfy U succeq 0, V succeq 0, and U
preceq V, then U^{1/2} preceq V^{1/2}. For A, B ∈ S_{+ +}^n, define G(A, B) = A^{1/2}
(A^{- 1/2}BA^{- 1/2})^{1/2} A^{1/2}. Show that X = G(A, B) solves the semidefinite program trace
maximization semidefinite program.
-/
theorem geometricMean_solves_traceMaximizationSemidefiniteProgram
    {n : ℕ}
    (P : TraceMaximizationSemidefiniteProgram n)
    (sqrtA invSqrtA sqrtMid : Matrix (Fin n) (Fin n) ℝ)
    (hA_symm : P.A.IsSymm)
    (hB_symm : P.B.IsSymm)
    (hA_pos : P.A.PosDef)
    (hB_pos : P.B.PosDef)
    (h_sqrtA_symm : sqrtA.IsSymm)
    (h_sqrtA_pos : sqrtA.PosDef)
    (h_sqrtA : sqrtA * sqrtA = P.A)
    (h_sqrtA_unique :
      ∀ S : Matrix (Fin n) (Fin n) ℝ,
        S.IsSymm →
        S.PosDef →
        S * S = P.A →
        S = sqrtA)
    (h_invSqrtA_symm : invSqrtA.IsSymm)
    (h_invSqrtA_pos : invSqrtA.PosDef)
    (h_invSqrtA_left : invSqrtA * sqrtA = 1)
    (h_invSqrtA_right : sqrtA * invSqrtA = 1)
    (h_sqrtMid_symm : sqrtMid.IsSymm)
    (h_sqrtMid_pos : sqrtMid.PosDef)
    (h_sqrtMid : sqrtMid * sqrtMid = invSqrtA * P.B * invSqrtA)
    (h_sqrtMid_unique :
      ∀ S : Matrix (Fin n) (Fin n) ℝ,
        S.IsSymm →
        S.PosDef →
        S * S = invSqrtA * P.B * invSqrtA →
        S = sqrtMid)
    (h_sqrt_mono :
      ∀ U V sqrtU sqrtV : Matrix (Fin n) (Fin n) ℝ,
        U.IsSymm →
        V.IsSymm →
        U.PosSemidef →
        V.PosSemidef →
        (V - U).PosSemidef →
        sqrtU.IsSymm →
        sqrtV.IsSymm →
        sqrtU.PosDef →
        sqrtV.PosDef →
        sqrtU * sqrtU = U →
        sqrtV * sqrtV = V →
        (sqrtV - sqrtU).PosSemidef) :
    TraceMaximizationSemidefiniteProgram.isFeasible P (sqrtA * sqrtMid * sqrtA) ∧
      ∀ Y : Matrix (Fin n) (Fin n) ℝ,
        TraceMaximizationSemidefiniteProgram.isFeasible P Y →
          TraceMaximizationSemidefiniteProgram.objective P Y ≤
            TraceMaximizationSemidefiniteProgram.objective P (sqrtA * sqrtMid * sqrtA) := by
  sorry

/-
Let S^n be the set of real symmetric n × n matrices. For positive definite A and B, the matrix
geometric mean G(A, B) is the optimizer of the trace-maximization SDP above. The concavity of
tr G(A, B) follows from this SDP representation: if G₁ and G₂ solve the endpoint SDPs and Gt solves
the SDP for the averaged pair, then tG₁ + (1 - t)G₂ is feasible for the averaged SDP, hence its
trace is at most the optimal trace at the averaged pair. This formulation avoids the false boundary
case in which arbitrary non-principal square roots are used to define G.
-/
theorem trace_geometricMean_concave
    {n : ℕ}
    (t : ℝ)
    (P₁ P₂ : TraceMaximizationSemidefiniteProgram n)
    (G₁ G₂ Gt : Matrix (Fin n) (Fin n) ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1)
    (hG₁_opt :
      TraceMaximizationSemidefiniteProgram.isFeasible P₁ G₁ ∧
        ∀ Y : Matrix (Fin n) (Fin n) ℝ,
          TraceMaximizationSemidefiniteProgram.isFeasible P₁ Y →
            TraceMaximizationSemidefiniteProgram.objective P₁ Y ≤
              TraceMaximizationSemidefiniteProgram.objective P₁ G₁)
    (hG₂_opt :
      TraceMaximizationSemidefiniteProgram.isFeasible P₂ G₂ ∧
        ∀ Y : Matrix (Fin n) (Fin n) ℝ,
          TraceMaximizationSemidefiniteProgram.isFeasible P₂ Y →
            TraceMaximizationSemidefiniteProgram.objective P₂ Y ≤
              TraceMaximizationSemidefiniteProgram.objective P₂ G₂)
    (hGt_opt :
      TraceMaximizationSemidefiniteProgram.isFeasible
        (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂) Gt ∧
        ∀ Y : Matrix (Fin n) (Fin n) ℝ,
          TraceMaximizationSemidefiniteProgram.isFeasible
            (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂) Y →
            TraceMaximizationSemidefiniteProgram.objective
              (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂) Y ≤
              TraceMaximizationSemidefiniteProgram.objective
                (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂) Gt) :
    TraceMaximizationSemidefiniteProgram.isFeasible
        (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂)
        (t • G₁ + (1 - t) • G₂) ∧
      t * TraceMaximizationSemidefiniteProgram.objective P₁ G₁ +
          (1 - t) * TraceMaximizationSemidefiniteProgram.objective P₂ G₂ ≤
        TraceMaximizationSemidefiniteProgram.objective
          (TraceMaximizationSemidefiniteProgram.interp t P₁ P₂) Gt := by
  sorry

end «problem-155»
