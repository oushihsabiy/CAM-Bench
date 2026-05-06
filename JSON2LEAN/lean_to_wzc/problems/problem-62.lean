import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-62»
/- [BLOCK Exercise 2.26-(b) | 31 | defn]
For symmetric matrices A, B ∈ S^n, A preceq B means that B - A succeq 0.
-/
def loewnerOrder {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm ∧ B.IsSymm ∧ Matrix.PosSemidef (B - A)

/- [BLOCK Exercise 2.26-(b) | 32 | defn]
If X = [ X_{11} & X_{12}; X_{12}ᵀ & X_{22} ] with X_{22} invertible, then the Schur complement of
X_{22} in X is X_{11} - X_{12}X_{22}^{-1}X_{12}ᵀ.
-/
def schurComplement {n m : ℕ} (X11 : Matrix (Fin n) (Fin n) ℝ)
    (X12 : Matrix (Fin n) (Fin m) ℝ)
    (X22 : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  X11 - X12 * X22⁻¹ * X12.transpose

/- [BLOCK Exercise 2.26-(b) | 33 | opt_prob]
aligned
minimize quad & log det Y^{-1} ;
subject to quad & [ Y & 0 ; 0 & 0 ] preceq [ X_{11} & X_{12} ; X_{12}ᵀ & X_{22} ],
aligned
with domain S_{++}^m for log det Y^{-1}.
-/
structure LogDetSemidefiniteProgram where
  n : ℕ
  m : ℕ
  X11 : Matrix (Fin m) (Fin m) ℝ
  X12 : Matrix (Fin m) (Fin n) ℝ
  X22 : Matrix (Fin n) (Fin n) ℝ
  Y : Matrix (Fin m) (Fin m) ℝ
  X11_symm : X11.IsSymm
  X22_symm : X22.IsSymm
  Y_symm : Y.IsSymm
  Y_posDef : Matrix.PosDef Y
  block_constraint :
    (Matrix.fromBlocks Y
      (0 : Matrix (Fin m) (Fin n) ℝ)
      (0 : Matrix (Fin n) (Fin m) ℝ)
      (0 : Matrix (Fin n) (Fin n) ℝ)).IsSymm ∧
    (Matrix.fromBlocks X11 X12 X12.transpose X22).IsSymm ∧
    Matrix.PosSemidef
      ((Matrix.fromBlocks X11 X12 X12.transpose X22) -
        Matrix.fromBlocks Y
          (0 : Matrix (Fin m) (Fin n) ℝ)
          (0 : Matrix (Fin n) (Fin m) ℝ)
          (0 : Matrix (Fin n) (Fin n) ℝ))

def LogDetSemidefiniteProgram.objective (p : LogDetSemidefiniteProgram) : ℝ :=
  Real.log (Matrix.det (p.Y⁻¹))

def LogDetSemidefiniteProgram.isFeasible (p : LogDetSemidefiniteProgram) : Prop :=
  (Matrix.fromBlocks p.Y
    (0 : Matrix (Fin p.m) (Fin p.n) ℝ)
    (0 : Matrix (Fin p.n) (Fin p.m) ℝ)
    (0 : Matrix (Fin p.n) (Fin p.n) ℝ)).IsSymm ∧
  (Matrix.fromBlocks p.X11 p.X12 p.X12.transpose p.X22).IsSymm ∧
  Matrix.PosSemidef
    ((Matrix.fromBlocks p.X11 p.X12 p.X12.transpose p.X22) -
      Matrix.fromBlocks p.Y
        (0 : Matrix (Fin p.m) (Fin p.n) ℝ)
        (0 : Matrix (Fin p.n) (Fin p.m) ℝ)
        (0 : Matrix (Fin p.n) (Fin p.n) ℝ))

def LogDetSemidefiniteProgram.schurComplementData (p : LogDetSemidefiniteProgram) :
    Matrix (Fin p.m) (Fin p.m) ℝ :=
  schurComplement p.X11 p.X12 p.X22

/- [BLOCK Exercise 2.26-(b) | 34 | thm]
Let n,m ∈ ℕ with m ≤ n. Let S^n be the set of real symmetric n × n matrices and S_{++}^n the set of
real symmetric positive definite n × n matrices. For A,B ∈ S^n, A preceq B means B-A succeq 0. Let P
∈ ℝ^{n × m} have rank m, and let f:S^n → ℝ have domain dom f=S_{++}^n, defined by f(X)=logdet(Pᵀ
X^{-1}P). Assume P=[ I ; 0 ], where I is the m × m identity matrix. Let X ∈ S_{++}^n be partitioned
as X=[ X_{11} & X_{12} ; X_{12}ᵀ & X_{22} ], where X_{11} ∈ S^m, X_{12} ∈ ℝ^{m × (n-m)}, and X_{22}
∈ S^{n-m}. Show that the optimization problem aligned minimize quad & log det Y^{-1} ; subject to
quad & [ Y & 0 ; 0 & 0 ] preceq [ X_{11} & X_{12} ; X_{12}ᵀ & X_{22} ], aligned Take S_{++}^m as the
domain of log det Y^{-1}. has the solution Y = X_{11} - X_{12} X_{22}^{-1} X_{12}ᵀ.
-/
theorem schur_complement_solves_logDetSemidefiniteProgram
    {n m : ℕ} (hmn : m ≤ n)
    (X11 : Matrix (Fin m) (Fin m) ℝ)
    (X12 : Matrix (Fin m) (Fin (n - m)) ℝ)
    (X22 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)
    (hX11symm : X11.IsSymm)
    (hX22symm : X22.IsSymm)
    (hXpos :
      Matrix.PosDef (Matrix.fromBlocks X11 X12 X12.transpose X22)) :
    let Yopt := schurComplement X11 X12 X22
    ((Matrix.fromBlocks Yopt
        (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
        (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
        (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)).IsSymm ∧
      (Matrix.fromBlocks X11 X12 X12.transpose X22).IsSymm ∧
      Matrix.PosSemidef
        ((Matrix.fromBlocks X11 X12 X12.transpose X22) -
          Matrix.fromBlocks Yopt
            (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
            (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
            (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ))) ∧
    Matrix.PosDef Yopt ∧
    ∀ Y : Matrix (Fin m) (Fin m) ℝ,
      Y.IsSymm →
      Matrix.PosDef Y →
      ((Matrix.fromBlocks Y
          (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
          (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
          (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)).IsSymm ∧
        (Matrix.fromBlocks X11 X12 X12.transpose X22).IsSymm ∧
        Matrix.PosSemidef
          ((Matrix.fromBlocks X11 X12 X12.transpose X22) -
            Matrix.fromBlocks Y
              (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
              (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
              (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ))) →
      Real.log (Matrix.det (Yopt⁻¹)) ≤ Real.log (Matrix.det (Y⁻¹)) := by
  sorry
end «problem-62»
