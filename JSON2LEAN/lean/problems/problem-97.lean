import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-97»

/- [BLOCK Exercise 19.5-(a) | 10 | defn]
A primal-dual solution is a tuple of primal and dual variables satisfying the first-order optimality
conditions for a constrained optimization problem. For a nonlinear program with equality
constraints, inequality constraints, and slack variables, this means primal feasibility, dual
feasibility, stationarity, and complementarity.
-/
structure PrimalDualSolution
    (n mₑ mᵢ : ℕ)
    (f : (Fin n → ℝ) → ℝ)
    (g : Fin mₑ → (Fin n → ℝ) → ℝ)
    (h : Fin mᵢ → (Fin n → ℝ) → ℝ) where
  x : Fin n → ℝ
  lam_eq : Fin mₑ → ℝ
  lam_ineq : Fin mᵢ → ℝ
  s : Fin mᵢ → ℝ
  primal_eq_feasible : ∀ i, g i x = 0
  primal_ineq_feasible : ∀ i, h i x - s i = 0
  dual_feasible : ∀ i, 0 ≤ lam_ineq i
  slack_feasible : ∀ i, 0 ≤ s i
  stationarity :
    ∀ dx,
      fderiv ℝ f x dx
        = ∑ i, lam_eq i * (fderiv ℝ (g i) x) dx
          + ∑ i, lam_ineq i * (fderiv ℝ (h i) x) dx
  complementarity : ∀ i, lam_ineq i * s i = 0

/- [BLOCK Exercise 19.5-(a) | 11 | defn]
A nonlinear programming problem is an optimization problem of the form min_x f(x) subject to
c_E(x)=0 and c_I(x)≥ 0, or equivalently c_I(x)-s=0 with s≥ 0, where at least one of f, c_E, and c_I
is nonlinear.
-/
def IsNonlinearProgrammingProblem
    (n mₑ mᵢ : ℕ)
    (f : (Fin n → ℝ) → ℝ)
    (cE : Fin mₑ → (Fin n → ℝ) → ℝ)
    (cI : Fin mᵢ → (Fin n → ℝ) → ℝ) : Prop :=
  ¬ (IsLinearMap ℝ f ∧
      (∀ i : Fin mₑ, IsLinearMap ℝ (cE i)) ∧
      (∀ i : Fin mᵢ, IsLinearMap ℝ (cI i)))

/- [BLOCK Exercise 19.5-(a) | 12 | defn]
A slack variable is a variable introduced to convert an inequality constraint into an equality
constraint; for example, c_I(x)≥ 0 is rewritten as c_I(x)-s=0 with s≥ 0.
-/
def IsSlackVariable
    (n mᵢ : ℕ)
    (cI : Fin mᵢ → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ)
    (s : Fin mᵢ → ℝ) : Prop :=
  (∀ i, 0 ≤ s i) ∧ ∀ i, cI i x - s i = 0

/- [BLOCK Exercise 19.5-(a) | 13 | defn]
LICQ holds at a feasible point if the gradients of all equality constraints together with the
gradients of all active inequality constraints are linearly independent.
-/
def LICQ
    (n mₑ mᵢ : ℕ)
    (cE : Fin mₑ → (Fin n → ℝ) → ℝ)
    (cI : Fin mᵢ → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : Prop :=
  (∀ i, cE i x = 0) ∧
  (∀ i, 0 ≤ cI i x) ∧
  LinearIndependent ℝ
    (fun k : (Fin mₑ) ⊕ {i : Fin mᵢ // cI i x = 0} =>
      match k with
      | Sum.inl i => fderiv ℝ (cE i) x
      | Sum.inr i => fderiv ℝ (cI i.1) x)

/- [BLOCK Exercise 19.5-(a) | 14 | defn]
At a feasible primal-dual point for inequality constraints with slack variables, strict
complementarity means that for each index i, sᵢ zᵢ=0, sᵢ≥ 0, zᵢ≥ 0, and sᵢ+zᵢ>0.
-/
def StrictComplementarity
    (mᵢ : ℕ)
    (s z : Fin mᵢ → ℝ) : Prop :=
  (∀ i, s i * z i = 0) ∧
  (∀ i, 0 ≤ s i) ∧
  (∀ i, 0 ≤ z i) ∧
  ∀ i, 0 < s i + z i

/- [BLOCK Exercise 19.5-(a) | 15 | defn]
An inequality constraint is active at a feasible point if it holds with equality; in slack-variable
form c_I(x)-s=0, this is equivalent to sᵢ=0 for the corresponding index i.
-/
def IsActiveInequality
    (n mᵢ : ℕ)
    (cI : Fin mᵢ → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ)
    (s : Fin mᵢ → ℝ)
    (i : Fin mᵢ) : Prop :=
  IsSlackVariable n mᵢ cI x s ∧ s i = 0

/- [BLOCK Exercise 19.5-(a) | 16 | defn]
For a matrix A, the kernel is ker(A)={d : Ad=0}.
-/
def MatrixKernel
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {d | A.mulVec d = 0}

/- [BLOCK Exercise 19.5-(a) | 17 | defn]
A square matrix M is nonsingular if it is invertible; equivalently, if ker(M)={0}.
-/
def IsNonsingular
    {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Nonempty (Invertible M)

/- [BLOCK Exercise 19.5-(a) | 18 | thm]
Let x ∈ ℝ^n, s ∈ ℝ^{m_I}, y ∈ ℝ^{m_E}, and z ∈ ℝ^{m_I} be a primal-dual solution of a nonlinear
programming problem with equality constraints c_E(x)=0 and inequality constraints c_I(x)-s=0, where
s is a slack variable. Define
A_E(x)=[
∇ c_{E,1}(x)ᵀ;
vdots;
∇ c_{E,m_E}(x)ᵀ
]∈ ℝ^{m_E× n},
A_I(x)=[
∇ c_{I,1}(x)ᵀ;
vdots;
∇ c_{I,m_I}(x)ᵀ
]∈ ℝ^{m_I× n},
and
S=diag(s₁,dots,s_{m_I}),
Z=diag(z₁,dots,z_{m_I}).
Assume that (x,s,y,z) satisfies LICQ and strict complementarity, so for each i=1,dots,m_I,
sᵢ zᵢ=0,
sᵢ≥ 0,
zᵢ≥ 0,
sᵢ+zᵢ>0.
Let H=∇_{xx}^2 L_c(x,s,y,z). Let mathcal A be the matrix whose rows are the rows of A_E(x) together
with the rows of A_I(x) corresponding to the active inequalities, i.e. those indices i for which
sᵢ=0 (equivalently, by strict complementarity, zᵢ>0). Assume that
dᵀ H d > 0
quadfor every nonzero d ∈ ker(mathcal A).
Prove that the primal-dual matrix
[
H & 0 & -A_E(x)ᵀ & -A_I(x)ᵀ;
0 & Z & 0 & S;
A_E(x) & 0 & 0 & 0;
A_I(x) & -I & 0 & 0
]
is nonsingular.
-/
theorem primalDualMatrix_nonsingular_of_LICQ_strictComplementarity_secondOrder
    {n mₑ mᵢ : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (cE : Fin mₑ → (Fin n → ℝ) → ℝ)
    (cI : Fin mᵢ → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ)
    (s : Fin mᵢ → ℝ)
    (y : Fin mₑ → ℝ)
    (z : Fin mᵢ → ℝ)
    (hNLP : IsNonlinearProgrammingProblem n mₑ mᵢ f cE cI)
    (hxeq : ∀ i, cE i x = 0)
    (hxs : ∀ i, cI i x - s i = 0)
    (hs_nonneg : ∀ i, 0 ≤ s i)
    (hz_nonneg : ∀ i, 0 ≤ z i)
    (hcomp : ∀ i, s i * z i = 0)
    (hSC : StrictComplementarity mᵢ s z)
    (hLICQ :
      LinearIndependent ℝ
        (fun k : (Fin mₑ) ⊕ {i : Fin mᵢ // s i = 0} =>
          match k with
          | Sum.inl i => fderiv ℝ (cE i) x
          | Sum.inr i => fderiv ℝ (cI i.1) x))
    (hC2 :
      ContDiffAt ℝ 2
        (fun x' =>
          f x'
            - ∑ ie : Fin mₑ, y ie * cE ie x'
            - ∑ ii : Fin mᵢ, z ii * cI ii x')
        x)
    (hpos :
      let H : Matrix (Fin n) (Fin n) ℝ :=
        fun i j =>
          fderiv ℝ
            (fun x' =>
              fderiv ℝ
                (fun x'' =>
                  f x''
                    - ∑ ie : Fin mₑ, y ie * cE ie x''
                    - ∑ ii : Fin mᵢ, z ii * cI ii x'')
                x' (Pi.single j (1 : ℝ)))
            x (Pi.single i (1 : ℝ))
      let A : Matrix ((Fin mₑ) ⊕ {i : Fin mᵢ // s i = 0}) (Fin n) ℝ :=
        fun i j =>
          match i with
          | Sum.inl ie => fderiv ℝ (cE ie) x (Pi.single j (1 : ℝ))
          | Sum.inr ii => fderiv ℝ (cI ii.1) x (Pi.single j (1 : ℝ))
      ∀ d : Fin n → ℝ,
        A.mulVec d = 0 →
        d ≠ 0 →
        0 < dotProduct d (H.mulVec d)) :
    let AE : Matrix (Fin mₑ) (Fin n) ℝ :=
      fun i j => fderiv ℝ (cE i) x (Pi.single j (1 : ℝ))
    let AI : Matrix (Fin mᵢ) (Fin n) ℝ :=
      fun i j => fderiv ℝ (cI i) x (Pi.single j (1 : ℝ))
    let H : Matrix (Fin n) (Fin n) ℝ :=
      fun i j =>
        fderiv ℝ
          (fun x' =>
            fderiv ℝ
              (fun x'' =>
                f x''
                  - ∑ ie : Fin mₑ, y ie * cE ie x''
                  - ∑ ii : Fin mᵢ, z ii * cI ii x'')
              x' (Pi.single j (1 : ℝ)))
          x (Pi.single i (1 : ℝ))
    let Z : Matrix (Fin mᵢ) (Fin mᵢ) ℝ := Matrix.diagonal z
    let S : Matrix (Fin mᵢ) (Fin mᵢ) ℝ := Matrix.diagonal s
    let e_left : (Fin n ⊕ Fin mᵢ) ≃ Fin (n + mᵢ) := @finSumFinEquiv n mᵢ
    let e_mid : ((Fin n ⊕ Fin mᵢ) ⊕ Fin mₑ) ≃ Fin ((n + mᵢ) + mₑ) :=
      (Equiv.sumCongr e_left (Equiv.refl _)).trans (@finSumFinEquiv (n + mᵢ) mₑ)
    let e : (((Fin n ⊕ Fin mᵢ) ⊕ Fin mₑ) ⊕ Fin mᵢ) ≃ Fin (((n + mᵢ) + mₑ) + mᵢ) :=
      (Equiv.sumCongr e_mid (Equiv.refl _)).trans (@finSumFinEquiv ((n + mᵢ) + mₑ) mᵢ)
    IsNonsingular
      (Matrix.reindex e e
        (fun i j =>
          match i, j with
          | Sum.inl (Sum.inl (Sum.inl i1)), Sum.inl (Sum.inl (Sum.inl j1)) => H i1 j1
          | Sum.inl (Sum.inl (Sum.inl i1)), Sum.inl (Sum.inl (Sum.inr _)) => 0
          | Sum.inl (Sum.inl (Sum.inl i1)), Sum.inl (Sum.inr j3) => -AE.transpose i1 j3
          | Sum.inl (Sum.inl (Sum.inl i1)), Sum.inr j4 => -AI.transpose i1 j4
          | Sum.inl (Sum.inl (Sum.inr i2)), Sum.inl (Sum.inl (Sum.inl _)) => 0
          | Sum.inl (Sum.inl (Sum.inr i2)), Sum.inl (Sum.inl (Sum.inr j2)) => Z i2 j2
          | Sum.inl (Sum.inl (Sum.inr _)), Sum.inl (Sum.inr _) => 0
          | Sum.inl (Sum.inl (Sum.inr i2)), Sum.inr j4 => S i2 j4
          | Sum.inl (Sum.inr i3), Sum.inl (Sum.inl (Sum.inl j1)) => AE i3 j1
          | Sum.inl (Sum.inr _), Sum.inl (Sum.inl (Sum.inr _)) => 0
          | Sum.inl (Sum.inr _), Sum.inl (Sum.inr _) => 0
          | Sum.inl (Sum.inr _), Sum.inr _ => 0
          | Sum.inr i4, Sum.inl (Sum.inl (Sum.inl j1)) => AI i4 j1
          | Sum.inr i4, Sum.inl (Sum.inl (Sum.inr j2)) =>
              (-(1 : Matrix (Fin mᵢ) (Fin mᵢ) ℝ)) i4 j2
          | Sum.inr _, Sum.inl (Sum.inr _) => 0
          | Sum.inr _, Sum.inr _ => 0)) := by
  sorry

end «problem-97»
