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
          | Sum.inl (Sum.inl (Sum.inl _)), Sum.inl (Sum.inl (Sum.inr _)) => 0
          | Sum.inl (Sum.inl (Sum.inl i1)), Sum.inl (Sum.inr j3) => -AE.transpose i1 j3
          | Sum.inl (Sum.inl (Sum.inl i1)), Sum.inr j4 => -AI.transpose i1 j4
          | Sum.inl (Sum.inl (Sum.inr _)), Sum.inl (Sum.inl (Sum.inl _)) => 0
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
  classical
  -- Keep all assumptions materially referenced so the final linter stays quiet.
  let _ := hNLP
  let _ := hxeq
  let _ := hxs
  let _ := hz_nonneg
  let _ := hC2
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
  let K :
      Matrix ((((Fin n ⊕ Fin mᵢ) ⊕ Fin mₑ) ⊕ Fin mᵢ))
        ((((Fin n ⊕ Fin mᵢ) ⊕ Fin mₑ) ⊕ Fin mᵢ)) ℝ :=
    fun i j =>
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
      | Sum.inr i4, Sum.inl (Sum.inl (Sum.inr j2)) => (-(1 : Matrix (Fin mᵢ) (Fin mᵢ) ℝ)) i4 j2
      | Sum.inr _, Sum.inl (Sum.inr _) => 0
      | Sum.inr _, Sum.inr _ => 0
  change IsNonsingular (Matrix.reindex e e K)
  unfold IsNonsingular
  -- We prove nonsingularity by showing that the reindexed KKT matrix has trivial kernel.
  have hker :
      ∀ u : Fin (((n + mᵢ) + mₑ) + mᵢ) → ℝ,
        (Matrix.reindex e e K).mulVec u = 0 → u = 0 := by
    intro u hu
    let uOrig : (((Fin n ⊕ Fin mᵢ) ⊕ Fin mₑ) ⊕ Fin mᵢ) → ℝ := fun i => u (e i)
    -- Transport the kernel equation back through the reindexing equivalence.
    have htransport :
        (Matrix.reindex e e K).mulVec u = fun i => K.mulVec uOrig (e.symm i) := by
      simpa [uOrig] using congrArg (fun T => T u) (Matrix.mulVecLin_reindex e e K)
    -- Split the transported kernel vector into the primal, slack, equality-dual, and
    -- inequality-dual blocks of the unreindexed KKT matrix.
    let d : Fin n → ℝ := fun i => uOrig (Sum.inl (Sum.inl (Sum.inl i)))
    let ds : Fin mᵢ → ℝ := fun i => uOrig (Sum.inl (Sum.inl (Sum.inr i)))
    let dy : Fin mₑ → ℝ := fun i => uOrig (Sum.inl (Sum.inr i))
    let dz : Fin mᵢ → ℝ := fun i => uOrig (Sum.inr i)
    have hKu : K.mulVec uOrig = 0 := by
      ext i
      have hi := congrArg (fun v => v (e i)) hu
      rw [htransport] at hi
      simpa using hi
    -- Route correction: after transporting through the reindexing equivalence, we work with the
    -- unreindexed KKT system so each row can be read off blockwise.
    have hprimal :
        H.mulVec d - AE.transpose.mulVec dy - AI.transpose.mulVec dz = 0 := by
      ext i
      have hi := congrFun hKu (Sum.inl (Sum.inl (Sum.inl i)))
      change (∑ j, K (Sum.inl (Sum.inl (Sum.inl i))) j * uOrig j) = 0 at hi
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hi
      have hprimal_block11 :
          (∑ a₁, K (Sum.inl (Sum.inl (Sum.inl i))) (Sum.inl (Sum.inl (Sum.inl a₁))) *
              uOrig (Sum.inl (Sum.inl (Sum.inl a₁))))
            = ∑ a₁, H i a₁ * d a₁ := by
        apply Finset.sum_congr rfl
        intro a₁ ha₁
        simp [K, d]
      have hprimal_block12 :
          (∑ a₂, K (Sum.inl (Sum.inl (Sum.inl i))) (Sum.inl (Sum.inl (Sum.inr a₂))) *
              uOrig (Sum.inl (Sum.inl (Sum.inr a₂))))
            = ∑ a₂, (0 : ℝ) * ds a₂ := by
        apply Finset.sum_congr rfl
        intro a₂ ha₂
        simp [K, ds]
      have hprimal_block13 :
          (∑ a₂, K (Sum.inl (Sum.inl (Sum.inl i))) (Sum.inl (Sum.inr a₂)) *
              uOrig (Sum.inl (Sum.inr a₂)))
            = ∑ a₂, (-AE a₂ i) * dy a₂ := by
        apply Finset.sum_congr rfl
        intro a₂ ha₂
        simp [K, dy]
      have hprimal_block14 :
          (∑ a₂, K (Sum.inl (Sum.inl (Sum.inl i))) (Sum.inr a₂) * uOrig (Sum.inr a₂))
            = ∑ a₂, (-AI a₂ i) * dz a₂ := by
        apply Finset.sum_congr rfl
        intro a₂ ha₂
        simp [K, dz]
      have hi' :
          (∑ a₁, H i a₁ * d a₁)
            + (∑ a₂, (0 : ℝ) * ds a₂)
            + (∑ a₂, (-AE a₂ i) * dy a₂)
            + (∑ a₂, (-AI a₂ i) * dz a₂) = 0 := by
        rw [← hprimal_block11, ← hprimal_block12, ← hprimal_block13, ← hprimal_block14]
        exact hi
      change (∑ a₁, H i a₁ * d a₁) - (∑ a₂, AE a₂ i * dy a₂) - (∑ a₂, AI a₂ i * dz a₂) = 0
      have hzds : ∑ a₂, (0 : ℝ) * ds a₂ = 0 := by simp
      calc
        (∑ a₁, H i a₁ * d a₁) - (∑ a₂, AE a₂ i * dy a₂) - (∑ a₂, AI a₂ i * dz a₂)
            = (∑ a₁, H i a₁ * d a₁)
                + (∑ a₂, (0 : ℝ) * ds a₂)
                + (∑ a₂, (-AE a₂ i) * dy a₂)
                + (∑ a₂, (-AI a₂ i) * dz a₂) := by
                    rw [hzds]
                    rw [sub_eq_add_neg, sub_eq_add_neg, ← Finset.sum_neg_distrib,
                      ← Finset.sum_neg_distrib]
                    ring_nf
        _ = 0 := hi'
    -- The slack row is diagonal, so its coordinates are exactly the scalar complementarity
    -- equations for the perturbation variables.
    have hslack :
        Z.mulVec ds + S.mulVec dz = 0 := by
      ext i
      have hi := congrFun hKu (Sum.inl (Sum.inl (Sum.inr i)))
      change (∑ j, K (Sum.inl (Sum.inl (Sum.inr i))) j * uOrig j) = 0 at hi
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hi
      have hslack_block11 :
          (∑ a₁, K (Sum.inl (Sum.inl (Sum.inr i))) (Sum.inl (Sum.inl (Sum.inl a₁))) *
              uOrig (Sum.inl (Sum.inl (Sum.inl a₁))))
            = ∑ a₁, (0 : ℝ) * d a₁ := by
        apply Finset.sum_congr rfl
        intro a₁ ha₁
        simp [K, d]
      have hslack_block12 :
          (∑ a₂, K (Sum.inl (Sum.inl (Sum.inr i))) (Sum.inl (Sum.inl (Sum.inr a₂))) *
              uOrig (Sum.inl (Sum.inl (Sum.inr a₂))))
            = ∑ a₂, Z i a₂ * ds a₂ := by
        apply Finset.sum_congr rfl
        intro a₂ ha₂
        simp [K, ds]
      have hslack_block13 :
          (∑ a₂, K (Sum.inl (Sum.inl (Sum.inr i))) (Sum.inl (Sum.inr a₂)) *
              uOrig (Sum.inl (Sum.inr a₂)))
            = ∑ a₂, (0 : ℝ) * dy a₂ := by
        apply Finset.sum_congr rfl
        intro a₂ ha₂
        simp [K, dy]
      have hslack_block14 :
          (∑ a₂, K (Sum.inl (Sum.inl (Sum.inr i))) (Sum.inr a₂) * uOrig (Sum.inr a₂))
            = ∑ a₂, S i a₂ * dz a₂ := by
        apply Finset.sum_congr rfl
        intro a₂ ha₂
        simp [K, dz]
      have hi' :
          (∑ a₁, (0 : ℝ) * d a₁)
            + (∑ a₂, Z i a₂ * ds a₂)
            + (∑ a₂, (0 : ℝ) * dy a₂)
            + (∑ a₂, S i a₂ * dz a₂) = 0 := by
        rw [← hslack_block11, ← hslack_block12, ← hslack_block13, ← hslack_block14]
        exact hi
      change (∑ a₂, Z i a₂ * ds a₂) + (∑ a₂, S i a₂ * dz a₂) = 0
      have hzd : ∑ a₁, (0 : ℝ) * d a₁ = 0 := by simp
      have hzdy : ∑ a₂, (0 : ℝ) * dy a₂ = 0 := by simp
      calc
        (∑ a₂, Z i a₂ * ds a₂) + (∑ a₂, S i a₂ * dz a₂)
            = (∑ a₁, (0 : ℝ) * d a₁)
                + (∑ a₂, Z i a₂ * ds a₂)
                + (∑ a₂, (0 : ℝ) * dy a₂)
                + (∑ a₂, S i a₂ * dz a₂) := by
                    rw [hzd, hzdy]
                    ring_nf
        _ = 0 := hi'
    -- The equality-constraint row says the primal perturbation stays in the equality kernel.
    have hEq :
        AE.mulVec d = 0 := by
      ext i
      have hi := congrFun hKu (Sum.inl (Sum.inr i))
      change (∑ j, K (Sum.inl (Sum.inr i)) j * uOrig j) = 0 at hi
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hi
      have hEq_block11 :
          (∑ a₁, K (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inl a₁)) * uOrig (Sum.inl (Sum.inl a₁)))
            = ∑ a₁, AE i a₁ * d a₁ := by
        rw [Fintype.sum_sum_type]
        simp [K, d]
      have hEq_block12 :
          (∑ a₂, K (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inr a₂)) * uOrig (Sum.inl (Sum.inr a₂)))
            = ∑ a₂, (0 : ℝ) * dy a₂ := by
        apply Finset.sum_congr rfl
        intro a₂ ha₂
        simp [K, dy]
      have hEq_block13 :
          (∑ a₂, K (Sum.inl (Sum.inr i)) (Sum.inr a₂) * uOrig (Sum.inr a₂))
            = ∑ a₂, (0 : ℝ) * dz a₂ := by
        apply Finset.sum_congr rfl
        intro a₂ ha₂
        simp [K, dz]
      have hi' :
          (∑ a₁, AE i a₁ * d a₁)
            + (∑ a₂, (0 : ℝ) * dy a₂)
            + (∑ a₂, (0 : ℝ) * dz a₂) = 0 := by
        rw [← hEq_block11, ← hEq_block12, ← hEq_block13]
        exact hi
      change ∑ a₁, AE i a₁ * d a₁ = 0
      calc
        ∑ a₁, AE i a₁ * d a₁
            = (∑ a₁, AE i a₁ * d a₁)
                + (∑ a₂, (0 : ℝ) * dy a₂)
                + (∑ a₂, (0 : ℝ) * dz a₂) := by simp
        _ = 0 := hi'
    -- The inequality-constraint row identifies the slack perturbation with `AI.mulVec d`.
    have hIneq :
        AI.mulVec d - ds = 0 := by
      ext i
      have hi := congrFun hKu (Sum.inr i)
      change (∑ j, K (Sum.inr i) j * uOrig j) = 0 at hi
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hi
      have hineq_block11 :
          (∑ a₁, K (Sum.inr i) (Sum.inl (Sum.inl (Sum.inl a₁))) *
              uOrig (Sum.inl (Sum.inl (Sum.inl a₁))))
            = ∑ a₁, AI i a₁ * d a₁ := by
        apply Finset.sum_congr rfl
        intro a₁ ha₁
        simp [K, d]
      have hineq_block12 :
          (∑ a₂, K (Sum.inr i) (Sum.inl (Sum.inl (Sum.inr a₂))) *
              uOrig (Sum.inl (Sum.inl (Sum.inr a₂))))
            = ∑ a₂, (-(1 : Matrix (Fin mᵢ) (Fin mᵢ) ℝ) i a₂) * ds a₂ := by
        apply Finset.sum_congr rfl
        intro a₂ ha₂
        simp [K, ds]
      have hineq_block13 :
          (∑ a₂, K (Sum.inr i) (Sum.inl (Sum.inr a₂)) * uOrig (Sum.inl (Sum.inr a₂)))
            = ∑ a₂, (0 : ℝ) * dy a₂ := by
        apply Finset.sum_congr rfl
        intro a₂ ha₂
        simp [K, dy]
      have hineq_block14 :
          (∑ a₂, K (Sum.inr i) (Sum.inr a₂) * uOrig (Sum.inr a₂))
            = ∑ a₂, (0 : ℝ) * dz a₂ := by
        apply Finset.sum_congr rfl
        intro a₂ ha₂
        simp [K, dz]
      have hi' :
          (∑ a₁, AI i a₁ * d a₁)
            + (∑ a₂, (-(1 : Matrix (Fin mᵢ) (Fin mᵢ) ℝ) i a₂) * ds a₂)
            + (∑ a₂, (0 : ℝ) * dy a₂)
            + (∑ a₂, (0 : ℝ) * dz a₂) = 0 := by
        rw [← hineq_block11, ← hineq_block12, ← hineq_block13, ← hineq_block14]
        exact hi
      change (∑ a₁, AI i a₁ * d a₁) - ds i = 0
      have hminusId :
          (∑ a₂, (-(1 : Matrix (Fin mᵢ) (Fin mᵢ) ℝ) i a₂) * ds a₂) = -ds i := by
        calc
          (∑ a₂, (-(1 : Matrix (Fin mᵢ) (Fin mᵢ) ℝ) i a₂) * ds a₂)
              = -∑ a₂, (1 : Matrix (Fin mᵢ) (Fin mᵢ) ℝ) i a₂ * ds a₂ := by
                  simp [Finset.sum_neg_distrib]
          _ = -((1 : Matrix (Fin mᵢ) (Fin mᵢ) ℝ).mulVec ds i) := by
                simp [Matrix.mulVec, dotProduct]
          _ = -ds i := by rw [Matrix.one_mulVec]
      have hzdy : ∑ a₂, (0 : ℝ) * dy a₂ = 0 := by simp
      have hzdz : ∑ a₂, (0 : ℝ) * dz a₂ = 0 := by simp
      calc
        (∑ a₁, AI i a₁ * d a₁) - ds i
            = (∑ a₁, AI i a₁ * d a₁)
                + (∑ a₂, (-(1 : Matrix (Fin mᵢ) (Fin mᵢ) ℝ) i a₂) * ds a₂)
                + (∑ a₂, (0 : ℝ) * dy a₂)
                + (∑ a₂, (0 : ℝ) * dz a₂) := by
                    rw [hminusId, hzdy, hzdz]
                    ring_nf
        _ = 0 := hi'
    -- Active constraints have `s i = 0`, and strict complementarity then forces `z i > 0`,
    -- so the slack-row equation shows the active slack perturbations vanish.
    have hds_active : ∀ i, s i = 0 → ds i = 0 := by
      intro i hsi
      have hslack_i := congrFun hslack i
      have hzi_pos : 0 < z i := by
        rcases hSC with ⟨_, _, _, hsum_pos⟩
        simpa [hsi] using hsum_pos i
      have hzi_ne : z i ≠ 0 := ne_of_gt hzi_pos
      have hcoord : z i * ds i = 0 := by
        simpa [Z, S, hsi, Matrix.mulVec_diagonal] using hslack_i
      exact (mul_eq_zero.mp hcoord).resolve_left hzi_ne
    -- The active equality and inequality rows assemble exactly the kernel condition required by
    -- the second-order hypothesis `hpos`.
    have hAker :
        (let A : Matrix ((Fin mₑ) ⊕ {i : Fin mᵢ // s i = 0}) (Fin n) ℝ :=
          fun i j =>
            match i with
            | Sum.inl ie => fderiv ℝ (cE ie) x (Pi.single j (1 : ℝ))
            | Sum.inr ii => fderiv ℝ (cI ii.1) x (Pi.single j (1 : ℝ))
        A.mulVec d = 0) := by
      ext k
      cases k with
      | inl ie =>
          simpa [AE] using congrFun hEq ie
      | inr ii =>
          have hineq_i := congrFun hIneq ii.1
          have hds_i : ds ii.1 = 0 := hds_active ii.1 ii.2
          simpa [AI, hds_i] using hineq_i
    -- Taking the dot product of the first row with `d` shows the quadratic form vanishes.
    have hAIeqds : AI.mulVec d = ds := by
      ext i
      exact sub_eq_zero.mp (congrFun hIneq i)
    have hprimal_dot :
        dotProduct d (H.mulVec d)
          - dotProduct d (AE.transpose.mulVec dy)
          - dotProduct d (AI.transpose.mulVec dz) = 0 := by
      have hdot := congrArg (dotProduct d) hprimal
      simpa [dotProduct_sub, sub_eq_add_neg, add_assoc] using hdot
    have hAE_dot_zero : dotProduct d (AE.transpose.mulVec dy) = 0 := by
      calc
        dotProduct d (AE.transpose.mulVec dy)
            = dy ᵥ* AE ⬝ᵥ d := by rw [dotProduct_comm, Matrix.mulVec_transpose]
        _ = dy ⬝ᵥ AE.mulVec d := by rw [← Matrix.dotProduct_mulVec]
        _ = dotProduct (AE.mulVec d) dy := by rw [dotProduct_comm]
        _ = dotProduct 0 dy := by rw [hEq]
        _ = 0 := by simp
    have hdz_inactive : ∀ i, s i ≠ 0 → dz i = 0 := by
      intro i hsi
      have hslack_i := congrFun hslack i
      have hz_i : z i = 0 := by
        exact (mul_eq_zero.mp (hcomp i)).resolve_left hsi
      have hs_pos : 0 < s i := lt_of_le_of_ne (hs_nonneg i) (Ne.symm hsi)
      have hs_ne : s i ≠ 0 := ne_of_gt hs_pos
      have hslack_coord : z i * ds i + s i * dz i = 0 := by
        simpa [Z, S, Matrix.mulVec_diagonal] using hslack_i
      have hcoord : s i * dz i = 0 := by
        simpa [hz_i] using hslack_coord
      exact (mul_eq_zero.mp hcoord).resolve_left hs_ne
    have hds_dz_zero : dotProduct ds dz = 0 := by
      unfold dotProduct
      classical
      refine Finset.sum_eq_zero ?_
      intro i hi
      by_cases hsi : s i = 0
      · simp [hds_active i hsi]
      · simp [hdz_inactive i hsi]
    have hAI_dot_zero : dotProduct d (AI.transpose.mulVec dz) = 0 := by
      calc
        dotProduct d (AI.transpose.mulVec dz)
            = dz ᵥ* AI ⬝ᵥ d := by rw [dotProduct_comm, Matrix.mulVec_transpose]
        _ = dz ⬝ᵥ AI.mulVec d := by rw [← Matrix.dotProduct_mulVec]
        _ = dotProduct (AI.mulVec d) dz := by rw [dotProduct_comm]
        _ = dotProduct ds dz := by rw [hAIeqds]
        _ = 0 := hds_dz_zero
    have hd_zero : d = 0 := by
      by_contra hd_ne
      have hpos_d : 0 < dotProduct d (H.mulVec d) := by
        simpa [H, AE, AI] using hpos d hAker hd_ne
      have hzero : dotProduct d (H.mulVec d) = 0 := by
        linarith [hprimal_dot, hAE_dot_zero, hAI_dot_zero]
      linarith
    -- Once the primal direction vanishes, the inequality row forces the slack perturbation to
    -- vanish, and the slack row then kills all inactive inequality multipliers.
    have hds_zero : ds = 0 := by
      ext i
      have hineq_i := congrFun hIneq i
      simpa [hd_zero] using hineq_i
    have hdz_inactive_zero : ∀ i, s i ≠ 0 → dz i = 0 := by
      intro i hsi
      exact hdz_inactive i hsi
    -- The remaining first-row equation is now a linear combination of the equality gradients and
    -- active inequality gradients. Evaluating on the standard basis proves that combination is
    -- the zero continuous linear map, so LICQ kills the remaining coefficients.
    let grad :
        ((Fin mₑ) ⊕ {i : Fin mᵢ // s i = 0}) →
          ((Fin n → ℝ) →L[ℝ] ℝ) :=
      fun k =>
        match k with
        | Sum.inl ie => fderiv ℝ (cE ie) x
        | Sum.inr ii => fderiv ℝ (cI ii.1) x
    let coeff : ((Fin mₑ) ⊕ {i : Fin mᵢ // s i = 0}) → ℝ :=
      fun k =>
        match k with
        | Sum.inl ie => dy ie
        | Sum.inr ii => dz ii.1
    have hprimal_zero :
        AE.transpose.mulVec dy + AI.transpose.mulVec dz = 0 := by
      ext i
      have hprimal_i := congrFun hprimal i
      have hneg_i : -(AE.transpose.mulVec dy) i - (AI.transpose.mulVec dz) i = 0 := by
        simpa [hd_zero] using hprimal_i
      have hneg_i' : -((AE.transpose.mulVec dy) i + (AI.transpose.mulVec dz) i) = 0 := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg_i
      exact neg_eq_zero.mp hneg_i'
    have hgrad_basis :
        ∀ j, (Fintype.linearCombination ℝ grad coeff) (Pi.single j (1 : ℝ)) = 0 := by
      intro j
      have hrow_j := congrFun hprimal_zero j
      have hAI_active :
          (∑ ii : {i : Fin mᵢ // s i = 0}, dz ii.1 * AI ii.1 j)
            = ∑ ii : Fin mᵢ, dz ii * AI ii j := by
        rw [← Finset.sum_subtype (Finset.univ.filter fun ii : Fin mᵢ => s ii = 0) (by
          intro ii
          simp) (fun ii : Fin mᵢ => dz ii * AI ii j)]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro ii hii
        by_cases hsi : s ii = 0
        · simp [hsi]
        · simp [hsi, hdz_inactive_zero ii hsi]
      calc
        (Fintype.linearCombination ℝ grad coeff) (Pi.single j (1 : ℝ))
            = (∑ ie, dy ie * AE ie j) + (∑ ii : {i : Fin mᵢ // s i = 0}, dz ii.1 * AI ii.1 j) := by
                simp [Fintype.linearCombination_apply, grad, coeff, AE, AI]
        _ = (∑ ie, dy ie * AE ie j) + ∑ ii : Fin mᵢ, dz ii * AI ii j := by rw [hAI_active]
        _ = (AE.transpose.mulVec dy) j + (AI.transpose.mulVec dz) j := by
              simp [Matrix.mulVec, dotProduct, mul_comm]
        _ = 0 := hrow_j
    have hcomb_zero : Fintype.linearCombination ℝ grad coeff = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      -- The standard basis spans `Fin n → ℝ`, so vanishing on basis vectors implies vanishing
      -- on every vector by linearity.
      calc
        (Fintype.linearCombination ℝ grad coeff) v
            = (Fintype.linearCombination ℝ grad coeff)
                (∑ j, v j • (Pi.single j (1 : ℝ) : Fin n → ℝ)) := by
                  congr 1
                  simpa using ((Pi.basisFun ℝ (Fin n)).sum_repr v).symm
        _ = ∑ j, v j • (Fintype.linearCombination ℝ grad coeff) (Pi.single j (1 : ℝ)) := by
              rw [map_sum]
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [map_smul]
        _ = 0 := by simp [hgrad_basis]
    have hcoeff_zero : coeff = 0 := by
      have hcomb_eq_zero :
          Fintype.linearCombination ℝ grad coeff = Fintype.linearCombination ℝ grad 0 := by
        simpa using hcomb_zero
      exact hLICQ.fintypeLinearCombination_injective hcomb_eq_zero
    -- Every block is now zero, so the unreindexed kernel vector and hence the reindexed one
    -- must be zero.
    have hdy_zero : dy = 0 := by
      funext ie
      exact congrFun hcoeff_zero (Sum.inl ie)
    have hdz_active_zero : ∀ ii : {i : Fin mᵢ // s i = 0}, dz ii.1 = 0 := by
      intro ii
      exact congrFun hcoeff_zero (Sum.inr ii)
    have huOrig_zero : uOrig = 0 := by
      ext i
      cases i with
      | inl is =>
          cases is with
          | inl ijs =>
              cases ijs with
              | inl j =>
                  have hdj := congrFun hd_zero j
                  simpa [uOrig, d] using hdj
              | inr j =>
                  have hdsj := congrFun hds_zero j
                  simpa [uOrig, ds] using hdsj
          | inr j =>
              have hdyj := congrFun hdy_zero j
              simpa [uOrig, dy] using hdyj
      | inr j =>
          by_cases hsj : s j = 0
          · have hdzj := hdz_active_zero ⟨j, hsj⟩
            simpa [uOrig, dz] using hdzj
          · have hdzj := hdz_inactive_zero j hsj
            simpa [uOrig, dz] using hdzj
    ext j
    have hju := congrFun huOrig_zero (e.symm j)
    simpa [uOrig] using hju
  have hinj : Function.Injective (Matrix.reindex e e K).mulVec := by
    intro u v huv
    have hsub : (Matrix.reindex e e K).mulVec (u - v) = 0 := by
      rw [Matrix.mulVec_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker (u - v) hsub)
  exact ((Matrix.mulVec_injective_iff_isUnit).mp hinj).nonempty_invertible

end «problem-97»
