import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-16»
/-
A matrix A ∈ ℝ^m × n has full row rank if rank(A) = m; equivalently, its rows are linearly
independent.
-/
def HasFullRowRank {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : Prop :=
  Matrix.rank A = Fintype.card m

/-
Let G ∈ ℝ^n×n, A ∈ ℝ^m × n, c ∈ ℝ^n, and b ∈ ℝ^m. Consider the equality - constrained quadratic
program min_x ∈ ℝ^n ((1)/(2) xᵀ G x + xᵀ c) subject to Ax = b.
-/
structure EqualityConstrainedQuadraticProgram
    (m n : Type*) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] where
  G : Matrix n n ℝ
  G_symm : G.IsSymm
  A : Matrix m n ℝ
  c : n → ℝ
  b : m → ℝ

def EqualityConstrainedQuadraticProgram.isFeasible
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : EqualityConstrainedQuadraticProgram m n) (x : n → ℝ) : Prop :=
  P.A.mulVec x = P.b

def EqualityConstrainedQuadraticProgram.objective
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : EqualityConstrainedQuadraticProgram m n) (x : n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (P.G.mulVec x) + dotProduct x P.c

/-
Let G ∈ ℝ^{n×n}, A ∈ ℝ^{m × n}, c ∈ ℝ^n, and b ∈ ℝ^m. Consider the equality - constrained quadratic
program min_{x ∈ ℝ^n} ((1)/(2) xᵀ G x + xᵀ c) subject to Ax = b. Assume that A has full row rank,
and let Z ∈ ℝ^{n × (n - m)} have columns forming a basis of the null space of A, so AZ = 0. Suppose
there exists u ∈ ℝ^{n - m} such that uᵀ Zᵀ G Zu < 0. Assume also that there exists (x*, λ^*) ∈ ℝ^n ×
ℝ^m such that [ G & - Aᵀ; A & 0 ] [ x*; λ^* ] = [ - c; b ]. Show that x* is a stationary point of
this
problem but not a local minimizer.
-/
theorem stationary_but_not_local_minimizer_of_negative_reduced_hessian
    {m n k : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (P : EqualityConstrainedQuadraticProgram m n)
    (hGsymm : P.G.IsSymm)
    (hfull : HasFullRowRank P.A)
    (Z : Matrix n k ℝ)
    (hAZ : P.A * Z = 0)
    (hZspan : ∀ d : n → ℝ, P.A.mulVec d = 0 → ∃ v : k → ℝ, Z.mulVec v = d)
    (u : k → ℝ)
    (hZu_ne_zero : Z.mulVec u ≠ 0)
    (hneg : dotProduct u ((Z.transpose * P.G * Z).mulVec u) < 0)
    (xstar : n → ℝ)
    (lambdastar : m → ℝ)
    (hkkt₁ : P.G.mulVec xstar - P.A.transpose.mulVec lambdastar = fun i => -P.c i)
    (hkkt₂ : P.A.mulVec xstar = P.b) :
    P.isFeasible xstar ∧
      (∀ d : n → ℝ, P.A.mulVec d = 0 →
        dotProduct d (P.G.mulVec xstar) + dotProduct d P.c = 0) ∧
      ¬IsLocalMinOn P.objective {x | P.isFeasible x} xstar := by
  let d : n → ℝ := Z.mulVec u
  have hd_null : P.A.mulVec d = 0 := by
    -- The reduced-space direction `Z * u` is feasible because `AZ = 0`.
    dsimp [d]
    simpa [Matrix.mulVec_mulVec] using congrArg (fun M => M.mulVec u) hAZ
  have hd_stationary :
      dotProduct d (P.G.mulVec xstar) + dotProduct d P.c = 0 := by
    -- Dot the KKT stationarity equation with any feasible direction and kill the multiplier term.
    have hdot :
        dotProduct d (P.G.mulVec xstar - P.A.transpose.mulVec lambdastar) =
          dotProduct d (fun i => -P.c i) := by
      simpa using congrArg (fun v => dotProduct d v) hkkt₁
    have hmultiplier : dotProduct d (P.A.transpose.mulVec lambdastar) = 0 := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hd_null]
      simp
    have hc : dotProduct d (fun i => -P.c i) = -dotProduct d P.c := by
      change dotProduct d (-P.c) = -dotProduct d P.c
      rw [dotProduct_neg]
    rw [dotProduct_sub, hmultiplier, sub_zero, hc] at hdot
    linarith
  have hd_neg : dotProduct d (P.G.mulVec d) < 0 := by
    -- Rewrite the reduced Hessian form back in the ambient coordinates along `d = Z * u`.
    have hneg₁ : dotProduct u ((Z.transpose * P.G).mulVec (Z.mulVec u)) < 0 := by
      simpa [Matrix.mulVec_mulVec, mul_assoc] using hneg
    have hneg₂ : Matrix.vecMul u (Z.transpose * P.G) ⬝ᵥ Z.mulVec u < 0 := by
      simpa [Matrix.dotProduct_mulVec] using hneg₁
    have hneg₃ : Matrix.vecMul (Z.mulVec u) P.G ⬝ᵥ Z.mulVec u < 0 := by
      have hneg₃' : (Matrix.vecMul u Z.transpose) ᵥ* P.G ⬝ᵥ Z.mulVec u < 0 := by
        simpa [Matrix.vecMul_vecMul] using hneg₂
      simpa [Matrix.vecMul_transpose] using hneg₃'
    dsimp [d]
    simpa [Matrix.dotProduct_mulVec] using hneg₃
  refine ⟨hkkt₂, ?_, ?_⟩
  · intro d' hd'
    -- The same KKT dot-product argument works for every feasible direction.
    have hdot :
        dotProduct d' (P.G.mulVec xstar - P.A.transpose.mulVec lambdastar) =
          dotProduct d' (fun i => -P.c i) := by
      simpa using congrArg (fun v => dotProduct d' v) hkkt₁
    have hmultiplier : dotProduct d' (P.A.transpose.mulVec lambdastar) = 0 := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hd']
      simp
    have hc : dotProduct d' (fun i => -P.c i) = -dotProduct d' P.c := by
      change dotProduct d' (-P.c) = -dotProduct d' P.c
      rw [dotProduct_neg]
    rw [dotProduct_sub, hmultiplier, sub_zero, hc] at hdot
    linarith
  · intro hlocal
    -- Unpack the local-minimum filter condition into an explicit feasible ball.
    rw [IsLocalMinOn, IsMinFilter] at hlocal
    rcases Metric.mem_nhdsWithin_iff.mp hlocal with ⟨ε, hε_pos, hε⟩
    have hd_ne_zero : d ≠ 0 := by
      simpa [d] using hZu_ne_zero
    have hd_norm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne_zero
    let t : ℝ := ε / (2 * ‖d‖)
    let xt : n → ℝ := xstar + t • d
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    have hxt_feasible : P.isFeasible xt := by
      -- The affine constraint is preserved along null directions of `A`.
      unfold EqualityConstrainedQuadraticProgram.isFeasible
      dsimp [xt, t]
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hkkt₂, hd_null]
      simp
    have hxt_dist : dist xt xstar < ε := by
      -- Choosing `t = ε / (2 ‖d‖)` keeps the perturbation strictly inside the local ball.
      calc
        dist xt xstar = ‖xt - xstar‖ := dist_eq_norm _ _
        _ = ‖t • d‖ := by
          dsimp [xt]
          abel_nf
        _ = |t| * ‖d‖ := norm_smul _ _
        _ = t * ‖d‖ := by rw [abs_of_pos ht_pos]
        _ = (ε / (2 * ‖d‖)) * ‖d‖ := by rfl
        _ = ε / 2 := by
          field_simp [hd_norm_pos.ne']
        _ < ε := by linarith
    have hlocal_bound : P.objective xstar ≤ P.objective xt := by
      apply hε
      exact ⟨hxt_dist, hxt_feasible⟩
    have hcross :
        dotProduct xstar (P.G.mulVec d) = dotProduct d (P.G.mulVec xstar) := by
      -- Symmetry turns the mixed quadratic term into the first-variation term.
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose P.G xstar, hGsymm.eq, dotProduct_comm]
    have hobjective_expansion :
        P.objective xt =
          P.objective xstar +
            t * (dotProduct d (P.G.mulVec xstar) + dotProduct d P.c) +
            (t ^ 2 / 2) * dotProduct d (P.G.mulVec d) := by
      -- Expand the quadratic objective along the affine ray `xstar + t d`.
      dsimp [xt, t]
      unfold EqualityConstrainedQuadraticProgram.objective
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      simp_rw [add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [hcross]
      ring_nf
    have ht_sq_half_pos : 0 < t ^ 2 / 2 := by
      nlinarith [ht_pos]
    have hdescent_term : (t ^ 2 / 2) * dotProduct d (P.G.mulVec d) < 0 := by
      nlinarith [ht_sq_half_pos, hd_neg]
    have hobjective_lt : P.objective xt < P.objective xstar := by
      rw [hobjective_expansion, hd_stationary]
      simp only [mul_zero, add_zero]
      linarith
    linarith

end «problem-16»
