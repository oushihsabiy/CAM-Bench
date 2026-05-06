import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-187»

/- [BLOCK Exercise 3.15-(c) | 22 | defn]
A set C ⊆ ℝ^{n+1} is pointed if C cap (-C) = {0}.
-/
def Pointed (C : Set (Fin (Nat.succ n) → ℝ)) : Prop :=
  C ∩ Neg.neg '' C = ({0} : Set (Fin (Nat.succ n) → ℝ))

/- [BLOCK Exercise 3.15-(c) | 23 | opt_prob]
Consider the convex optimization problem
aligned
minimize quad & cᵀ x ;
subject\ to quad & fᵢ(x) ≤ 0, quad i=1,ldots,m, ;
& Ax=b,
aligned
where x ∈ ℝ^n, c ∈ ℝ^n, A ∈ ℝ^{p × n}, b ∈ ℝ^p, and each fᵢ : ℝ^n → ℝ is convex with dom fᵢ = ℝ^n
for i=1,ldots,m.
-/
structure ConvexOptimizationProblem where
  n : ℕ
  m : ℕ
  p : ℕ
  c : Fin n → ℝ
  A : Matrix (Fin p) (Fin n) ℝ
  b : Fin p → ℝ
  f : Fin m → (Fin n → ℝ) → ℝ

def ConvexOptimizationProblem.isFeasible
    (P : ConvexOptimizationProblem) (x : Fin P.n → ℝ) : Prop :=
  (∀ i : Fin P.m, P.f i x ≤ 0) ∧ P.A.mulVec x = P.b

def ConvexOptimizationProblem.objective
    (P : ConvexOptimizationProblem) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.c j * x j

/- [BLOCK Exercise 3.15-(c) | 24 | thm]
Consider the convex optimization problem
aligned
minimize quad & cᵀ x ;
subject\ to quad & fᵢ(x) ≤ 0, quad i=1,ldots,m, ;
& Ax=b,
aligned
where x ∈ ℝ^n, c ∈ ℝ^n, A ∈ ℝ^{p × n}, b ∈ ℝ^p, and each fᵢ : ℝ^n → ℝ is convex with dom fᵢ = ℝ^n
for i=1,ldots,m.
Define
K = cl≤ft{(x,t) ∈ ℝ^{n+1} | t>0, t fᵢ(x/t) ≤ 0 for i=1,ldots,m },
where cl denotes closure ∈ ℝ^{n+1}.
Assume that the set
{x ∈ ℝ^n | fᵢ(x) ≤ 0, quad i=1,ldots,m}
is bounded.
A set C ⊆ ℝ^{n+1} is pointed if
C cap (-C) = {0}.
Show that K is pointed.
-/
theorem K_pointed_of_bounded_feasible_set
    (P : ConvexOptimizationProblem)
    (hconvex_f : ∀ i : Fin P.m, ConvexOn ℝ (Set.univ : Set (Fin P.n → ℝ)) (P.f i))
    (hfeasible : {x : Fin P.n → ℝ | P.isFeasible x}.Nonempty)
    (hbounded :
      Bornology.IsBounded
        {x : Fin P.n → ℝ | P.isFeasible x}) :
    Pointed
      (closure
        {xt : Fin (Nat.succ P.n) → ℝ |
          0 < xt 0 ∧
          (∀ i : Fin P.m,
            xt 0 * P.f i
              (fun j : Fin P.n => xt (Fin.succ j) / xt 0) ≤ 0) ∧
          P.A.mulVec (fun j : Fin P.n => xt (Fin.succ j) / xt 0) = P.b}) := by
  let S : Set (Fin (Nat.succ P.n) → ℝ) :=
    {xt : Fin (Nat.succ P.n) → ℝ |
      0 < xt 0 ∧
      (∀ i : Fin P.m,
        xt 0 * P.f i
          (fun j : Fin P.n => xt (Fin.succ j) / xt 0) ≤ 0) ∧
      P.A.mulVec (fun j : Fin P.n => xt (Fin.succ j) / xt 0) = P.b}
  change Pointed (closure S)
  rcases hbounded.subset_closedBall (0 : Fin P.n → ℝ) with ⟨R, hRsub⟩
  let T : Set (Fin (Nat.succ P.n) → ℝ) :=
    {xt : Fin (Nat.succ P.n) → ℝ | 0 ≤ xt 0} ∩
      ⋂ j : Fin P.n, {xt : Fin (Nat.succ P.n) → ℝ | ‖xt (Fin.succ j)‖ ≤ R * xt 0}
  have hraw_tube : S ⊆ T := by
    intro xt hxt
    rcases hxt with ⟨hxt0_pos, hineq, hEq⟩
    let x : Fin P.n → ℝ := fun j => xt (Fin.succ j) / xt 0
    have hxfeasible : P.isFeasible x := by
      constructor
      · -- Positive homogenization lets us divide the inequality by the head coordinate.
        intro i
        by_contra hfi
        have hfi_pos : 0 < P.f i x := lt_of_not_ge hfi
        have hmul_pos : 0 < xt 0 * P.f i x := mul_pos hxt0_pos hfi_pos
        linarith [hineq i]
      · -- The affine constraint is already recorded in the raw homogenized point.
        exact hEq
    have hx_ball : x ∈ Metric.closedBall (0 : Fin P.n → ℝ) R := hRsub hxfeasible
    have hx_norm : ‖x‖ ≤ R := by
      -- The feasible slice sits in a closed ball centered at the origin.
      simpa [Metric.closedBall, dist_zero_right] using hx_ball
    constructor
    · -- Every raw homogenized point has nonnegative head coordinate.
      exact hxt0_pos.le
    · refine Set.mem_iInter.2 ?_
      intro j
      have hxcoord : ‖x j‖ ≤ R := (norm_le_pi_norm x j).trans hx_norm
      have hdiv : ‖xt (Fin.succ j)‖ / xt 0 ≤ R := by
        -- The bounded feasible slice controls each normalized tail coordinate.
        simpa [x, norm_div, Real.norm_eq_abs, abs_of_pos hxt0_pos] using hxcoord
      -- Multiplying back by the positive head coordinate recovers the tail bound.
      exact (div_le_iff₀ hxt0_pos).mp hdiv
  have hTclosed : IsClosed T := by
    have hhead_closed : IsClosed {xt : Fin (Nat.succ P.n) → ℝ | 0 ≤ xt 0} := by
      -- The head-coordinate nonnegativity condition is closed.
      simpa using isClosed_le continuous_const (continuous_apply 0)
    have htail_closed :
        ∀ j : Fin P.n,
          IsClosed {xt : Fin (Nat.succ P.n) → ℝ | ‖xt (Fin.succ j)‖ ≤ R * xt 0} := by
      intro j
      -- Each coordinate inequality is closed because both sides are continuous.
      refine isClosed_le ?_ ?_
      · exact (continuous_apply (Fin.succ j)).norm
      · exact continuous_const.mul (continuous_apply 0)
    -- The bounded tube is the intersection of the closed head and tail conditions.
    simpa [T] using hhead_closed.inter (isClosed_iInter htail_closed)
  have hclosure_tube : closure S ⊆ T := closure_minimal hraw_tube hTclosed
  have hzero_mem : (0 : Fin (Nat.succ P.n) → ℝ) ∈ closure S := by
    rcases hfeasible with ⟨xbar, hxbar_mem⟩
    have hxbar : P.isFeasible xbar := by
      simpa using hxbar_mem
    let v : Fin (Nat.succ P.n) → ℝ := Fin.cons (1 : ℝ) xbar
    rw [Metric.mem_closure_iff]
    intro ε hε
    let t : ℝ := ε / (‖v‖ + 1)
    have hden_pos : 0 < ‖v‖ + 1 := by
      positivity
    have htpos : 0 < t := by
      dsimp [t]
      positivity
    have hnormalized :
        (fun j : Fin P.n => (t • v) (Fin.succ j) / (t • v) 0) = xbar := by
      ext j
      -- The positive scale cancels when we renormalize the tail coordinates.
      simp [t, v, htpos.ne']
    have htv_mem : t • v ∈ S := by
      change
        0 < (t • v) 0 ∧
          (∀ i : Fin P.m,
            (t • v) 0 *
                P.f i (fun j : Fin P.n => (t • v) (Fin.succ j) / (t • v) 0) ≤ 0) ∧
          P.A.mulVec (fun j : Fin P.n => (t • v) (Fin.succ j) / (t • v) 0) = P.b
      constructor
      · -- The ray parameter gives the positive head coordinate.
        simpa [v, t] using htpos
      constructor
      · intro i
        have hscaled : t * P.f i xbar ≤ 0 := by
          -- Feasibility of `xbar` is preserved after multiplying by the positive scale.
          simpa using mul_le_mul_of_nonneg_left (hxbar.1 i) htpos.le
        rw [hnormalized]
        simpa [v] using hscaled
      · -- Normalization also preserves the affine equality constraint along the ray.
        rw [hnormalized]
        simpa [v] using hxbar.2
    have ht_mul : t * (‖v‖ + 1) = ε := by
      dsimp [t]
      field_simp [hden_pos.ne']
    have hdist_lt : dist (0 : Fin (Nat.succ P.n) → ℝ) (t • v) < ε := by
      -- Choosing `t = ε / (‖v‖ + 1)` makes the scaled ray point ε-close to the origin.
      have hv_lt : ‖v‖ < ‖v‖ + 1 := by
        linarith [norm_nonneg v]
      have hmul_lt : t * ‖v‖ < t * (‖v‖ + 1) := mul_lt_mul_of_pos_left hv_lt htpos
      calc
        dist (0 : Fin (Nat.succ P.n) → ℝ) (t • v) = ‖t • v‖ := dist_zero_left _
        _ = ‖t‖ * ‖v‖ := norm_smul t v
        _ = t * ‖v‖ := by simp [abs_of_nonneg htpos.le]
        _ < t * (‖v‖ + 1) := hmul_lt
        _ = ε := ht_mul
    exact ⟨t • v, htv_mem, hdist_lt⟩
  -- The pointedness claim is exactly the statement that the closure intersects its negative only at `0`.
  unfold Pointed
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hy_closure, hy_neg⟩
    rcases hy_neg with ⟨z, hz_closure, rfl⟩
    have hzT : z ∈ T := hclosure_tube hz_closure
    have hnegzT : -z ∈ T := hclosure_tube hy_closure
    have hz0_nonneg : 0 ≤ z 0 := hzT.1
    have hz0_nonpos : z 0 ≤ 0 := by
      -- Membership of `-z` in the tube forces the head coordinate to be nonpositive.
      simpa using hnegzT.1
    have hz0 : z 0 = 0 := le_antisymm hz0_nonpos hz0_nonneg
    have htail_zero : ∀ j : Fin P.n, z (Fin.succ j) = 0 := by
      intro j
      have hzbound : ‖z (Fin.succ j)‖ ≤ R * z 0 := Set.mem_iInter.1 hzT.2 j
      have hnorm_le_zero : ‖z (Fin.succ j)‖ ≤ 0 := by
        simpa [hz0] using hzbound
      have hnorm_eq_zero : ‖z (Fin.succ j)‖ = 0 :=
        le_antisymm hnorm_le_zero (norm_nonneg _)
      -- Once the head vanishes, the tail bounds collapse to zero coordinatewise.
      exact norm_eq_zero.mp hnorm_eq_zero
    have hz_eq_zero : z = 0 := by
      ext i
      -- Finite-coordinate extensionality separates the head from the tail coordinates.
      refine Fin.cases ?_ ?_ i
      · simpa using hz0
      · intro j
        exact htail_zero j
    simpa [hz_eq_zero]
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    constructor
    · exact hzero_mem
    · -- Negation fixes the origin, so the same closure point gives the image membership.
      simpa using Set.mem_image_of_mem Neg.neg hzero_mem

end «problem-187»
