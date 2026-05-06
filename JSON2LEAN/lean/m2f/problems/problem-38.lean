import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-38»
/- [BLOCK Exercise 3.15-(b) | 19 | defn]
A set S ⊆ ℝ^n has nonempty interior if there exist x ∈ S and varepsilon > 0 such that {y ∈ ℝ^n :
‖y-x‖ < varepsilon} ⊆ S.
-/
def HasNonemptyInterior {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ x ∈ S, ∃ ε > 0, Metric.ball x ε ⊆ S

/- [BLOCK Exercise 3.15-(b) | 20 | opt_prob]
Consider the convex optimization problem
aligned
minimize quad & cᵀ x ;
subject to quad & fᵢ(x) ≤ 0, quad i=1,ldots,m, ;
& Ax=b.
aligned
-/
structure ConvexOptimizationProblem where
  n : ℕ
  m : ℕ
  c : EuclideanSpace ℝ (Fin n)
  f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ
  A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)
  b : EuclideanSpace ℝ (Fin m)

open scoped RealInnerProductSpace

def ConvexOptimizationProblem.isFeasible (P : ConvexOptimizationProblem)
    (x : EuclideanSpace ℝ (Fin P.n)) : Prop :=
  (∀ i : Fin P.m, P.f i x ≤ 0) ∧ P.A x = P.b

def ConvexOptimizationProblem.objectiveValue (P : ConvexOptimizationProblem)
    (x : EuclideanSpace ℝ (Fin P.n)) : ℝ :=
  ⟪P.c, x⟫

/- [BLOCK Exercise 3.15-(b) | 21 | thm]
Consider the convex optimization problem where x ∈ ℝ^n, c ∈ ℝ^n, A ∈ ℝ^{p × n}, b ∈ ℝ^p, and each fᵢ
: ℝ^n → ℝ is convex with dom fᵢ = ℝ^n for i=1,ldots,m. Introduce t ∈ ℝ and define K = cl≤ft{(x,t) ∈
ℝ^{n+1} | t fᵢ(x/t) ≤ 0, quad i=1,ldots,m, quad t>0 }, where cl(·) denotes closure ∈ ℝ^{n+1}. Assume
there exists x ∈ ℝ^n such that fᵢ(x) < 0, quad i=1,ldots,m. Show that K has nonempty interior ∈
ℝ^{n+1}.
-/
theorem cone_closure_has_nonempty_interior
    (P : ConvexOptimizationProblem)
    (hconvex : ∀ i : Fin P.m, ConvexOn ℝ Set.univ (P.f i))
    (x_tilde : EuclideanSpace ℝ (Fin P.n))
    (hSlater : ∀ i : Fin P.m, P.f i x_tilde < 0) :
    HasNonemptyInterior
      (closure
        {z : EuclideanSpace ℝ (Fin (P.n + 1)) |
          0 < z 0 ∧
          (∀ i : Fin P.m,
            z 0 * P.f i
                (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin P.n)).symm
                  (fun j : Fin P.n => z j.succ / z 0) : EuclideanSpace ℝ (Fin P.n))) ≤ 0)}) := by
  let targetSet :
      Set (EuclideanSpace ℝ (Fin (P.n + 1))) :=
    {z : EuclideanSpace ℝ (Fin (P.n + 1)) |
      0 < z 0 ∧
      (∀ i : Fin P.m,
        z 0 * P.f i
            (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin P.n)).symm
              (fun j : Fin P.n => z j.succ / z 0) : EuclideanSpace ℝ (Fin P.n))) ≤ 0)}
  let zStar : EuclideanSpace ℝ (Fin (P.n + 1)) :=
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (P.n + 1))).symm (Fin.cons 1 fun j => x_tilde j)
  let dehom : EuclideanSpace ℝ (Fin (P.n + 1)) → EuclideanSpace ℝ (Fin P.n) :=
    fun z =>
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin P.n)).symm
        (fun j : Fin P.n => z j.succ / z 0)
  let g : Fin P.m → EuclideanSpace ℝ (Fin (P.n + 1)) → ℝ :=
    fun i z => z 0 * P.f i (dehom z)
  -- Route correction: use a neighborhood around the Slater point rather than a global openness
  -- argument, since the dehomogenization map only needs continuity where the first coordinate
  -- stays nonzero.
  have hzStar_zero : zStar 0 = 1 := by
    simp [zStar]
  have hzStar_succ (j : Fin P.n) : zStar j.succ = x_tilde j := by
    simp [zStar]
  have hdehom_zStar : dehom zStar = x_tilde := by
    -- The chosen center dehomogenizes back to the given Slater point.
    ext j
    simp [dehom, hzStar_zero, hzStar_succ]
  have hdehom_cont : ContinuousAt dehom zStar := by
    -- Each coordinate of `dehom` is a quotient with denominator `z 0 = 1` at the Slater center.
    have hcoord (k : Fin (P.n + 1)) :
        Continuous fun z : EuclideanSpace ℝ (Fin (P.n + 1)) => z k := by
      simpa using
        (continuous_apply k).comp (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (P.n + 1))).continuous
    have hcoords :
        ContinuousAt (fun z : EuclideanSpace ℝ (Fin (P.n + 1)) => fun j : Fin P.n => z j.succ / z 0)
          zStar := by
      rw [continuousAt_pi]
      intro j
      exact ContinuousAt.div (hcoord j.succ).continuousAt
        (hcoord 0).continuousAt (by simp [hzStar_zero])
    exact (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin P.n)).symm.continuousAt.comp hcoords
  have hg_cont (i : Fin P.m) : ContinuousAt (g i) zStar := by
    -- Compose the continuous dehomogenization with continuity of each convex constraint.
    have hfi_cont :
        ContinuousAt (P.f i) x_tilde := by
      exact (ConvexOn.continuousOn isOpen_univ (hconvex i)).continuousAt <|
        by simp
    have hfi_cont_dehom : ContinuousAt (P.f i) (dehom zStar) := by
      simpa [hdehom_zStar] using hfi_cont
    have hcomp : ContinuousAt (fun z : EuclideanSpace ℝ (Fin (P.n + 1)) => P.f i (dehom z)) zStar :=
      hfi_cont_dehom.comp hdehom_cont
    have hcoord_zero :
        Continuous fun z : EuclideanSpace ℝ (Fin (P.n + 1)) => z 0 := by
      simpa using
        (continuous_apply 0).comp (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (P.n + 1))).continuous
    exact ContinuousAt.mul hcoord_zero.continuousAt hcomp
  have hzStar_mem_target : zStar ∈ targetSet := by
    -- The center itself satisfies the strict Slater inequalities, hence also the weak ones.
    refine ⟨by simp [hzStar_zero], ?_⟩
    intro i
    exact le_of_lt (by simpa [targetSet, g, hzStar_zero, hdehom_zStar] using hSlater i)
  have hpos_nhds : {z : EuclideanSpace ℝ (Fin (P.n + 1)) | 0 < z 0} ∈ nhds zStar := by
    -- Positivity of the homogenizing coordinate persists on a neighborhood of `zStar`.
    have hcoord_zero :
        Continuous fun z : EuclideanSpace ℝ (Fin (P.n + 1)) => z 0 := by
      simpa using
        (continuous_apply 0).comp (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (P.n + 1))).continuous
    simpa [Set.preimage, Set.mem_setOf_eq] using
      ContinuousAt.preimage_mem_nhds hcoord_zero.continuousAt
        (Ioi_mem_nhds (show (0 : ℝ) < zStar 0 by simp [hzStar_zero]))
  have hconstraint_nhds (i : Fin P.m) :
      {z : EuclideanSpace ℝ (Fin (P.n + 1)) | g i z < 0} ∈ nhds zStar := by
    -- Each strict inequality also persists by continuity at the Slater center.
    simpa [Set.preimage, Set.mem_setOf_eq] using
      ContinuousAt.preimage_mem_nhds (hg_cont i)
        (Iio_mem_nhds (show g i zStar < 0 by simpa [g, hzStar_zero, hdehom_zStar] using hSlater i))
  have hstrict_nhds :
      ({z : EuclideanSpace ℝ (Fin (P.n + 1)) | 0 < z 0} ∩
          ⋂ i : Fin P.m, {z : EuclideanSpace ℝ (Fin (P.n + 1)) | g i z < 0}) ∈ nhds zStar := by
    -- Intersect the positivity neighborhood with the finitely many strict-constraint neighborhoods.
    refine Filter.inter_mem hpos_nhds ?_
    rw [Filter.iInter_mem]
    intro i
    exact hconstraint_nhds i
  rcases Metric.mem_nhds_iff.mp hstrict_nhds with ⟨ε, hε_pos, hball_subset⟩
  refine ⟨zStar, subset_closure hzStar_mem_target, ε, hε_pos, ?_⟩
  intro z hz
  have hz_mem_strict := hball_subset hz
  have hz_pos : 0 < z 0 := hz_mem_strict.1
  have hz_lt : ∀ i : Fin P.m, g i z < 0 := by
    intro i
    exact (Set.mem_iInter.mp hz_mem_strict.2) i
  -- The strict neighborhood sits inside the original cone, hence inside its closure.
  apply subset_closure
  refine ⟨hz_pos, ?_⟩
  intro i
  exact le_of_lt (hz_lt i)

end «problem-38»
