import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-139»

-- chapter5_Ex_18

/- [BLOCK chapter5 Ex.18 | 10 | defn]
A point z* in the domain of a function f is a local minimizer if there exists varepsilon>0 such that
f(z*)≤ f(z) for all z satisfying ‖z-z*‖< varepsilon.
-/
def IsLocalMinimizer {E β : Type*} [NormedAddCommGroup E] [Preorder β] (f : E → β) (zStar : E) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ z : E, ‖z - zStar‖ < ε → f zStar ≤ f z


/- [BLOCK chapter5 Ex.18 | 13 | opt_prob]
Let A∈ℝ^{m× n} and r ∈ ℕ be given. The decision variables are X∈ℝ^{m× r} and Y∈ℝ^{r× n}. Consider
the optimization problem
min_{X,Y} f(X,Y), f(X,Y)=‖A-XY‖_F^2.
-/
structure LowRankMatrixFactorizationProblem (m n r : Type*)
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r] where
  A : Matrix m n ℝ
  objective : Matrix m r ℝ → Matrix r n ℝ → ℝ :=
    fun X Y => ∑ i, ∑ j, (A i j - (X * Y) i j) ^ 2

def LowRankMatrixFactorizationProblem.isOptimal
    {m n r : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (p : LowRankMatrixFactorizationProblem m n r) (X : Matrix m r ℝ) (Y : Matrix r n ℝ) : Prop :=
  ∀ X' : Matrix m r ℝ, ∀ Y' : Matrix r n ℝ,
    p.objective X Y ≤ p.objective X' Y'

/- [BLOCK chapter5 Ex.18 | 14 | thm]
Let a given matrix A ∈ ℝ^{m × n} and a given rank parameter r ∈ ℕ be specified. The decision
variables are X ∈ ℝ^{m × r} and Y ∈ ℝ^{r × n}. Consider the low-rank matrix factorization problem
min_{X,Y} f(X,Y), f(X,Y)=‖A-XY‖_F^2, where ‖·‖_F denotes the Frobenius norm, i.e., the square root
of the sum of the squares of all matrix entries. The dimensions of the matrix product XY are
guaranteed by the above specification to be well-defined. Let (X*,Y*) ∈ ℝ^{m × r} × ℝ^{r × n} be a
local minimizer of this problem. Write down the necessary conditions for (X*,Y*) to be a local
minimizer. In the statement, explicitly give the first-order stationary conditions of the objective
function with respect to X and Y, and further explain the second-order necessary conditions that a
local minimizer should satisfy.
-/
open scoped RealInnerProductSpace

/-- Convert the metric-ball formulation of a local minimizer into mathlib's filter-based notion. -/
lemma IsLocalMinimizer.toIsLocalMin
    {E β : Type*} [NormedAddCommGroup E] [Preorder β] {f : E → β} {zStar : E}
    (h : IsLocalMinimizer f zStar) : IsLocalMin f zStar := by
  rcases h with ⟨ε, hε, hεmin⟩
  -- The witness ball from `IsLocalMinimizer` is a neighborhood on which the minimizer inequality holds.
  refine Filter.mem_of_superset (Metric.ball_mem_nhds zStar hε) ?_
  intro z hz
  exact hεmin z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)

/-- At a one-dimensional local minimum, the second derivative at the minimizer is nonnegative. -/
lemma secondDerivative_nonneg_at_localMin_zero
    {g : ℝ → ℝ} (hmin : IsLocalMin g 0) (hg : ContDiffAt ℝ 2 g 0) :
    0 ≤ deriv (deriv g) 0 := by
  by_contra hnonneg
  have hneg : deriv (deriv g) 0 < 0 := by
    linarith
  have hmax : IsLocalMax g 0 := by
    -- A negative second derivative together with the first-order stationarity gives a local maximum.
    exact isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hg.continuousAt
  have hconst : g =ᶠ[𝓝 0] fun _ => g 0 :=
    eventuallyEq_of_isMinFilter_of_isMaxFilter hmin hmax
  have hderivConst : deriv g =ᶠ[𝓝 0] fun _ => 0 := by
    -- Local constancy forces the first derivative to vanish near the minimizer.
    simpa using hconst.deriv
  have hsecondZero : deriv (deriv g) 0 = 0 := by
    -- Differentiating the zero first derivative once more forces the second derivative to vanish.
    rw [EventuallyEq.deriv_eq hderivConst, deriv_const]
  linarith

/-- The second derivative of the line restriction equals the Hessian quadratic form. -/
lemma lineSecondDerivative_eq_hessianQuadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {x d : E} (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (fun t : ℝ => f (x + t • d))) 0 = ⟪d, (fderiv ℝ (gradient f) x) d⟫ := by
  let line : ℝ → E := fun t => x + t • d
  let ψ : ℝ → ℝ := fun t => (fderiv ℝ f (line t)) d
  have hlineDeriv : HasDerivAt line d 0 := by
    -- The affine line through `x` in direction `d` has constant derivative `d`.
    simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hnear : ∀ᶠ t in 𝓝 0, ContDiffAt ℝ 2 f (line t) := by
    -- The `C²` hypothesis persists in a neighborhood and can be pulled back along the line.
    have hnearX : ∀ᶠ y in 𝓝 (line 0), ContDiffAt ℝ 2 f y := by
      simpa [line] using hf.eventually (by simp)
    exact (by fun_prop : ContinuousAt line 0).tendsto.eventually hnearX
  have hderivEq : deriv (fun t : ℝ => f (line t)) =ᶠ[𝓝 0] ψ := by
    -- Near `0`, the derivative of the line restriction is the Fréchet derivative applied to `d`.
    filter_upwards [hnear] with t ht
    have hlineDeriv_t : HasDerivAt line d t := by
      simpa [line] using ((hasDerivAt_id t).smul_const d).const_add x
    have hdiff_t : DifferentiableAt ℝ f (line t) := ht.differentiableAt two_ne_zero
    simpa [ψ] using (hdiff_t.hasFDerivAt.comp_hasDerivAt t hlineDeriv_t).deriv
  have hψDeriv : HasDerivAt ψ (((fderiv ℝ (fderiv ℝ f) x) d) d) 0 := by
    let evalD : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ d
    have hfderivDiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
      -- A `C²` function has a differentiable first derivative.
      exact
        ((hf.fderiv_right (m := 1) (by decide : ((1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))))
          .differentiableAt one_ne_zero)
    have hcomp : HasDerivAt ((fderiv ℝ f) ∘ line) ((fderiv ℝ (fderiv ℝ f) x) d) 0 := by
      -- Chain rule for `fderiv f` along the affine line.
      exact hfderivDiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hlineDeriv (by simp [line])
    -- Evaluating the derivative map at `d` extracts the duplicated second directional derivative.
    simpa [ψ, evalD] using evalD.hasFDerivAt.comp_hasDerivAt 0 hcomp
  have hsecond :
      deriv (deriv (fun t : ℝ => f (line t))) 0 = ((fderiv ℝ (fderiv ℝ f) x) d) d := by
    -- Replace the derivative of the line restriction by the derivative of `ψ`.
    rw [EventuallyEq.deriv_eq hderivEq]
    exact hψDeriv.deriv
  have hgradApply :
      (fderiv ℝ (gradient f) x) d =
        (InnerProductSpace.toDual ℝ E).symm ((fderiv ℝ (fderiv ℝ f) x) d : StrongDual ℝ E) := by
    have hgrad :
        fderiv ℝ (gradient f) x =
          (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv : StrongDual ℝ E ≃L[ℝ] E) :
            StrongDual ℝ E →L[ℝ] E).comp
            (fderiv ℝ (fderiv ℝ f) x) := by
      -- Route correction: instead of differentiating `gradient` directly, rewrite it as `toDual.symm ∘ fderiv`.
      simpa [gradient, Function.comp_def] using
        (((InnerProductSpace.toDual ℝ E).symm : StrongDual ℝ E ≃ₗᵢ[ℝ] E).comp_fderiv
          (f := fderiv ℝ f) (x := x))
    simpa using congrArg (fun L : E →L[ℝ] E => L d) hgrad
  -- Rewrite the duplicated Fréchet derivative as the Hessian quadratic form.
  calc
    deriv (deriv (fun t : ℝ => f (x + t • d))) 0 = ((fderiv ℝ (fderiv ℝ f) x) d) d := by
      simpa [line] using hsecond
    _ = ⟪(InnerProductSpace.toDual ℝ E).symm ((fderiv ℝ (fderiv ℝ f) x) d : StrongDual ℝ E), d⟫ := by
      symm
      rw [InnerProductSpace.toDual_symm_apply]
    _ = ⟪(fderiv ℝ (gradient f) x) d, d⟫ := by rw [hgradApply]
    _ = ⟪d, (fderiv ℝ (gradient f) x) d⟫ := by rw [real_inner_comm]

/-- A `C²` local minimum has a nonnegative Hessian quadratic form in every direction. -/
lemma hessianQuadratic_nonneg_of_localMin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {x : E} (hmin : IsLocalMin f x) (hf : ContDiffAt ℝ 2 f x) :
    ∀ d : E, 0 ≤ ⟪d, (fderiv ℝ (gradient f) x) d⟫ := by
  intro d
  let φ : ℝ → ℝ := fun t => f (x + t • d)
  have hφmin : IsLocalMin φ 0 := by
    -- Restrict the ambient local minimum to the affine line through `x`.
    have hminLine : IsLocalMin f ((fun t : ℝ => x + t • d) 0) := by
      simpa using hmin
    simpa [φ] using hminLine.comp_continuous (g := fun t : ℝ => x + t • d) (b := 0) (by fun_prop)
  have hφsmooth : ContDiffAt ℝ 2 φ 0 := by
    -- The line restriction remains `C²`.
    have hfLine : ContDiffAt ℝ 2 f ((fun t : ℝ => x + t • d) 0) := by
      simpa using hf
    simpa [φ] using hfLine.comp 0 (by fun_prop)
  have hsecond : 0 ≤ deriv (deriv φ) 0 :=
    secondDerivative_nonneg_at_localMin_zero hφmin hφsmooth
  -- Translate the one-dimensional second derivative back to the Hessian quadratic form.
  simpa [φ, lineSecondDerivative_eq_hessianQuadratic (f := f) (x := x) (d := d) hf] using hsecond

theorem lowRankMatrixFactorization_localMinimizer_necessary_conditions
    {m n r : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    [InnerProductSpace ℝ (Matrix m r ℝ × Matrix r n ℝ)]
    (p : LowRankMatrixFactorizationProblem m n r)
    (XStar : Matrix m r ℝ) (YStar : Matrix r n ℝ)
    (hloc :
      IsLocalMinimizer
        (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
          ∑ i, ∑ j, (p.A i j - (Z.1 * Z.2) i j) ^ 2)
        (XStar, YStar)) :
    fderiv ℝ
        (fun X : Matrix m r ℝ => ∑ i, ∑ j, (p.A i j - (X * YStar) i j) ^ 2)
        XStar = 0 ∧
      fderiv ℝ
        (fun Y : Matrix r n ℝ => ∑ i, ∑ j, (p.A i j - (XStar * Y) i j) ^ 2)
        YStar = 0 ∧
      (ContDiffAt ℝ 2
          (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
            ∑ i, ∑ j, (p.A i j - (Z.1 * Z.2) i j) ^ 2)
          (XStar, YStar) →
        ∀ d : Matrix m r ℝ × Matrix r n ℝ,
          0 ≤
            ⟪d,
              (fderiv ℝ
                (gradient
                  (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
                    ∑ i, ∑ j, (p.A i j - (Z.1 * Z.2) i j) ^ 2))
                (XStar, YStar)) d⟫) := by
  let F : (Matrix m r ℝ × Matrix r n ℝ) → ℝ :=
    fun Z => ∑ i, ∑ j, (p.A i j - (Z.1 * Z.2) i j) ^ 2
  have hF : IsLocalMin F (XStar, YStar) := by
    -- Convert the custom local minimizer assumption into the standard local minimum API.
    exact hloc.toIsLocalMin
  constructor
  · have hX : IsLocalMin (fun X : Matrix m r ℝ => F (X, YStar)) XStar := by
      -- Freeze `YStar` and restrict the local minimum to the `X`-coordinates.
      simpa [F] using
        hF.comp_continuous (g := fun X : Matrix m r ℝ => (X, YStar)) (b := XStar) (by fun_prop)
    -- Fermat's theorem gives the vanishing derivative in the `X` direction.
    simpa [F] using hX.fderiv_eq_zero
  constructor
  · have hY : IsLocalMin (fun Y : Matrix r n ℝ => F (XStar, Y)) YStar := by
      -- Freeze `XStar` and restrict the local minimum to the `Y`-coordinates.
      simpa [F] using
        hF.comp_continuous (g := fun Y : Matrix r n ℝ => (XStar, Y)) (b := YStar) (by fun_prop)
    -- Fermat's theorem gives the vanishing derivative in the `Y` direction.
    simpa [F] using hY.fderiv_eq_zero
  · intro hContDiff d
    -- The Hessian of the full objective is nonnegative on every direction at a local minimum.
    simpa [F] using hessianQuadratic_nonneg_of_localMin (f := F) (x := (XStar, YStar)) hF hContDiff d

end «problem-139»
