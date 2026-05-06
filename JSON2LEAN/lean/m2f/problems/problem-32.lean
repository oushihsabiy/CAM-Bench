import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open scoped MatrixOrder
open Filter
open scoped BigOperators

namespace «problem-32»

/- [BLOCK Exercise 8.20 | 12 | defn]
An ellipsoid in ℝ^n is a set of the form
{x∈ ℝ^n| (x-c)ᵀ P (x-c)≤ 1},
for some center $c∈ ℝ^n and some symmetric positive definite matrix P∈ S^n.
-/
def ellipsoid {n : ℕ} (c : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (_hP_symm : P.IsSymm)
    (_hP_pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (P.mulVec x)) :
    Set (Fin n → ℝ) :=
  {x | dotProduct (x - c) (P.mulVec (x - c)) ≤ 1}

/- [BLOCK Exercise 8.20 | 13 | opt_prob]
Let
C={x∈ ℝ^n| x₁A_1+x₂A_2+·s+x_nA_npreceq B},
where A₁,dots,Aₙ,B∈ S^m, S^m is the set of real symmetric m× m matrices, and for X,Y∈ S^m,
Xpreceq Y means that Y-X is positive semidefinite. Assume that C has nonempty interior. Let
x_ac be the minimizer of
φ(x)=-logdet(B-x₁A_1-x₂A_2-·s-x_nA_n)
over the domain
{x∈ ℝ^n| B-x₁A_1-x₂A_2-·s-x_nA_nsucc 0},
where Xsucc 0 means that X is positive definite.
-/
structure LogDetAnalyticCenterProblem (n m : ℕ) where
  A : Fin n → Matrix (Fin m) (Fin m) ℝ
  B : Matrix (Fin m) (Fin m) ℝ
  A_symm : ∀ i, (A i).IsSymm
  B_symm : B.IsSymm
  interior_nonempty :
    ∃ x : Fin n → ℝ,
      Matrix.PosDef (B - ∑ i, (x i) • A i)
  x_ac : Fin n → ℝ

def LogDetAnalyticCenterProblem.slack {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x : Fin n → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  p.B - ∑ i, (x i) • p.A i

def LogDetAnalyticCenterProblem.feasible {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x : Fin n → ℝ) : Prop :=
  Matrix.PosSemidef (p.slack x)

def LogDetAnalyticCenterProblem.strictlyFeasible {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x : Fin n → ℝ) : Prop :=
  Matrix.PosDef (p.slack x)

def LogDetAnalyticCenterProblem.constraintSet {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) : Set (Fin n → ℝ) :=
  {x | p.feasible x}

def LogDetAnalyticCenterProblem.domain {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) : Set (Fin n → ℝ) :=
  {x | p.strictlyFeasible x}

def LogDetAnalyticCenterProblem.objective {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x : Fin n → ℝ) : ℝ :=
  -Real.log (Matrix.det (p.slack x))

def LogDetAnalyticCenterProblem.IsAnalyticCenter {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x_ac : Fin n → ℝ) : Prop :=
  x_ac ∈ p.domain ∧
    ∀ x ∈ p.domain, p.objective x_ac ≤ p.objective x

/-- Every strictly feasible point of the log-det problem is feasible. -/
lemma LogDetAnalyticCenterProblem.feasible_of_strictlyFeasible {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) {x : Fin n → ℝ}
    (hx : p.strictlyFeasible x) :
    p.feasible x := by
  -- A positive-definite slack matrix is automatically positive semidefinite.
  simpa [LogDetAnalyticCenterProblem.feasible,
    LogDetAnalyticCenterProblem.strictlyFeasible] using hx.posSemidef

/-- The strict-feasibility domain is contained in the semidefinite constraint set. -/
lemma LogDetAnalyticCenterProblem.domain_subset_constraintSet {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) :
    p.domain ⊆ p.constraintSet := by
  -- Unfold the two sets and apply the basic positivity implication pointwise.
  intro x hx
  simpa [LogDetAnalyticCenterProblem.domain, LogDetAnalyticCenterProblem.constraintSet] using
    p.feasible_of_strictlyFeasible (x := x) hx

/-- An analytic center is automatically a point of the semidefinite constraint set. -/
lemma LogDetAnalyticCenterProblem.analyticCenter_mem_constraintSet {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) {x : Fin n → ℝ}
    (hx : p.IsAnalyticCenter x) :
    x ∈ p.constraintSet := by
  -- The analytic-center hypothesis already records that `x` lies in the strict domain.
  exact p.domain_subset_constraintSet hx.1

/-- Every slack matrix in the log-det problem is symmetric. -/
lemma LogDetAnalyticCenterProblem.slack_isSymm {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x : Fin n → ℝ) :
    (p.slack x).IsSymm := by
  -- The constant term is symmetric, and the variable-dependent sum preserves symmetry termwise.
  have hsum : (∑ i, (x i) • p.A i).IsSymm := by
    classical
    -- Build symmetry of the sum by induction over the finite index set.
    refine Finset.induction_on Finset.univ ?_ ?_
    · simp
    · intro i s hi hs
      simp [Finset.sum_insert, hi, hs, (p.A_symm i).smul (x i)]
  -- The slack is the difference of these two symmetric matrices.
  simpa [LogDetAnalyticCenterProblem.slack] using p.B_symm.sub hsum

/-- The slack at `x` is the analytic-center slack minus the displacement-weighted matrix sum. -/
lemma LogDetAnalyticCenterProblem.slack_sub_analyticCenter {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (x : Fin n → ℝ) :
    p.slack x = p.slack p.x_ac - ∑ i, ((x - p.x_ac) i) • p.A i := by
  -- Split the coefficient vector into the analytic-center part plus the displacement.
  have hsum :
      ∑ i, (x i) • p.A i =
        ∑ i, (p.x_ac i) • p.A i + ∑ i, ((x - p.x_ac) i) • p.A i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    -- Pointwise, `x i` decomposes as the center coordinate plus the displacement.
    have hx : x i = p.x_ac i + (x - p.x_ac) i := by
      simp [Pi.sub_apply]
    rw [hx, add_smul]
  -- Substitute the coefficient decomposition into the affine slack formula.
  rw [LogDetAnalyticCenterProblem.slack, hsum, LogDetAnalyticCenterProblem.slack]
  abel

/-- Along an affine line through the analytic center, the slack varies linearly in the direction. -/
lemma LogDetAnalyticCenterProblem.slack_line_through_analyticCenter {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (u : Fin n → ℝ) (t : ℝ) :
    p.slack (p.x_ac + t • u) = p.slack p.x_ac - t • ∑ i, (u i) • p.A i := by
  -- First rewrite the pointwise displacement from `x_ac`.
  have hshift : p.x_ac + t • u - p.x_ac = t • u := by
    -- The affine line is centered at `x_ac`, so the displacement is exactly `t • u`.
    ext i
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  -- Then invoke the generic affine slack expansion around `x_ac`.
  rw [p.slack_sub_analyticCenter, hshift]
  -- Pull the scalar `t` out of the matrix sum.
  simp [Finset.smul_sum, smul_smul]

/-- The analytic-center slack matrix is positive definite. -/
lemma LogDetAnalyticCenterProblem.slack_analyticCenter_posDef {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m)
    (hx_ac : p.IsAnalyticCenter p.x_ac) :
    Matrix.PosDef (p.slack p.x_ac) := by
  -- The analytic-center hypothesis records strict feasibility at `p.x_ac`.
  simpa [LogDetAnalyticCenterProblem.domain,
    LogDetAnalyticCenterProblem.strictlyFeasible] using hx_ac.1

/-- The matrix sum attached to a direction is symmetric. -/
lemma LogDetAnalyticCenterProblem.directionMatrix_isSymm {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m) (u : Fin n → ℝ) :
    (∑ i, (u i) • p.A i).IsSymm := by
  classical
  -- Sum the symmetric data matrices termwise along the chosen direction.
  refine Finset.induction_on Finset.univ ?_ ?_
  · simp
  · intro i s hi hs
    simp [Finset.sum_insert, hi, hs, (p.A_symm i).smul (u i)]

/-- Conjugating by the square root of the analytic-center slack normalizes the slack on a line. -/
lemma LogDetAnalyticCenterProblem.normalizedSlack_line {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m)
    (hx_ac : p.IsAnalyticCenter p.x_ac)
    (u : Fin n → ℝ) (t : ℝ) :
    let X := p.slack p.x_ac
    let T := CFC.sqrt X
    let S : Matrix (Fin m) (Fin m) ℝ := ∑ i, (u i) • p.A i
    let Δ : Matrix (Fin m) (Fin m) ℝ := T⁻¹ * S * T⁻¹
    p.slack (p.x_ac + t • u) = T * (1 - t • Δ) * T := by
  classical
  dsimp
  set X : Matrix (Fin m) (Fin m) ℝ := p.slack p.x_ac
  set T : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt X
  set S : Matrix (Fin m) (Fin m) ℝ := ∑ i, (u i) • p.A i
  set Δ : Matrix (Fin m) (Fin m) ℝ := T⁻¹ * S * T⁻¹
  have hX_pos : Matrix.PosDef X := by
    -- The analytic center lies in the strict domain, so its slack is positive definite.
    simpa [X] using p.slack_analyticCenter_posDef hx_ac
  have hT_unit : IsUnit T := by
    -- Invertibility passes from a positive-definite matrix to its square root.
    simpa [T, X] using (CFC.isUnit_sqrt_iff X).2 hX_pos.isUnit
  letI := hT_unit.invertible
  have hconj : T * Δ * T = S := by
    -- Cancel the square root against its inverse on both sides of the direction matrix.
    calc
      T * Δ * T = ((T * T⁻¹) * S) * (T⁻¹ * T) := by
        simp [Δ, Matrix.mul_assoc]
      _ = S := by
        simp
  have hTT : T * T = X := by
    -- The square root squares back to the analytic-center slack.
    simpa [T, X] using CFC.sqrt_mul_sqrt_self X
  calc
    p.slack (p.x_ac + t • u) = X - t • S := by
      simpa [X, S] using p.slack_line_through_analyticCenter u t
    _ = T * T - t • (T * Δ * T) := by
      rw [← hTT, ← hconj]
    _ = T * (1 - t • Δ) * T := by
      -- Regroup the two terms into one conjugated normalized slack matrix.
      symm
      calc
        T * (1 - t • Δ) * T = (T * (1 - t • Δ)) * T := by rw [Matrix.mul_assoc]
        _ = (T * 1 - T * (t • Δ)) * T := by rw [mul_sub]
        _ = (T - t • (T * Δ)) * T := by simp
        _ = T * T - t • ((T * Δ) * T) := by
          rw [sub_mul]
          simp
        _ = T * T - t • (T * Δ * T) := by rw [Matrix.mul_assoc]

/-- Restricting a differentiable function to an affine line differentiates in the line direction. -/
lemma hasDerivAt_lineMap_apply_fderiv
    {n : ℕ} {g : (Fin n → ℝ) → ℝ} {x y : Fin n → ℝ} {t : ℝ}
    (hg : DifferentiableAt ℝ g (AffineMap.lineMap x y t)) :
    HasDerivAt (fun s => g (AffineMap.lineMap x y s))
      (fderiv ℝ g (AffineMap.lineMap x y t) (y - x)) t := by
  -- Compose the ambient derivative with the standard derivative of the affine line map.
  exact hg.hasFDerivAt.comp_hasDerivAt t (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))

/-- Evaluating the derivative of `y ↦ fderiv g y` on a fixed vector recovers the same entry of the
second Fréchet derivative. -/
lemma fderiv_apply_const_eq_fderiv_fderiv
    {n : ℕ} {g : (Fin n → ℝ) → ℝ} {x v w : Fin n → ℝ}
    (hg2 : ContDiffAt ℝ 2 g x) :
    (fderiv ℝ (fun y => (fderiv ℝ g y) w) x) v = fderiv ℝ (fderiv ℝ g) x v w := by
  -- Differentiate the CLM-valued derivative map and then evaluate at the fixed vector `w`.
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := (hg2.fderiv_right_succ).differentiableAt_one
  have hclm :
      fderiv ℝ (fun y => (fderiv ℝ g y) w) x =
        (fderiv ℝ (fderiv ℝ g) x).flip w := by
    simpa using
      fderiv_clm_apply (c := fderiv ℝ g) (u := fun _ : Fin n → ℝ => w) (x := x) hfdiff
        (differentiableAt_const w)
  simpa using congrArg (fun A => A v) hclm

/-- The second derivative of a line restriction equals the diagonal evaluation of the second
Fréchet derivative in the line direction. -/
lemma hasDerivAt_lineMap_apply_iteratedFDeriv
    {n : ℕ} {g : (Fin n → ℝ) → ℝ} {x y : Fin n → ℝ} {t : ℝ}
    (hg2 : ContDiffAt ℝ 2 g (AffineMap.lineMap x y t)) :
    HasDerivAt (fun s => (fderiv ℝ g (AffineMap.lineMap x y s)) (y - x))
      (iteratedFDeriv ℝ 2 g (AffineMap.lineMap x y t) ![y - x, y - x]) t := by
  -- Differentiate the scalar directional derivative along the same affine line.
  have hdiff :
      DifferentiableAt ℝ (fun z => (fderiv ℝ g z) (y - x)) (AffineMap.lineMap x y t) := by
    exact ((hg2.fderiv_right_succ).clm_apply contDiffAt_const).differentiableAt_one
  convert
      hasDerivAt_lineMap_apply_fderiv
        (g := fun z => (fderiv ℝ g z) (y - x)) (x := x) (y := y) (t := t) hdiff using 1
  rw [fderiv_apply_const_eq_fderiv_fderiv (g := g) (x := AffineMap.lineMap x y t) (v := y - x)
      (w := y - x) hg2]
  simp [iteratedFDeriv_two_apply]

/-- Expanding the second Fréchet derivative in the standard basis recovers the coordinate
quadratic form that the theorem stores in the matrix `H`. -/
lemma coordinateQuadraticForm_eq_iteratedFDeriv_diag
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x z : Fin n → ℝ}
    (hf2 : ContDiffAt ℝ 2 f x) :
    ∑ i : Fin n, z i *
      ∑ j : Fin n, z j *
        ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ))) =
      iteratedFDeriv ℝ 2 f x ![z, z] := by
  -- First rewrite each coordinate entry as the corresponding component of the bilinear Hessian.
  have hentry (i j : Fin n) :
      (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x) (Pi.single i (1 : ℝ)) =
        ((fderiv ℝ (fderiv ℝ f) x) (Pi.single i (1 : ℝ))) (Pi.single j (1 : ℝ)) := by
    simpa using
      fderiv_apply_const_eq_fderiv_fderiv (g := f) (x := x) (v := Pi.single i (1 : ℝ))
        (w := Pi.single j (1 : ℝ)) hf2
  -- Then package the coordinate sum back into the canonical iterated derivative.
  calc
    ∑ i : Fin n, z i *
      ∑ j : Fin n, z j *
        ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
          (Pi.single i (1 : ℝ))) =
      bilinearIteratedFDerivTwo ℝ f x z z := by
        simpa [dotProduct, Matrix.mulVec, bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
          iteratedFDeriv_two_apply, hentry,
          mul_assoc, mul_left_comm, mul_comm] using
          (apply_eq_dotProduct_toMatrix₂_mulVec (b₁ := Pi.basisFun ℝ (Fin n))
            (b₂ := Pi.basisFun ℝ (Fin n)) (B := bilinearIteratedFDerivTwo ℝ f x) z z).symm
    _ = iteratedFDeriv ℝ 2 f x ![z, z] := by
      rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]

/-- Once `H` is identified with the coordinate Hessian at `p.x_ac`, its quadratic form matches
the diagonal second Fréchet derivative in the same direction. -/
lemma quadraticForm_eq_iteratedFDeriv_at_analyticCenter
    {n m : ℕ} (p : LogDetAnalyticCenterProblem n m)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH_hessian :
      H = fun i j =>
        (fderiv ℝ
          (fun y : Fin n → ℝ =>
            (fderiv ℝ p.objective y (Pi.single j (1 : ℝ)))) p.x_ac)
          (Pi.single i (1 : ℝ)))
    (hobjective₂ : ContDiffAt ℝ 2 p.objective p.x_ac)
    (u : Fin n → ℝ) :
    dotProduct u (H.mulVec u) = iteratedFDeriv ℝ 2 p.objective p.x_ac ![u, u] := by
  -- Expand the matrix quadratic form into the coordinate expression used by `hH_hessian`.
  calc
    dotProduct u (H.mulVec u) =
      ∑ i : Fin n, u i *
        ∑ j : Fin n, u j *
          ((fderiv ℝ
            (fun y : Fin n → ℝ =>
              (fderiv ℝ p.objective y (Pi.single j (1 : ℝ)))) p.x_ac)
            (Pi.single i (1 : ℝ))) := by
        simp [dotProduct, Matrix.mulVec, hH_hessian, mul_comm]
    _ = iteratedFDeriv ℝ 2 p.objective p.x_ac ![u, u] := by
      simpa using
        (coordinateQuadraticForm_eq_iteratedFDeriv_diag (f := p.objective) (x := p.x_ac)
          (z := u) hobjective₂)

/-- If every eigenvalue is at most `1` and their sum is `0`, then the sum of squares is at most
`m (m - 1)`. This is the scalar inequality needed for the outer ellipsoid estimate. -/
lemma eigenvalue_square_bound_of_le_one_and_zero_sum
    {m : ℕ} (lambda : Fin m → ℝ)
    (h_le : ∀ i, lambda i ≤ 1)
    (h_sum : ∑ i, lambda i = 0) :
    ∑ i, (lambda i)^2 ≤ (m : ℝ) * (m - 1) := by
  -- First bound each eigenvalue from below by using that the other `m - 1` values are all `≤ 1`.
  have h_lower : ∀ i, -(m - 1 : ℝ) ≤ lambda i := by
    intro i
    have hsum_erase := by
      show Finset.sum (Finset.univ.erase i) (fun j : Fin m => lambda j) = -lambda i
      have hsplit :=
        Finset.sum_erase_add (s := Finset.univ) (f := fun j : Fin m => lambda j) (a := i)
          (by simp)
      rw [h_sum] at hsplit
      linarith
    have hupper :
        Finset.sum (Finset.univ.erase i) (fun j : Fin m => lambda j) ≤ (m - 1 : ℝ) := by
      calc
        Finset.sum (Finset.univ.erase i) (fun j : Fin m => lambda j) ≤
            Finset.sum (Finset.univ.erase i) (fun _ : Fin m => (1 : ℝ)) := by
          exact Finset.sum_le_sum fun j _ => h_le j
        _ = ((Finset.univ.erase i).card : ℝ) := by simp
        _ = (m - 1 : ℝ) := by
          have hm_pos : 0 < m := by
            simpa using (Fintype.card_pos_iff.mpr ⟨i⟩ : 0 < Fintype.card (Fin m))
          have hm_one : 1 ≤ m := Nat.succ_le_of_lt hm_pos
          simp [Finset.card_erase_of_mem, hm_one, Nat.cast_sub]
    have hneg_le : -lambda i ≤ (m - 1 : ℝ) := by simpa [hsum_erase] using hupper
    linarith
  -- Sum the nonnegative scalar inequality `(1 - λᵢ) * (λᵢ + (m - 1)) ≥ 0`.
  have hsum_nonneg :
      0 ≤ ∑ i, (1 - lambda i) * (lambda i + (m - 1 : ℝ)) := by
    refine Finset.sum_nonneg ?_
    intro i _
    exact mul_nonneg (sub_nonneg.mpr (h_le i)) (by linarith [h_lower i])
  have hexpand :
      ∑ i, (1 - lambda i) * (lambda i + (m - 1 : ℝ)) =
        (m : ℝ) * (m - 1) - ∑ i, (lambda i)^2 := by
    calc
      ∑ i, (1 - lambda i) * (lambda i + (m - 1 : ℝ)) =
          ∑ i, ((m - 1 : ℝ) + (2 - m : ℝ) * lambda i - (lambda i)^2) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = ∑ i, (m - 1 : ℝ) + (2 - m : ℝ) * ∑ i, lambda i - ∑ i, (lambda i)^2 := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = (m : ℝ) * (m - 1) - ∑ i, (lambda i)^2 := by
            rw [h_sum]
            simp
            ring
  nlinarith [hsum_nonneg, hexpand]

/-- The determinant of the affine slack matrix is analytic in the primal variable, so composing
with `Real.log` gives the local smoothness of the barrier at the analytic center. -/
lemma LogDetAnalyticCenterProblem.objective_contDiffAt_of_strictlyFeasible
    {n m : ℕ} (p : LogDetAnalyticCenterProblem n m) {x : Fin n → ℝ}
    (hx : p.strictlyFeasible x) :
    ContDiffAt ℝ 2 p.objective x := by
  let detPoly : MvPolynomial (Fin m × Fin m) ℝ :=
    Matrix.det (Matrix.mvPolynomialX (Fin m) (Fin m) ℝ)
  have hdet : AnalyticAt ℝ (fun y : Fin n → ℝ => Matrix.det (p.slack y)) x := by
    have hcoord :
        ∀ ij : Fin m × Fin m,
          AnalyticAt ℝ
            (fun y : Fin n → ℝ => p.B ij.1 ij.2 - ∑ k, y k * p.A k ij.1 ij.2) x := by
      intro ij
      -- Each entry of the slack matrix is affine in `y`, hence analytic.
      have hsum :
          AnalyticAt ℝ (fun y : Fin n → ℝ => ∑ k, y k * p.A k ij.1 ij.2) x := by
        refine Finset.univ.analyticAt_fun_sum ?_
        intro k hk
        exact (((ContinuousLinearMap.proj k) : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt x).mul
          (analyticAt_const : AnalyticAt ℝ (fun _ : Fin n → ℝ => p.A k ij.1 ij.2) x)
      exact analyticAt_const.sub hsum
    -- Evaluate the universal determinant polynomial on the affine slack entries.
    have han :=
      AnalyticAt.aeval_mvPolynomial (z := x)
        (f := fun y (ij : Fin m × Fin m) => p.B ij.1 ij.2 - ∑ k, y k * p.A k ij.1 ij.2)
        hcoord detPoly
    convert han using 1
    ext y
    have hmap :
        (Matrix.mvPolynomialX (Fin m) (Fin m) ℝ).map
          (MvPolynomial.eval
            (fun ij : Fin m × Fin m => p.B ij.1 ij.2 - ∑ k, y k * p.A k ij.1 ij.2)) =
          p.slack y := by
      -- Entrywise evaluation of the universal matrix polynomial recovers the concrete slack matrix.
      ext i j
      simp [LogDetAnalyticCenterProblem.slack]
      rw [Finset.sum_apply]
      simp
    symm
    simpa [detPoly, RingHom.map_det] using congrArg Matrix.det hmap
  have hdet_ne : Matrix.det (p.slack x) ≠ 0 := by
    -- Strict feasibility makes the slack positive definite, so its determinant is positive.
    exact hx.det_pos.ne'
  have hlog :
      ContDiffAt ℝ 2 (fun y : Fin n → ℝ => Real.log (Matrix.det (p.slack y))) x := by
    -- Compose the analytic determinant with the smooth logarithm at a nonzero point.
    exact ((Real.contDiffAt_log).2 hdet_ne).comp x hdet.contDiffAt
  -- Negating the logarithm gives the barrier objective.
  simpa [LogDetAnalyticCenterProblem.objective] using hlog.neg

lemma LogDetAnalyticCenterProblem.objective_contDiffAt_analyticCenter
    {n m : ℕ} (p : LogDetAnalyticCenterProblem n m)
    (hx_ac : p.IsAnalyticCenter p.x_ac) :
    ContDiffAt ℝ 2 p.objective p.x_ac := by
  -- Specialize the generic strict-feasibility smoothness lemma to the analytic center.
  exact p.objective_contDiffAt_of_strictlyFeasible hx_ac.1

/-- Applying the Hermitian functional calculus to `x ↦ 1 - t x` gives the affine matrix
perturbation `1 - t • A`. -/
lemma Matrix.IsHermitian.cfc_one_sub_smul
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    hA.cfc (fun x => 1 - t * x) = 1 - t • A := by
  let U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  let D : Matrix n n ℝ := Matrix.diagonal hA.eigenvalues
  have hdiag : Matrix.diagonal ((fun x => 1 - t * x) ∘ hA.eigenvalues) = 1 - t • D := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, hij]
  have hspectral : U * D * star U = A := by
    -- The spectral theorem diagonalizes `A` with the chosen eigenbasis.
    simpa [U, D, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem.symm
  calc
    hA.cfc (fun x => 1 - t * x) = U * Matrix.diagonal ((fun x => 1 - t * x) ∘ hA.eigenvalues) * star U := by
      rfl
    _ = U * (1 - t • D) * star U := by rw [hdiag]
    _ = (U * (1 - t • D)) * star U := by rw [mul_assoc]
    _ = (U * 1 - U * (t • D)) * star U := by rw [mul_sub]
    _ = U * 1 * star U - (U * (t • D)) * star U := by rw [sub_mul]
    _ = U * 1 * star U - t • (U * D * star U) := by simp [mul_assoc]
    _ = 1 - t • (U * D * star U) := by simp [U, mul_assoc]
    _ = 1 - t • A := by rw [hspectral]

/-- A Hermitian affine perturbation `1 - t • A` is positive semidefinite exactly when each shifted
eigenvalue `1 - t λᵢ` is nonnegative. -/
lemma Matrix.IsHermitian.one_sub_smul_posSemidef_iff
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    Matrix.PosSemidef (1 - t • A) ↔ ∀ i, 0 ≤ 1 - t * hA.eigenvalues i := by
  rw [← Matrix.IsHermitian.cfc_one_sub_smul hA t]
  let U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  have hU_unit : IsUnit U := by
    -- The unitary eigenbasis matrix is invertible with inverse `star U`.
    refine ⟨⟨U, star U, ?_, ?_⟩, rfl⟩ <;> simp [U]
  have hconj := (Matrix.IsUnit.posSemidef_star_right_conjugate_iff (U := U)
    (x := Matrix.diagonal ((fun x => 1 - t * x) ∘ hA.eigenvalues)) hU_unit)
  simpa [Matrix.IsHermitian.cfc, U, Unitary.conjStarAlgAut_apply, Matrix.posSemidef_diagonal_iff,
    Function.comp_apply, mul_assoc] using hconj

/-- A Hermitian affine perturbation `1 - t • A` is positive definite exactly when each shifted
eigenvalue `1 - t λᵢ` is positive. -/
lemma Matrix.IsHermitian.one_sub_smul_posDef_iff
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    Matrix.PosDef (1 - t • A) ↔ ∀ i, 0 < 1 - t * hA.eigenvalues i := by
  rw [← Matrix.IsHermitian.cfc_one_sub_smul hA t]
  let U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  have hU_unit : IsUnit U := by
    -- The unitary eigenbasis matrix is invertible with inverse `star U`.
    refine ⟨⟨U, star U, ?_, ?_⟩, rfl⟩ <;> simp [U]
  have hconj := (Matrix.IsUnit.posDef_star_right_conjugate_iff (U := U)
    (x := Matrix.diagonal ((fun x => 1 - t * x) ∘ hA.eigenvalues)) hU_unit)
  simpa [Matrix.IsHermitian.cfc, U, Unitary.conjStarAlgAut_apply, Matrix.posDef_diagonal_iff,
    Function.comp_apply, mul_assoc] using hconj

/-- The determinant of `1 - t • A` is the product of the shifted eigenvalues of the Hermitian
matrix `A`. -/
lemma Matrix.IsHermitian.det_one_sub_smul
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    Matrix.det (1 - t • A) = ∏ i, (1 - t * hA.eigenvalues i) := by
  rw [← Matrix.IsHermitian.cfc_one_sub_smul hA t]
  simp [Matrix.IsHermitian.cfc, -Unitary.conjStarAlgAut_apply]

/-- The spectral sum `-∑ log (1 - t λᵢ)` differentiates termwise wherever no factor vanishes. -/
lemma hasDerivAt_negLog_spectralSum
    {m : Type*} [Fintype m] (lambda : m → ℝ) {t : ℝ}
    (ht : ∀ i, 1 - t * lambda i ≠ 0) :
    HasDerivAt (∑ i, fun s => -Real.log (1 - s * lambda i))
      (∑ i, lambda i / (1 - t * lambda i)) t := by
  classical
  let A : m → ℝ → ℝ := fun i s => -Real.log (1 - s * lambda i)
  let A' : m → ℝ := fun i => lambda i / (1 - t * lambda i)
  have hsum : HasDerivAt (∑ i, A i) (∑ i, A' i) t := by
    refine HasDerivAt.sum (u := Finset.univ) (A := A) (A' := A') ?_
    intro i hi
    have hinner : HasDerivAt (fun s => 1 - s * lambda i) (-lambda i) t := by
      -- Differentiate the affine factor `1 - s λᵢ`.
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id t).mul_const (lambda i)).neg.const_add 1
    have hlog : HasDerivAt (fun s => Real.log (1 - s * lambda i))
        (-lambda i / (1 - t * lambda i)) t := by
      simpa using hinner.log (ht i)
    simpa [A, A', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlog.neg
  simpa [A, A'] using hsum

/-- The reciprocal spectral sum `∑ λᵢ / (1 - t λᵢ)` differentiates termwise wherever no factor
vanishes. -/
lemma hasDerivAt_reciprocal_spectralSum
    {m : Type*} [Fintype m] (lambda : m → ℝ) {t : ℝ}
    (ht : ∀ i, 1 - t * lambda i ≠ 0) :
    HasDerivAt (∑ i, fun s => lambda i / (1 - s * lambda i))
      (∑ i, (lambda i)^2 / (1 - t * lambda i)^2) t := by
  classical
  let A : m → ℝ → ℝ := fun i s => lambda i / (1 - s * lambda i)
  let A' : m → ℝ := fun i => (lambda i)^2 / (1 - t * lambda i)^2
  have hsum : HasDerivAt (∑ i, A i) (∑ i, A' i) t := by
    refine HasDerivAt.sum (u := Finset.univ) (A := A) (A' := A') ?_
    intro i hi
    have hinner : HasDerivAt (fun s => 1 - s * lambda i) (-lambda i) t := by
      -- Differentiate the affine denominator `1 - s λᵢ`.
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id t).mul_const (lambda i)).neg.const_add 1
    have hconst : HasDerivAt (fun _ : ℝ => lambda i) 0 t := by
      simpa using (hasDerivAt_const (x := t) (c := lambda i))
    have hquot : HasDerivAt (fun s => lambda i / (1 - s * lambda i))
        ((lambda i)^2 / (1 - t * lambda i)^2) t := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
        (HasDerivAt.div hconst hinner (ht i))
    simpa [A, A'] using hquot
  simpa [A, A'] using hsum

/-- The normalized direction matrix is symmetric because it is a symmetric congruence transform of
the symmetric direction matrix by the inverse square root of the analytic-center slack. -/
lemma LogDetAnalyticCenterProblem.normalizedDirection_isSymm
    {n m : ℕ} (p : LogDetAnalyticCenterProblem n m)
    (u : Fin n → ℝ) :
    let X := p.slack p.x_ac
    let T := CFC.sqrt X
    let S : Matrix (Fin m) (Fin m) ℝ := ∑ i, (u i) • p.A i
    let Δ : Matrix (Fin m) (Fin m) ℝ := T⁻¹ * S * T⁻¹
    Δ.IsSymm := by
  dsimp
  set X : Matrix (Fin m) (Fin m) ℝ := p.slack p.x_ac
  set T : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt X
  set S : Matrix (Fin m) (Fin m) ℝ := ∑ i, (u i) • p.A i
  have hT_symm : T.IsSymm := by
    -- The square root of a positive matrix is self-adjoint, hence symmetric over `ℝ`.
    have hself : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
    simpa [T, Matrix.IsSymm, Matrix.IsHermitian] using hself
  have hTinv_symm : T⁻¹.IsSymm := hT_symm.inv
  have hS_symm : S.IsSymm := by
    -- The directional matrix sum is symmetric termwise.
    simpa [S] using p.directionMatrix_isSymm u
  -- Transpose the normalized product and use symmetry of each factor.
  simp [Matrix.IsSymm, Matrix.transpose_mul, Matrix.mul_assoc, hTinv_symm.eq, hS_symm.eq]

/-- Feasibility of `x_ac + u` is equivalent to positive semidefiniteness of the normalized slack
`1 - Δ`, where `Δ` is the direction matrix conjugated by the inverse slack square root. -/
lemma LogDetAnalyticCenterProblem.feasible_add_iff_normalizedDirection_posSemidef
    {n m : ℕ} (p : LogDetAnalyticCenterProblem n m)
    (hx_ac : p.IsAnalyticCenter p.x_ac)
    (u : Fin n → ℝ) :
    let X := p.slack p.x_ac
    let T := CFC.sqrt X
    let S : Matrix (Fin m) (Fin m) ℝ := ∑ i, (u i) • p.A i
    let Δ : Matrix (Fin m) (Fin m) ℝ := T⁻¹ * S * T⁻¹
    p.feasible (p.x_ac + u) ↔ Matrix.PosSemidef (1 - Δ) := by
  dsimp
  set X : Matrix (Fin m) (Fin m) ℝ := p.slack p.x_ac
  set T : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt X
  set S : Matrix (Fin m) (Fin m) ℝ := ∑ i, (u i) • p.A i
  set Δ : Matrix (Fin m) (Fin m) ℝ := T⁻¹ * S * T⁻¹
  have hX_pos : Matrix.PosDef X := by
    -- The analytic center lies in the strict domain, so its slack is positive definite.
    simpa [X] using p.slack_analyticCenter_posDef hx_ac
  have hT_unit : IsUnit T := by
    -- The square root of an invertible positive matrix is invertible.
    simpa [T, X] using (CFC.isUnit_sqrt_iff X).2 hX_pos.isUnit
  letI := hT_unit.invertible
  have hT_symm : T.IsSymm := by
    -- The square root matrix is symmetric, so conjugation by `T` is a star-conjugation.
    have hself : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
    simpa [T, Matrix.IsSymm, Matrix.IsHermitian] using hself
  have hstarT : star T = T := by
    -- Over real matrices, self-adjointness is exactly `star T = T`.
    have hself : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
    simpa [isSelfAdjoint_iff, Matrix.IsHermitian] using hself
  have hconj :
      p.slack (p.x_ac + u) = T * (1 - Δ) * star T := by
    -- Specialize the normalized line identity to `t = 1` and rewrite the right factor as `star T`.
    calc
      p.slack (p.x_ac + u) = T * (1 - (1 : ℝ) • Δ) * T := by
        simpa [X, T, S, Δ] using p.normalizedSlack_line hx_ac u (1 : ℝ)
      _ = T * (1 - Δ) * star T := by
        simp [hstarT]
  -- Feasibility is invariant under conjugation by the invertible square root.
  rw [LogDetAnalyticCenterProblem.feasible, hconj]
  simpa using
    (Matrix.IsUnit.posSemidef_star_right_conjugate_iff (U := T) (x := 1 - Δ) hT_unit)

/-
Exercise 8.20 | 14 | thm

Let C = {x ∈ ℝⁿ | x₁A₁ + x₂A₂ + ··· + xₙAₙ ⪯ B}, where A₁, …, Aₙ, B ∈ Sᵐ, Sᵐ is the set of real
symmetric m × m matrices, and for X, Y ∈ Sᵐ, X ⪯ Y means that Y - X is positive semidefinite. Assume
that C has nonempty interior. Let x_ac be the minimizer of φ(x) = -log det(B - x₁A₁ - x₂A₂ - ··· -
xₙAₙ) over the domain {x ∈ ℝⁿ | B - x₁A₁ - x₂A₂ - ··· - xₙAₙ ≻ 0}, where X ≻ 0 means that X is
positive definite. Let H be the Hessian of φ at x_ac. Define E_inner = {x ∈ ℝⁿ | (x - x_ac)ᵀ H (x -
x_ac) ≤ q 1} and E_outer = {x ∈ ℝⁿ | (x - x_ac)ᵀ H (x - x_ac) ≤ q m(m - 1)}. Show that E_inner ⊆ C ⊆
E_outer.
-/
theorem analyticCenter_ellipsoid_bounds
    {n m : ℕ}
    (p : LogDetAnalyticCenterProblem n m)
    (hx_ac : p.IsAnalyticCenter p.x_ac)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH_hessian :
      H = fun i j =>
        (fderiv ℝ
          (fun y : Fin n → ℝ =>
            (fderiv ℝ p.objective y (Pi.single j (1 : ℝ)))) p.x_ac)
          (Pi.single i (1 : ℝ)))
    (hH_symm : H.IsSymm)
    (hH_pos : ∀ u : Fin n → ℝ, u ≠ 0 → 0 < dotProduct u (H.mulVec u)) :
    {x | dotProduct (x - p.x_ac) (H.mulVec (x - p.x_ac)) ≤ 1} ⊆ p.constraintSet ∧
      p.constraintSet ⊆
        {x | dotProduct (x - p.x_ac) (H.mulVec (x - p.x_ac)) ≤ (m * (m - 1) : ℝ)} := by
  classical
  have hobjective₂ : ContDiffAt ℝ 2 p.objective p.x_ac :=
    p.objective_contDiffAt_analyticCenter hx_ac
  have hspectral_data :
      ∀ u : Fin n → ℝ,
        ∃ lambda : Fin m → ℝ,
          (∑ i, lambda i = 0) ∧
          dotProduct u (H.mulVec u) = ∑ i, (lambda i)^2 ∧
          (p.feasible (p.x_ac + u) ↔ ∀ i, lambda i ≤ 1) := by
    intro u
    set X : Matrix (Fin m) (Fin m) ℝ := p.slack p.x_ac
    set T : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt X
    set S : Matrix (Fin m) (Fin m) ℝ := ∑ i, (u i) • p.A i
    set Δ : Matrix (Fin m) (Fin m) ℝ := T⁻¹ * S * T⁻¹
    have hX_pos : Matrix.PosDef X := by
      -- The analytic center lies in the strict domain, so its slack is positive definite.
      simpa [X] using p.slack_analyticCenter_posDef hx_ac
    have hT_unit : IsUnit T := by
      -- Invertibility passes from a positive-definite matrix to its square root.
      simpa [T, X] using (CFC.isUnit_sqrt_iff X).2 hX_pos.isUnit
    letI := hT_unit.invertible
    have hT_symm : T.IsSymm := by
      -- The square root of a positive matrix is symmetric over `ℝ`.
      have hself : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
      simpa [T, Matrix.IsSymm, Matrix.IsHermitian] using hself
    have hstarT : star T = T := by
      -- Over real matrices, self-adjointness is the same as `star T = T`.
      have hself : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
      simpa [isSelfAdjoint_iff, Matrix.IsHermitian] using hself
    have hΔ_symm : Δ.IsSymm := by
      -- The normalized direction matrix is symmetric by congruence.
      simpa [X, T, S, Δ] using p.normalizedDirection_isSymm (u := u)
    have hΔ_herm : Δ.IsHermitian := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hΔ_symm
    let lambda : Fin m → ℝ := hΔ_herm.eigenvalues
    have hdirection : p.x_ac + u - p.x_ac = u := by
      -- The line endpoint differs from the analytic center exactly by `u`.
      ext i
      simp [Pi.add_apply, Pi.sub_apply]
    have hlineMap_eq (t : ℝ) :
        AffineMap.lineMap p.x_ac (p.x_ac + u) t = p.x_ac + t • u := by
      -- The affine line through `x_ac` and `x_ac + u` is the translated ray `x_ac + t • u`.
      ext i
      simp [AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply]
      ring
    have hfeasible_iff :
        p.feasible (p.x_ac + u) ↔ ∀ i, lambda i ≤ 1 := by
      -- Feasibility along the translated line is equivalent to `1 - Δ` being positive semidefinite.
      rw [show p.feasible (p.x_ac + u) ↔ Matrix.PosSemidef (1 - Δ) by
        simpa [X, T, S, Δ] using
          p.feasible_add_iff_normalizedDirection_posSemidef hx_ac u]
      simpa [one_mul, lambda, sub_nonneg] using
        (Matrix.IsHermitian.one_sub_smul_posSemidef_iff hΔ_herm (1 : ℝ))
    let sumAbs : ℝ := ∑ i, |lambda i|
    let eps : ℝ := 1 / (sumAbs + 1)
    have hsumAbs_nonneg : 0 ≤ sumAbs := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact abs_nonneg (lambda i)
    have heps_pos : 0 < eps := by
      have hsumAbs_pos : 0 < sumAbs + 1 := by linarith
      simpa [eps] using one_div_pos.mpr hsumAbs_pos
    have hfactor_pos : ∀ {t : ℝ}, |t| < eps → ∀ i, 0 < 1 - t * lambda i := by
      intro t ht i
      have hLambdaAbsLe : |lambda i| ≤ sumAbs := by
        calc
          |lambda i| = ({i} : Finset (Fin m)).sum (fun j => |lambda j|) := by simp
          _ ≤ Finset.univ.sum (fun j => |lambda j|) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro j hj
              simp at hj
              simp [hj]
            · intro j hj hji
              exact abs_nonneg (lambda j)
          _ = sumAbs := by simp [sumAbs]
      have hsumAbs_pos : 0 < sumAbs + 1 := by linarith
      have hmul_lt : |t| * (sumAbs + 1) < 1 := by
        have htmp := mul_lt_mul_of_nonneg_right ht (show 0 ≤ sumAbs + 1 by linarith)
        simpa [eps, hsumAbs_pos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htmp
      have hts : |t| * sumAbs < 1 := by
        have hlt : |t| * sumAbs < |t| * (sumAbs + 1) := by
          refine mul_lt_mul_of_nonneg_left ?_ (abs_nonneg t)
          linarith
        linarith
      have habs_lt : |t * lambda i| < 1 := by
        calc
          |t * lambda i| = |t| * |lambda i| := by rw [abs_mul]
          _ ≤ |t| * sumAbs := mul_le_mul_of_nonneg_left hLambdaAbsLe (abs_nonneg t)
          _ < 1 := hts
      have hlt_one : t * lambda i < 1 := (abs_lt.mp habs_lt).2
      linarith
    have hstrict_eventually :
        ∀ᶠ t in 𝓝 (0 : ℝ), p.strictlyFeasible (p.x_ac + t • u) := by
      have hI : Set.Ioo (-eps) eps ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) heps_pos
      filter_upwards [hI] with t ht
      have ht_abs : |t| < eps := by
        exact abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
      have hnorm_pd : Matrix.PosDef (1 - t • Δ) := by
        refine (Matrix.IsHermitian.one_sub_smul_posDef_iff hΔ_herm t).2 ?_
        intro i
        exact hfactor_pos ht_abs i
      have hconj :
          p.slack (p.x_ac + t • u) = T * (1 - t • Δ) * star T := by
        -- The normalized slack identity expresses the line slack as an invertible congruence.
        calc
          p.slack (p.x_ac + t • u) = T * (1 - t • Δ) * T := by
            simpa [X, T, S, Δ] using p.normalizedSlack_line hx_ac u t
          _ = T * (1 - t • Δ) * star T := by
            simp [hstarT]
      have hslack_pd : Matrix.PosDef (p.slack (p.x_ac + t • u)) := by
        rw [hconj]
        exact (Matrix.IsUnit.posDef_star_right_conjugate_iff (U := T) (x := 1 - t • Δ) hT_unit).2
          hnorm_pd
      simpa [LogDetAnalyticCenterProblem.strictlyFeasible] using hslack_pd
    let lineObj : ℝ → ℝ := fun t => p.objective (p.x_ac + t • u)
    let g : ℝ → ℝ :=
      fun t => p.objective p.x_ac + (∑ i, fun s => -Real.log (1 - s * lambda i)) t
    let g' : ℝ → ℝ := ∑ i, fun s => lambda i / (1 - s * lambda i)
    let ambientDir : ℝ → ℝ := fun t => fderiv ℝ p.objective (p.x_ac + t • u) u
    have hline_formula :
        ∀ t : ℝ, p.strictlyFeasible (p.x_ac + t • u) → lineObj t = g t := by
      intro t ht
      have hconj :
          p.slack (p.x_ac + t • u) = T * (1 - t • Δ) * star T := by
        -- Rewrite the slack on the line as a star-conjugate of `1 - t • Δ`.
        calc
          p.slack (p.x_ac + t • u) = T * (1 - t • Δ) * T := by
            simpa [X, T, S, Δ] using p.normalizedSlack_line hx_ac u t
          _ = T * (1 - t • Δ) * star T := by
            simp [hstarT]
      have hnorm_pd : Matrix.PosDef (1 - t • Δ) := by
        have hslack_pd : Matrix.PosDef (p.slack (p.x_ac + t • u)) := by
          simpa [LogDetAnalyticCenterProblem.strictlyFeasible] using ht
        rw [hconj] at hslack_pd
        exact (Matrix.IsUnit.posDef_star_right_conjugate_iff (U := T) (x := 1 - t • Δ) hT_unit).1
          hslack_pd
      have hfactor_pos_t : ∀ i, 0 < 1 - t * lambda i := by
        simpa [lambda] using (Matrix.IsHermitian.one_sub_smul_posDef_iff hΔ_herm t).1 hnorm_pd
      have hdet_shift : Matrix.det (1 - t • Δ) = ∏ i, (1 - t * lambda i) := by
        simpa [lambda] using Matrix.IsHermitian.det_one_sub_smul hΔ_herm t
      have hTT : T * T = X := by
        simpa [T, X] using CFC.sqrt_mul_sqrt_self X
      have hdet_line :
          Matrix.det (p.slack (p.x_ac + t • u)) = Matrix.det X * ∏ i, (1 - t * lambda i) := by
        calc
          Matrix.det (p.slack (p.x_ac + t • u)) = Matrix.det (T * (1 - t • Δ) * T) := by
            simpa [X, T, S, Δ] using p.normalizedSlack_line hx_ac u t
          _ = Matrix.det T * Matrix.det (1 - t • Δ) * Matrix.det T := by
            simp [Matrix.det_mul, mul_assoc]
          _ = (Matrix.det T * Matrix.det T) * Matrix.det (1 - t • Δ) := by ring
          _ = Matrix.det X * Matrix.det (1 - t • Δ) := by
            rw [show Matrix.det T * Matrix.det T = Matrix.det X by
              calc
                Matrix.det T * Matrix.det T = Matrix.det (T * T) := by
                  symm
                  exact Matrix.det_mul T T
                _ = Matrix.det X := by rw [hTT]]
          _ = Matrix.det X * ∏ i, (1 - t * lambda i) := by rw [hdet_shift]
      have hX_det_ne : Matrix.det X ≠ 0 := hX_pos.det_pos.ne'
      have hprod_ne : ∏ i, (1 - t * lambda i) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro i hi
        exact (hfactor_pos_t i).ne'
      calc
        lineObj t = -Real.log (Matrix.det X * ∏ i, (1 - t * lambda i)) := by
          simp [lineObj, LogDetAnalyticCenterProblem.objective, hdet_line]
        _ = -(Real.log (Matrix.det X) + Real.log (∏ i, (1 - t * lambda i))) := by
          rw [Real.log_mul hX_det_ne hprod_ne]
        _ = -(Real.log (Matrix.det X) + ∑ i, Real.log (1 - t * lambda i)) := by
          rw [Real.log_prod]
          intro i hi
          exact (hfactor_pos_t i).ne'
        _ = g t := by
          simp [g, LogDetAnalyticCenterProblem.objective, X, Finset.sum_neg_distrib]
          ring
    have hline_eq : lineObj =ᶠ[𝓝 (0 : ℝ)] g := by
      filter_upwards [hstrict_eventually] with t ht
      exact hline_formula t ht
    have hline_le : (fun _ : ℝ => p.objective p.x_ac) ≤ᶠ[𝓝 (0 : ℝ)] lineObj := by
      filter_upwards [hstrict_eventually] with t ht
      exact hx_ac.2 (p.x_ac + t • u)
        (by simpa [LogDetAnalyticCenterProblem.domain, LogDetAnalyticCenterProblem.strictlyFeasible]
          using ht)
    have hline_min : IsLocalMin lineObj (0 : ℝ) := by
      exact hline_le.isLocalMin (by simp [lineObj]) isLocalMin_const
    have hg_deriv0 : HasDerivAt g (∑ i, lambda i) 0 := by
      simpa [g] using
        (hasDerivAt_negLog_spectralSum lambda (t := 0) (by simp)).const_add (p.objective p.x_ac)
    have hsum_zero : ∑ i, lambda i = 0 := by
      have hline_deriv0 : HasDerivAt lineObj (∑ i, lambda i) 0 :=
        hg_deriv0.congr_of_eventuallyEq hline_eq
      exact hline_min.hasDerivAt_eq_zero hline_deriv0
    have hg_deriv_eventually : deriv g =ᶠ[𝓝 (0 : ℝ)] g' := by
      have hI : Set.Ioo (-eps) eps ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) heps_pos
      filter_upwards [hI] with t ht
      have ht_abs : |t| < eps := by
        exact abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
      have hnonzero : ∀ i, 1 - t * lambda i ≠ 0 := by
        intro i
        exact (hfactor_pos ht_abs i).ne'
      have hderiv_t : HasDerivAt g (g' t) t := by
        simpa [g, g'] using
          (hasDerivAt_negLog_spectralSum lambda (t := t) hnonzero).const_add (p.objective p.x_ac)
      exact hderiv_t.deriv
    have hline_deriv_eventually : deriv lineObj =ᶠ[𝓝 (0 : ℝ)] g' :=
      hline_eq.deriv.trans hg_deriv_eventually
    have hambient_eq : ambientDir =ᶠ[𝓝 (0 : ℝ)] deriv lineObj := by
      filter_upwards [hstrict_eventually] with t ht
      have hcont_t : ContDiffAt ℝ 2 p.objective (p.x_ac + t • u) :=
        p.objective_contDiffAt_of_strictlyFeasible ht
      have hderiv_t : HasDerivAt lineObj (ambientDir t) t := by
        have h :=
          hasDerivAt_lineMap_apply_fderiv
            (g := p.objective) (x := p.x_ac) (y := p.x_ac + u) (t := t)
            hcont_t.differentiableAt
        simpa [lineObj, ambientDir, hlineMap_eq t, hdirection] using h
      exact hderiv_t.deriv.symm
    have hambient_eq_g' : ambientDir =ᶠ[𝓝 (0 : ℝ)] g' :=
      hambient_eq.trans hline_deriv_eventually
    have hambient_deriv :
        HasDerivAt ambientDir (iteratedFDeriv ℝ 2 p.objective p.x_ac ![u, u]) 0 := by
      have h :=
        hasDerivAt_lineMap_apply_iteratedFDeriv
          (g := p.objective) (x := p.x_ac) (y := p.x_ac + u) (t := 0) hobjective₂
      simpa [ambientDir, hlineMap_eq 0, hdirection] using h
    have hg'0 : HasDerivAt g' (∑ i, (lambda i)^2) 0 := by
      simpa [g'] using
        hasDerivAt_reciprocal_spectralSum lambda (t := 0) (by simp)
    have hambient_from_g' : HasDerivAt ambientDir (∑ i, (lambda i)^2) 0 :=
      hg'0.congr_of_eventuallyEq hambient_eq_g'
    have hiter_eq : iteratedFDeriv ℝ 2 p.objective p.x_ac ![u, u] = ∑ i, (lambda i)^2 := by
      exact hambient_deriv.unique hambient_from_g'
    have hquad : dotProduct u (H.mulVec u) = ∑ i, (lambda i)^2 := by
      calc
        dotProduct u (H.mulVec u) =
            iteratedFDeriv ℝ 2 p.objective p.x_ac ![u, u] := by
              simpa using
                quadraticForm_eq_iteratedFDeriv_at_analyticCenter p H hH_hessian hobjective₂ u
        _ = ∑ i, (lambda i)^2 := hiter_eq
    exact ⟨lambda, hsum_zero, hquad, hfeasible_iff⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    let u : Fin n → ℝ := x - p.x_ac
    have hx_eq : p.x_ac + u = x := by
      ext i
      simp [u, Pi.add_apply, Pi.sub_apply]
    obtain ⟨lambda, hsum_zero, hquad, hfeasible_iff⟩ := hspectral_data u
    have hsq_le : ∑ i, (lambda i)^2 ≤ 1 := by
      rw [← hquad]
      simpa [u] using hx
    have hle : ∀ i, lambda i ≤ 1 := by
      intro i
      by_contra hgt
      have hi_sq_le_sum : (lambda i)^2 ≤ ∑ j, (lambda j)^2 := by
        refine Finset.single_le_sum ?_ ?_
        · intro j
          exact sq_nonneg (lambda j)
        · simp
      have hi_sq_gt : 1 < (lambda i)^2 := by
        nlinarith
      linarith
    have hfeas : p.feasible (p.x_ac + u) := (hfeasible_iff).2 hle
    have hx_feas : p.feasible x := by
      simpa [hx_eq] using hfeas
    simpa [LogDetAnalyticCenterProblem.constraintSet] using hx_feas
  · intro x hx
    let u : Fin n → ℝ := x - p.x_ac
    have hx_eq : p.x_ac + u = x := by
      ext i
      simp [u, Pi.add_apply, Pi.sub_apply]
    have hx_feas : p.feasible (p.x_ac + u) := by
      simpa [hx_eq, LogDetAnalyticCenterProblem.constraintSet] using hx
    obtain ⟨lambda, hsum_zero, hquad, hfeasible_iff⟩ := hspectral_data u
    have hle : ∀ i, lambda i ≤ 1 := (hfeasible_iff).1 hx_feas
    have hsq_le : ∑ i, (lambda i)^2 ≤ (m : ℝ) * (m - 1) :=
      eigenvalue_square_bound_of_le_one_and_zero_sum lambda hle hsum_zero
    rw [← hquad]
    simpa [u]

end «problem-32»
