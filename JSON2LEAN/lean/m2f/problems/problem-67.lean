import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-67»

-- Exercise_3_49__d_

/- [BLOCK Exercise 3.49-(d) | 40 | defn]
A function f : C → ℝ_{++} on a convex set C is log-concave if log f is concave on C; equivalently,
for all x,y ∈ C and θ ∈ [0,1],
f(θ x+(1-θ)y) ≥ f(x)^θ f(y)^{1-θ}.
-/
def LogConcaveOn (C : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ C ∧
    Set.MapsTo f C (Set.Ioi 0) ∧
      ∀ ⦃x y : ℝ⦄, x ∈ C → y ∈ C →
        ∀ ⦃θ : ℝ⦄, θ ∈ Set.Icc (0 : ℝ) 1 →
          f (θ * x + (1 - θ) * y) ≥ Real.rpow (f x) θ * Real.rpow (f y) (1 - θ)

/-- The cone of positive definite matrices is convex. -/
lemma convex_setOf_posDef
    (n : Type*) [Fintype n] [DecidableEq n] :
    Convex ℝ {X : Matrix n n ℝ | X.PosDef} := by
  intro X hX Y hY a b ha hb hab
  rcases eq_or_lt_of_le ha with rfl | ha'
  · -- If the first weight vanishes, the convex combination is just `Y`.
    have hb1 : b = 1 := by linarith
    simpa [hb1]
  rcases eq_or_lt_of_le hb with rfl | hb'
  · -- If the second weight vanishes, the convex combination is just `X`.
    have ha1 : a = 1 := by linarith
    simpa [ha1, add_comm]
  -- In the genuine convex-combination case, positivity is preserved by positive scaling and addition.
  exact (hX.smul ha').add (hY.smul hb')

/-- Every point on the closed segment between two positive definite matrices is positive definite. -/
lemma segment_posDef_of_mem_Icc
    {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℝ}
    (hX : X.PosDef) (hY : Y.PosDef) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (t • X + (1 - t) • Y).PosDef := by
  rcases ht with ⟨ht0, ht1⟩
  -- Repackage the segment point as a convex combination with nonnegative coefficients.
  have hsum : t + (1 - t) = 1 := by ring
  -- The convexity lemma from above closes the goal once the coefficients are identified.
  exact convex_setOf_posDef n hX hY ht0 (sub_nonneg.mpr ht1) hsum

/-- On a positive definite matrix, the target function can be rewritten in terms of eigenvalues. -/
lemma log_det_sub_log_trace_eq_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℝ} (hX : X.PosDef) :
    Real.log (Matrix.det X) - Real.log (Matrix.trace X) =
      (∑ i, Real.log (hX.isHermitian.eigenvalues i)) -
        Real.log (∑ i, hX.isHermitian.eigenvalues i) := by
  -- Rewrite determinant and trace through the Hermitian spectral theorem for `X`.
  rw [hX.isHermitian.det_eq_prod_eigenvalues, hX.isHermitian.trace_eq_sum_eigenvalues]
  -- The determinant part becomes a sum of logarithms because each eigenvalue is positive.
  rw [Real.log_prod]
  · simp
  · intro i _
    exact (hX.eigenvalues_pos i).ne'

/-- A positive definite endpoint provides an invertible factor that moves the other endpoint to a
relative positive definite matrix by conjugation. -/
lemma relative_posDef_exists_conj_factor
    {n : Type*} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℝ}
    (hX : X.PosDef) (hY : Y.PosDef) :
    ∃ B : Matrix n n ℝ, IsUnit B ∧ Y = star B * B ∧ (B⁻¹ * X * star B⁻¹).PosDef := by
  -- Route correction: first factor the reference endpoint `Y`, then conjugate `X` by that factor.
  obtain ⟨B, hB_unit, hY_fac⟩ := (Matrix.posDef_iff_eq_conjTranspose_mul_self (A := Y)).1 hY
  refine ⟨B, hB_unit, ?_, ?_⟩
  · -- Over `ℝ`, conjugate transpose is just `star`, so the factorization matches the planned form.
    simpa [Matrix.star_eq_conjTranspose] using hY_fac
  · -- Positivity is stable under invertible right-star conjugation, exactly as needed later.
    rcases hB_unit with ⟨U, rfl⟩
    have hUi : IsUnit (((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ)) := Units.isUnit U⁻¹
    simpa using (_root_.Matrix.IsUnit.posDef_star_right_conjugate_iff
      (U := (((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ))) (x := X) hUi).2 hX

/-- Multiplying on the left by a diagonal matrix reads off the diagonal entries in the trace. -/
lemma trace_diagonal_mul
    {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (M : Matrix n n ℝ) :
    Matrix.trace (Matrix.diagonal d * M) = ∑ i, d i * M i i := by
  -- Expand the trace and use that a diagonal matrix kills all off-diagonal contributions.
  rw [Matrix.trace_mul_comm]
  simpa [mul_comm] using
    (by simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal] :
      Matrix.trace (M * Matrix.diagonal d) = ∑ i, M i i * d i)

/-- An affine combination of a diagonal matrix with the identity is diagonal again, with the
expected affine combination on the diagonal entries. -/
lemma diagonal_affine_combination
    {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (t : ℝ) :
    t • Matrix.diagonal d + (1 - t) • (1 : Matrix n n ℝ) =
      Matrix.diagonal (fun i => t * d i + (1 - t)) := by
  -- Compare the two matrices entrywise, separating diagonal and off-diagonal entries.
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [sub_eq_add_neg]
  · simp [hij, sub_eq_add_neg]

/-- After unitary diagonalization, pairing with the trace only keeps the diagonal of the conjugated
weight matrix. -/
lemma trace_unitary_diagonal_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℝ) (d : n → ℝ) (S : Matrix n n ℝ) :
    Matrix.trace (((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U) (Matrix.diagonal d)) * S) =
      ∑ i, d i * (star (U : Matrix n n ℝ) * S * (U : Matrix n n ℝ)) i i := by
  -- Rewrite the unitary conjugation explicitly so the diagonal factor can be moved to the left.
  calc
    Matrix.trace (((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U) (Matrix.diagonal d)) * S)
        = Matrix.trace (((U : Matrix n n ℝ) * Matrix.diagonal d * star (U : Matrix n n ℝ)) * S) := by
            simp [Unitary.conjStarAlgAut_apply]
    _ = Matrix.trace ((U : Matrix n n ℝ) * Matrix.diagonal d * (star (U : Matrix n n ℝ) * S)) := by
          simp [Matrix.mul_assoc]
    _ = Matrix.trace ((star (U : Matrix n n ℝ) * S) * (U : Matrix n n ℝ) * Matrix.diagonal d) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (Matrix.diagonal d * (star (U : Matrix n n ℝ) * S * (U : Matrix n n ℝ))) := by
          rw [Matrix.trace_mul_comm]
          simp [Matrix.mul_assoc]
    _ = ∑ i, d i * (star (U : Matrix n n ℝ) * S * (U : Matrix n n ℝ)) i i := by
          simpa using trace_diagonal_mul d (star (U : Matrix n n ℝ) * S * (U : Matrix n n ℝ))

/-- The scalar curvature term from the weighted Jensen reduction is always dominated by the
diagonal negative contribution. -/
lemma weighted_affine_curvature_nonpos
    {n : Type*} [Fintype n] [Nonempty n]
    (δ z w : n → ℝ) (hz : ∀ i, 0 < z i) (hw : ∀ i, 0 < w i) :
    ((∑ i, w i * δ i) ^ 2) / (∑ i, w i * z i) ^ 2 ≤ ∑ i, (δ i) ^ 2 / (z i) ^ 2 := by
  have hsumz_pos : 0 < ∑ i, w i * z i := by
    -- Every weight-length product is positive, so the whole denominator is positive.
    exact Finset.sum_pos (fun i _ => mul_pos (hw i) (hz i)) Finset.univ_nonempty
  have hcs :
      (∑ i, w i * δ i) ^ 2 / ∑ i, w i * z i ≤
        ∑ i, (w i * δ i) ^ 2 / (w i * z i) := by
    -- First apply Titu's lemma / Cauchy-Schwarz with `f i = w i * δ i` and `g i = w i * z i`.
    simpa using
      (Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun i => w i * δ i)
        (fun i _ => mul_pos (hw i) (hz i)))
  have hcs' :
      ((∑ i, w i * δ i) ^ 2) / (∑ i, w i * z i) ^ 2 ≤
        (∑ i, (w i * δ i) ^ 2 / (w i * z i)) / (∑ i, w i * z i) := by
    -- Divide the previous inequality by the positive denominator one more time.
    have hcs'' := div_le_div_of_nonneg_right hcs hsumz_pos.le
    simpa [pow_two, div_div] using hcs''
  have hsumbound :
      ∑ i, (w i * δ i) ^ 2 / (w i * z i) ≤
        (∑ i, w i * z i) * ∑ i, (δ i) ^ 2 / (z i) ^ 2 := by
    -- Each summand is bounded using the trivial estimate `w i * z i ≤ ∑ j, w j * z j`.
    calc
      ∑ i, (w i * δ i) ^ 2 / (w i * z i)
          = ∑ i, (w i * z i) * ((δ i) ^ 2 / (z i) ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              field_simp [(hz i).ne', (hw i).ne']
      _ ≤ ∑ i, (∑ j, w j * z j) * ((δ i) ^ 2 / (z i) ^ 2) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hle : w i * z i ≤ ∑ j, w j * z j := by
              exact Finset.single_le_sum
                (fun j _ => mul_nonneg (hw j).le (hz j).le)
                (Finset.mem_univ i)
            have hnonneg : 0 ≤ (δ i) ^ 2 / (z i) ^ 2 := by positivity
            nlinarith
      _ = (∑ i, w i * z i) * ∑ i, (δ i) ^ 2 / (z i) ^ 2 := by
            rw [← Finset.mul_sum]
  have hfinal :
      (∑ i, (w i * δ i) ^ 2 / (w i * z i)) / (∑ i, w i * z i) ≤
        ∑ i, (δ i) ^ 2 / (z i) ^ 2 := by
    -- Cancel the positive denominator from the upper bound.
    exact (div_le_iff₀ hsumz_pos).2 <| by simpa [mul_comm, mul_left_comm, mul_assoc] using hsumbound
  exact hcs'.trans hfinal

/-- Normalizing a positive-definite segment against one endpoint rewrites the target function as a
scalar log-ratio in the relative eigenvalues. -/
lemma relative_segment_log_rewrite
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {X Y : Matrix n n ℝ} (hX : X.PosDef) (hY : Y.PosDef) :
    ∃ eig w : n → ℝ, (∀ i, 0 < eig i) ∧ (∀ i, 0 < w i) ∧
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
        Real.log (Matrix.det (t • X + (1 - t) • Y)) -
            Real.log (Matrix.trace (t • X + (1 - t) • Y)) =
          Real.log (Matrix.det Y) +
            (∑ i, Real.log (t * eig i + (1 - t))) -
              Real.log (∑ i, w i * (t * eig i + (1 - t))) := by
  -- TODO: factor `Y = star B * B`, set the relative matrix `A := star B⁻¹ * X * B⁻¹`,
  -- diagonalize `A`, and then rewrite determinant and trace using the helpers above.
  sorry

/-- The scalar log-ratio coming from the relative eigenvalue reduction is concave on `[0,1]`. -/
lemma weighted_log_ratio_concaveOn_Icc
    {n : Type*} [Fintype n] [Nonempty n]
    (eig w : n → ℝ) (heig : ∀ i, 0 < eig i) (hw : ∀ i, 0 < w i) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t => (∑ i, Real.log (t * eig i + (1 - t))) -
        Real.log (∑ i, w i * (t * eig i + (1 - t)))) := by
  -- Route correction: the remaining work is now purely scalar; the matrix normalization is done.
  -- TODO: compute the second derivative on `Set.Ioo 0 1` and apply
  -- `concaveOn_of_hasDerivWithinAt2_nonpos`, using `weighted_affine_curvature_nonpos` with
  -- `δ i = eig i - 1` and `z i = t * eig i + (1 - t)`.
  sorry

/- [BLOCK Exercise 3.49-(d) | 41 | thm]
Let S_{++}^n denote the set of all n× n real symmetric positive definite matrices. For X∈ S_{++}^n,
define f(X)=det X{tr X}. Prove that f is log-concave on S_{++}^n; equivalently, prove that the
function X mapsto log det X-log(tr X) is concave on S_{++}^n.
-/
theorem det_div_trace_logConcaveOn_posDef
    (n : Type*) [Fintype n] [DecidableEq n] :
    ConcaveOn ℝ
      {X : Matrix n n ℝ | X.PosDef}
      (fun X : Matrix n n ℝ => Real.log (Matrix.det X) - Real.log (Matrix.trace X)) := by
  classical
  by_cases hn : IsEmpty n
  · letI : IsEmpty n := hn
    -- When the index type is empty, every matrix is equal, so the function is constant on its domain.
    refine ⟨?_, ?_⟩
    · intro X hX Y hY a b ha hb hab
      have hcombo : a • X + b • Y = X := Subsingleton.elim _ _
      simpa [hcombo] using hX
    · intro X hX Y hY a b ha hb hab
      have hXY : Y = X := Subsingleton.elim _ _
      simp [hXY]
  · letI : Nonempty n := not_isEmpty_iff.mp hn
    have hconv : Convex ℝ {X : Matrix n n ℝ | X.PosDef} := convex_setOf_posDef n
    refine ⟨hconv, ?_⟩
    intro X hX Y hY a b ha hb hab
    -- Route correction: instead of trying to subtract two separate concave matrix-valued pieces,
    -- normalize the segment against `Y` and reduce everything to a scalar concavity statement.
    obtain ⟨eig, w, heig, hw, hrewrite⟩ := relative_segment_log_rewrite hX hY
    let φ : ℝ → ℝ := fun t =>
      (∑ i, Real.log (t * eig i + (1 - t))) -
        Real.log (∑ i, w i * (t * eig i + (1 - t)))
    have hφconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) φ :=
      weighted_log_ratio_concaveOn_Icc eig w heig hw
    have ha_mem : a ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact ha
      · linarith
    have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    have hφineq := hφconc.2 h1_mem h0_mem ha hb (by simpa [hab])
    have hAtA :
        Real.log (Matrix.det (a • X + (1 - a) • Y)) -
            Real.log (Matrix.trace (a • X + (1 - a) • Y)) =
          Real.log (Matrix.det Y) + φ a := by
      -- This is the scalarized form of the point on the segment at parameter `a`.
      simpa [φ] using hrewrite ha_mem
    have hAt1 :
        Real.log (Matrix.det X) - Real.log (Matrix.trace X) =
          Real.log (Matrix.det Y) + φ 1 := by
      -- At `t = 1`, the segment returns the left endpoint `X`.
      have h := hrewrite h1_mem
      simpa [φ] using h
    have hAt0 :
        Real.log (Matrix.det Y) - Real.log (Matrix.trace Y) =
          Real.log (Matrix.det Y) + φ 0 := by
      -- At `t = 0`, the segment returns the right endpoint `Y`.
      have h := hrewrite h0_mem
      simpa [φ] using h
    -- Apply scalar concavity at `1` and `0`, then translate back to the matrix expressions.
    calc
      Real.log (Matrix.det (a • X + b • Y)) - Real.log (Matrix.trace (a • X + b • Y))
          = Real.log (Matrix.det (a • X + (1 - a) • Y)) -
              Real.log (Matrix.trace (a • X + (1 - a) • Y)) := by
                congr 1
                · simp [hab]
                · simp [hab]
      _ = Real.log (Matrix.det Y) + φ a := hAtA
      _ ≥ Real.log (Matrix.det Y) + (a * φ 1 + b * φ 0) := by
            linarith
      _ = a * (Real.log (Matrix.det Y) + φ 1) + b * (Real.log (Matrix.det Y) + φ 0) := by
            ring_nf
            linarith
      _ = a * (Real.log (Matrix.det X) - Real.log (Matrix.trace X)) +
            b * (Real.log (Matrix.det Y) - Real.log (Matrix.trace Y)) := by
            rw [← hAt1, ← hAt0]
      _ = a • (Real.log (Matrix.det X) - Real.log (Matrix.trace X)) +
            b • (Real.log (Matrix.det Y) - Real.log (Matrix.trace Y)) := by
            simp [smul_eq_mul]

end «problem-67»
