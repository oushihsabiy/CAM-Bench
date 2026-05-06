import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-17»
/-
For a twice differentiable function f: ℝ^n → ℝ, the Hessian at x is the matrix ∇^2 f(x) ∈ S^n with
entries (∇^2 f(x))_ij = ∂^2 f / (∂ xᵢ ∂ xⱼ)(x).
-/
def Hessian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (_hC2 : ContDiffAt ℝ 2 f x) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
      (Pi.single i (1 : ℝ))

/-- The bordered Hessian built from a symmetric Hessian matrix is itself symmetric. -/
lemma borderedHessian_isSymm
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hC2 : ContDiffAt ℝ 2 f x)
    (hHess_symm : (Hessian f x hC2).IsSymm) :
    let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j =>
        if hi : i.1 < n then
          if hj : j.1 < n then
            (Hessian f x hC2) ⟨i.1, hi⟩ ⟨j.1, hj⟩
          else
            deriv (fun t : ℝ => f (Function.update x ⟨i.1, hi⟩ t)) (x ⟨i.1, hi⟩)
        else if hj : j.1 < n then
          deriv (fun t : ℝ => f (Function.update x ⟨j.1, hj⟩ t)) (x ⟨j.1, hj⟩)
        else
          0
    H.IsSymm := by
  -- Check the four index-position cases; only the top-left block uses Hessian symmetry.
  intro H
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  by_cases hi : i.1 < n
  · by_cases hj : j.1 < n
    · simpa [H, hi, hj] using hHess_symm.apply ⟨i.1, hi⟩ ⟨j.1, hj⟩
    · simp [H, hi, hj]
  · by_cases hj : j.1 < n
    · simp [H, hi, hj]
    · simp [H, hi, hj]

/-- If every coordinate gradient vanishes, the tangent condition is exactly positive
semidefiniteness of the Hessian. -/
lemma tangent_nonneg_iff_posSemidef_when_gradient_zero
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hC2 : ContDiffAt ℝ 2 f x)
    (hHess_symm : (Hessian f x hC2).IsSymm)
    (hgrad :
      ∀ i, deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) :
    (∀ y : Fin n → ℝ,
      (∑ i, y i * deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) →
        0 ≤ ∑ i, ∑ j, y i * (Hessian f x hC2) i j * y j) ↔
      Matrix.PosSemidef (Hessian f x hC2) := by
  constructor
  · intro htangent
    -- With zero gradient the tangent constraint is vacuous, so every quadratic form value is
    -- nonnegative.
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · simpa using hHess_symm
    · intro y
      have hy_constraint :
          ∑ i, y i * deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0 := by
        simp [hgrad]
      have hy_nonneg := htangent y hy_constraint
      simpa [Matrix.dotProduct_mulVec, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
        using hy_nonneg
  · intro hPSD y _hy
    -- Positive semidefiniteness already gives the required quadratic-form nonnegativity.
    have hy_nonneg : 0 ≤ star y ⬝ᵥ ((Hessian f x hC2) *ᵥ y) :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hPSD).2 y
    simpa [Matrix.dotProduct_mulVec, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      using hy_nonneg

/-- Rewriting the bordered arrow matrix with `Fin.lastCases` removes the index arithmetic from the
quadratic-form computations. -/
lemma bordered_matrix_eq_lastCases
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) :
    (fun i j : Fin (n + 1) =>
      if hi : i.1 < n then
        if hj : j.1 < n then
          A ⟨i.1, hi⟩ ⟨j.1, hj⟩
        else
          g ⟨i.1, hi⟩
      else if hj : j.1 < n then
        g ⟨j.1, hj⟩
      else
        0) =
    (fun i j : Fin (n + 1) =>
      Fin.lastCases (motive := fun _ => Fin (n + 1) → ℝ)
        (Fin.lastCases 0 (fun j => g j))
        (fun i => Fin.lastCases (g i) (fun j => A i j)) i j) := by
  -- Check the four positions: top-left Hessian block, the two gradient blocks, and the zero corner.
  ext i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp

/-- The bordered arrow quadratic form splits as the Hessian quadratic form plus the last-coordinate
cross term. -/
lemma bordered_matrix_quadratic_form
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) (v : Fin (n + 1) → ℝ) :
    let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j =>
        if hi : i.1 < n then
          if hj : j.1 < n then
            A ⟨i.1, hi⟩ ⟨j.1, hj⟩
          else
            g ⟨i.1, hi⟩
        else if hj : j.1 < n then
          g ⟨j.1, hj⟩
        else
          0
    (∑ i, ∑ j, v i * H i j * v j) =
      (∑ i, ∑ j, v i.castSucc * A i j * v j.castSucc) +
        2 * v (Fin.last n) * ∑ i, v i.castSucc * g i := by
  -- Route correction: switch from the raw `if` matrix to the equivalent `Fin.lastCases` form so
  -- the `Fin.sum_univ_castSucc` decomposition becomes a pure ring calculation.
  intro H
  have hcalc :
      (∑ i, ∑ j,
        v i *
          (fun i j : Fin (n + 1) =>
            Fin.lastCases (motive := fun _ => Fin (n + 1) → ℝ)
              (Fin.lastCases 0 (fun j => g j))
              (fun i => Fin.lastCases (g i) (fun j => A i j)) i j) i j *
          v j) =
        (∑ i, ∑ j, v i.castSucc * A i j * v j.castSucc) +
          2 * v (Fin.last n) * ∑ i, v i.castSucc * g i := by
    simp only [Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [Finset.sum_add_distrib]
    have hcross :
        ∑ x, v x.castSucc * g x * v (Fin.last n) =
          v (Fin.last n) * ∑ x, v x.castSucc * g x := by
      -- Pull the last coordinate out of the sum; the remaining term is the gradient pairing.
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x hx
      ring
    have hcross' :
        ∑ x, v (Fin.last n) * g x * v x.castSucc =
          v (Fin.last n) * ∑ x, v x.castSucc * g x := by
      -- The symmetric gradient block contributes the same cross term.
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x hx
      ring
    rw [hcross, hcross']
    ring
  simpa [H, bordered_matrix_eq_lastCases] using hcalc

/-- A nonzero gradient coordinate produces a vector normalized by the gradient pairing. -/
lemma exists_normalized_gradient_vector
    {n : ℕ} (g : Fin n → ℝ) {i0 : Fin n} (hi0 : g i0 ≠ 0) :
    ∃ u : Fin n → ℝ, ∑ i, u i * g i = 1 := by
  -- Put all the mass on the nonzero coordinate and divide by that coordinate.
  refine ⟨fun i => if i = i0 then 1 / g i0 else 0, ?_⟩
  simp [hi0]

/-- The normalized gradient vector gives an explicit negative value of the bordered quadratic form. -/
lemma bordered_matrix_negative_witness
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) (u : Fin n → ℝ)
    (hu : ∑ i, u i * g i = 1) :
    let q : ℝ := ∑ i, ∑ j, u i * A i j * u j
    let v : Fin (n + 1) → ℝ := Fin.lastCases (-(q + 1) / 2) (fun i => u i)
    let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j =>
        if hi : i.1 < n then
          if hj : j.1 < n then
            A ⟨i.1, hi⟩ ⟨j.1, hj⟩
          else
            g ⟨i.1, hi⟩
        else if hj : j.1 < n then
          g ⟨j.1, hj⟩
        else
          0
    (∑ i, ∑ j, v i * H i j * v j) = -1 := by
  -- Plug the normalized vector into the quadratic-form identity and choose the last coordinate so
  -- that the cross term cancels all but `-1`.
  intro q v H
  rw [bordered_matrix_quadratic_form]
  simp [v, q, hu]
  ring

/-- For a symmetric real matrix, swapping the two arguments of the associated bilinear form does
not change its value. -/
lemma symmetric_dotProduct_mulVec_swap
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (x u : Fin n → ℝ) :
    x ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ x) := by
  -- Rewrite both bilinear forms as double sums and swap the indices using symmetry.
  have hcross :
      ∑ i, ∑ j, u i * A i j * x j =
        ∑ i, ∑ j, x i * A i j * u j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hA.apply j i]
    ring
  simpa [Matrix.dotProduct_mulVec, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using
    hcross.symm

/-- Expanding a symmetric quadratic form along a single direction produces the expected bilinear
cross term. -/
lemma symmetric_quadratic_form_add_smul
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (x u : Fin n → ℝ) (s : ℝ) :
    (x + s • u) ⬝ᵥ (A *ᵥ (x + s • u)) =
      x ⬝ᵥ (A *ᵥ x) + 2 * s * (x ⬝ᵥ (A *ᵥ u)) + s ^ 2 * (u ⬝ᵥ (A *ᵥ u)) := by
  -- Expand linearly, then merge the two cross terms by symmetry.
  have hsym := symmetric_dotProduct_mulVec_swap A hA x u
  simp [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, mul_add]
  rw [hsym]
  ring_nf

/-- Completing the square for the bordered arrow matrix isolates the tangent quadratic part. -/
lemma bordered_matrix_complete_square
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (g u z : Fin n → ℝ)
    (hu : ∑ i, u i * g i = 1) (hz : ∑ i, z i * g i = 0) (s t : ℝ) :
    let q : ℝ := u ⬝ᵥ (A *ᵥ u)
    let w : Fin (n + 1) → ℝ :=
      Fin.lastCases (t - z ⬝ᵥ (A *ᵥ u) - (q / 2) * s) (fun i => z i + s * u i)
    let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j =>
        if hi : i.1 < n then
          if hj : j.1 < n then
            A ⟨i.1, hi⟩ ⟨j.1, hj⟩
          else
            g ⟨i.1, hi⟩
        else if hj : j.1 < n then
          g ⟨j.1, hj⟩
        else
          0
    (∑ i, ∑ j, w i * H i j * w j) = z ⬝ᵥ (A *ᵥ z) + 2 * s * t := by
  -- Route correction: package the bordered-Hessian algebra into one square-completion identity so
  -- the remaining obstruction is purely spectral.
  intro q w H
  rw [bordered_matrix_quadratic_form]
  have hgrad_pairing :
      ∑ i, (z i + s * u i) * g i = s := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, hz]
    have hs :
        ∑ i, s * u i * g i = s * ∑ i, u i * g i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    rw [hs, hu]
    ring
  have hquad :
      (fun i => z i + s * u i) ⬝ᵥ (A *ᵥ (fun i => z i + s * u i)) =
        z ⬝ᵥ (A *ᵥ z) + 2 * s * (z ⬝ᵥ (A *ᵥ u)) + s ^ 2 * q := by
    change (z + s • u) ⬝ᵥ (A *ᵥ (z + s • u)) =
      z ⬝ᵥ (A *ᵥ z) + 2 * s * (z ⬝ᵥ (A *ᵥ u)) + s ^ 2 * q
    simpa [q] using symmetric_quadratic_form_add_smul A hA z u s
  have hlast :
      2 * (t - z ⬝ᵥ (A *ᵥ u) - (q / 2) * s) * s =
        2 * s * t - 2 * s * (z ⬝ᵥ (A *ᵥ u)) - s ^ 2 * q := by
    ring
  have hsum_form :
      (∑ i, ∑ j, (z i + s * u i) * A i j * (z j + s * u j)) =
        z ⬝ᵥ (A *ᵥ z) + 2 * s * (z ⬝ᵥ (A *ᵥ u)) + s ^ 2 * q := by
    simpa [Matrix.dotProduct_mulVec, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using
      hquad
  simp_rw [w, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [hsum_form, hgrad_pairing, hlast]
  ring

/-- The gradient pairing on the top block of a bordered vector is linear. -/
lemma bordered_tangent_functional_add_smul
    {n : ℕ} (g : Fin n → ℝ) (r s : ℝ) (a b : Fin (n + 1) → ℝ) :
    (∑ i, (r • a + s • b) i.castSucc * g i) =
      r * ∑ i, a i.castSucc * g i + s * ∑ i, b i.castSucc * g i := by
  -- Expand the sum coordinatewise and pull the scalar coefficients outside.
  have ha :
      ∑ x, r * a x.castSucc * g x = r * ∑ i, a i.castSucc * g i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  have hb :
      ∑ x, s * b x.castSucc * g x = s * ∑ i, b i.castSucc * g i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  calc
    ∑ i, (r • a + s • b) i.castSucc * g i
        = ∑ i, (r * (a i.castSucc * g i) + s * (b i.castSucc * g i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            ring
    _ = ∑ i, r * (a i.castSucc * g i) + ∑ i, s * (b i.castSucc * g i) := by
          rw [Finset.sum_add_distrib]
    _ = r * ∑ i, a i.castSucc * g i + s * ∑ i, b i.castSucc * g i := by
          simpa [mul_assoc] using congrArg₂ (fun x y => x + y) ha hb

/-- Evaluating a Hermitian quadratic form on one of its orthonormal eigenvectors returns the
corresponding eigenvalue. -/
lemma hermitian_quadratic_form_eigenvector
    {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) (hA : A.IsHermitian) (i : m) :
    star ⇑(hA.eigenvectorBasis i) ⬝ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis i)) = hA.eigenvalues i := by
  -- The eigenvector relation collapses the quadratic form to the eigenvalue times the norm square.
  simpa using (hA.eigenvalues_eq i).symm

/-- A real Hermitian quadratic form is the sum of its eigenvalues weighted by the squared
coordinates in an orthonormal eigenbasis. -/
lemma hermitian_quadratic_form_eq_sum_eigenvalues
    {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) (hA : A.IsHermitian) (w : m → ℝ) :
    star w ⬝ᵥ (A *ᵥ w) =
      ∑ i, hA.eigenvalues i * (inner ℝ (hA.eigenvectorBasis i) (WithLp.toLp 2 w)) ^ 2 := by
  let v : EuclideanSpace ℝ m := WithLp.toLp 2 w
  let T : EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ m := Matrix.toEuclideanLin A
  have hTsymm : T.IsSymmetric := by
    simpa [T] using (Matrix.isHermitian_iff_isSymmetric (A := A)).mp hA
  have hinner :
      star w ⬝ᵥ (A *ᵥ w) = inner ℝ (T v) v := by
    simpa [T, v] using
      (EuclideanSpace.inner_toLp_toLp (x := A *ᵥ w) (y := w)).symm
  calc
    star w ⬝ᵥ (A *ᵥ w) = inner ℝ (T v) v := hinner
    _ = ∑ i, inner ℝ (T v) (hA.eigenvectorBasis i) *
          inner ℝ (hA.eigenvectorBasis i) v := by
          rw [← (hA.eigenvectorBasis).sum_inner_mul_inner (T v) v]
    _ = ∑ i, hA.eigenvalues i * (inner ℝ (hA.eigenvectorBasis i) v) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hbasis :
              T (hA.eigenvectorBasis i) = (hA.eigenvalues i) • hA.eigenvectorBasis i := by
            -- The Hermitian operator acts diagonally on its orthonormal eigenbasis.
            simpa [T] using congrArg (WithLp.toLp 2) (hA.mulVec_eigenvectorBasis i)
          have hcoord :
              inner ℝ (T v) (hA.eigenvectorBasis i) =
                hA.eigenvalues i * inner ℝ (hA.eigenvectorBasis i) v := by
            -- Symmetry moves `T` to the right, where the eigenvector relation applies.
            calc
              inner ℝ (T v) (hA.eigenvectorBasis i) =
                  inner ℝ v (T (hA.eigenvectorBasis i)) := by
                    simpa [T] using hTsymm v (hA.eigenvectorBasis i)
              _ = inner ℝ v ((hA.eigenvalues i) • hA.eigenvectorBasis i) := by
                    rw [hbasis]
              _ = hA.eigenvalues i * inner ℝ v (hA.eigenvectorBasis i) := by
                    rw [inner_smul_right]
              _ = hA.eigenvalues i * inner ℝ (hA.eigenvectorBasis i) v := by
                    rw [real_inner_comm]
          rw [hcoord]
          ring

/-- If all eigenvalues away from one distinguished direction are positive, then the quadratic form
is positive on every nonzero vector orthogonal to that eigenvector. -/
lemma hermitian_quadratic_form_pos_of_orthogonal
    {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) (hA : A.IsHermitian) {k : m}
    (hkrest : ∀ j : m, j ≠ k → 0 < hA.eigenvalues j)
    {w : m → ℝ}
    (horth : dotProduct (star ⇑(hA.eigenvectorBasis k)) w = 0)
    (hw : w ≠ 0) :
    0 < star w ⬝ᵥ (A *ᵥ w) := by
  let coeff : m → ℝ := fun j => inner ℝ (hA.eigenvectorBasis j) (WithLp.toLp 2 w)
  have hkcoeff : coeff k = 0 := by
    dsimp [coeff]
    rw [EuclideanSpace.inner_toLp_toLp]
    simpa [coeff, dotProduct_comm] using horth
  have hterm_nonneg : ∀ j : m, 0 ≤ hA.eigenvalues j * coeff j ^ 2 := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp [coeff, hkcoeff]
    · exact mul_nonneg (le_of_lt (hkrest j hj)) (sq_nonneg _)
  obtain ⟨j, hjk, hjcoeff⟩ : ∃ j : m, j ≠ k ∧ coeff j ≠ 0 := by
    by_contra hcoords
    push_neg at hcoords
    have hcoeff_zero : ∀ i : m, coeff i = 0 := by
      intro i
      by_cases hi : i = k
      · subst hi
        exact hkcoeff
      · exact hcoords i hi
    have hvzero : WithLp.toLp 2 w = 0 := by
      calc
        WithLp.toLp 2 w = ∑ i, coeff i • hA.eigenvectorBasis i := by
          symm
          exact (hA.eigenvectorBasis).sum_repr' (WithLp.toLp 2 w)
        _ = 0 := by
          simp [coeff, hcoeff_zero]
    exact hw (by simpa using hvzero)
  rw [hermitian_quadratic_form_eq_sum_eigenvalues A hA w]
  have hpos_term : 0 < hA.eigenvalues j * coeff j ^ 2 := by
    exact mul_pos (hkrest j hjk) (sq_pos_of_ne_zero hjcoeff)
  have hle :
      hA.eigenvalues j * coeff j ^ 2 ≤
        ∑ i, hA.eigenvalues i * coeff i ^ 2 := by
    exact Finset.single_le_sum (fun i hi => hterm_nonneg i) (Finset.mem_univ _)
  linarith

/-
Let f: ℝ^n → ℝ be twice differentiable at x ∈ dom f. Let ∇ f(x) be the ∇of f at x, ∇^2 f(x) the
Hessian at x, and S^n the set of n × n real symmetric matrices. For M ∈ S^n, write M succeq 0 when M
is positive semidefinite, and let λ_n(M) denote the smallest eigenvalue of M. Define H(x) = [ ∇^2
f(x) & ∇ f(x); ∇ f(x)ᵀ & 0 ]. Prove that the condition ∀ y ∈ ℝ^n, yᵀ ∇ f(x) = 0 implies yᵀ ∇^2 f(x)y
≥ 0 holds if and only if either ∇ f(x) = 0 and ∇^2 f(x)succeq 0, or ∇ f(x)! = 0 and H(x) has exactly
one negative eigenvalue.
-/
theorem hessian_tangent_nonneg_iff_gradient_zero_psd_or_one_negative_eigenvalue
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hC2 : ContDiffAt ℝ 2 f x)
    (hHess_symm : (Hessian f x hC2).IsSymm) :
    (∀ y : Fin n → ℝ,
      (∑ i, y i * deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) →
        0 ≤ ∑ i, ∑ j, y i * (Hessian f x hC2) i j * y j) ↔
      ((∀ i, deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) ∧
        Matrix.PosSemidef (Hessian f x hC2)) ∨
      ((¬ ∀ i, deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) ∧
        let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
          fun i j =>
            if hi : i.1 < n then
              if hj : j.1 < n then
                (Hessian f x hC2) ⟨i.1, hi⟩ ⟨j.1, hj⟩
              else
                deriv (fun t : ℝ => f (Function.update x ⟨i.1, hi⟩ t)) (x ⟨i.1, hi⟩)
            else if hj : j.1 < n then
              deriv (fun t : ℝ => f (Function.update x ⟨j.1, hj⟩ t)) (x ⟨j.1, hj⟩)
            else
              0
        ∃ hHsymm : H.IsSymm,
          let hHherm : H.IsHermitian := by
            simpa using hHsymm
          ∃ k : Fin (n + 1), hHherm.eigenvalues k < 0 ∧
            ∀ j : Fin (n + 1), j ≠ k → 0 ≤ hHherm.eigenvalues j) := by
  classical
  by_cases hgrad :
      ∀ i, deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0
  · -- When the gradient vanishes, the theorem collapses to the positive-semidefinite criterion.
    have hzero :
        (∀ y : Fin n → ℝ,
          (∑ i, y i * deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) →
            0 ≤ ∑ i, ∑ j, y i * (Hessian f x hC2) i j * y j) ↔
          Matrix.PosSemidef (Hessian f x hC2) :=
      tangent_nonneg_iff_posSemidef_when_gradient_zero f x hC2 hHess_symm hgrad
    simpa [hgrad] using hzero
  · -- Route correction: the easy `g = 0` reduction is finished above, so the only remaining work is
    -- the genuine bordered-Hessian signature theorem in the nonzero-gradient case.
    have hnonzero_case :
        (∀ y : Fin n → ℝ,
          (∑ i, y i * deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) →
            0 ≤ ∑ i, ∑ j, y i * (Hessian f x hC2) i j * y j) ↔
          let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
            fun i j =>
              if hi : i.1 < n then
                if hj : j.1 < n then
                  (Hessian f x hC2) ⟨i.1, hi⟩ ⟨j.1, hj⟩
                else
                  deriv (fun t : ℝ => f (Function.update x ⟨i.1, hi⟩ t)) (x ⟨i.1, hi⟩)
              else if hj : j.1 < n then
                deriv (fun t : ℝ => f (Function.update x ⟨j.1, hj⟩ t)) (x ⟨j.1, hj⟩)
              else
                0
          ∃ hHsymm : H.IsSymm,
            let hHherm : H.IsHermitian := by
              simpa using hHsymm
            ∃ k : Fin (n + 1), hHherm.eigenvalues k < 0 ∧
              ∀ j : Fin (n + 1), j ≠ k → 0 ≤ hHherm.eigenvalues j := by
      -- Route correction: first isolate the explicit negative direction given by the nonzero
      -- gradient. This reduces the remaining work to the spectral uniqueness step.
      let g : Fin n → ℝ :=
        fun i => deriv (fun t : ℝ => f (Function.update x i t)) (x i)
      let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
        fun i j =>
          if hi : i.1 < n then
            if hj : j.1 < n then
              (Hessian f x hC2) ⟨i.1, hi⟩ ⟨j.1, hj⟩
            else
              g ⟨i.1, hi⟩
          else if hj : j.1 < n then
            g ⟨j.1, hj⟩
          else
            0
      have hHsymm : H.IsSymm := by
        -- The bordered matrix is symmetric because both the Hessian block and the gradient blocks
        -- are symmetric.
        simpa [H, g] using borderedHessian_isSymm f x hC2 hHess_symm
      let hHherm : H.IsHermitian := by
        simpa using hHsymm
      obtain ⟨i0, hi0⟩ : ∃ i, g i ≠ 0 := by
        -- The branch assumption says the gradient is not identically zero.
        simpa [g] using not_forall.mp hgrad
      obtain ⟨u, hu⟩ := exists_normalized_gradient_vector g hi0
      let q : ℝ := ∑ i, ∑ j, u i * (Hessian f x hC2) i j * u j
      let vneg : Fin (n + 1) → ℝ := Fin.lastCases (-(q + 1) / 2) (fun i => u i)
      have hvneg :
          (∑ i, ∑ j, vneg i * H i j * vneg j) = -1 := by
        -- This is the explicit negative witness promised by the bordered-matrix identity.
        simpa [H, g, q, vneg] using
          bordered_matrix_negative_witness (A := Hessian f x hC2) (g := g) (u := u) hu
      have hnot_posSemidef : ¬ Matrix.PosSemidef H := by
        -- A positive-semidefinite matrix cannot take the value `-1` on any vector.
        intro hPSD
        have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hPSD).2 vneg
        have hvalue :
            star vneg ⬝ᵥ (H *ᵥ vneg) =
              ∑ i, ∑ j, vneg i * H i j * vneg j := by
          simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
        linarith [hvneg, hvalue.symm ▸ hnonneg]
      have hnot_all_nonneg : ¬ ∀ j : Fin (n + 1), 0 ≤ hHherm.eigenvalues j := by
        -- If every eigenvalue were nonnegative, the Hermitian matrix would be positive semidefinite.
        intro hall
        exact hnot_posSemidef ((hHherm.posSemidef_iff_eigenvalues_nonneg).2 hall)
      obtain ⟨k, hkneg⟩ : ∃ k : Fin (n + 1), hHherm.eigenvalues k < 0 := by
        simpa using not_forall.mp hnot_all_nonneg
      have hquadratic_raw (w : Fin (n + 1) → ℝ) :
          star w ⬝ᵥ (H *ᵥ w) = ∑ i, ∑ j, w i * H i j * w j := by
        -- Over `ℝ`, the Hermitian quadratic form is the raw double sum defining the bordered form.
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      have hbordered_nonneg_of_tangent
          (htangent :
            ∀ y : Fin n → ℝ,
              (∑ i, y i * deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) →
                0 ≤ ∑ i, ∑ j, y i * (Hessian f x hC2) i j * y j)
          {w : Fin (n + 1) → ℝ}
          (hw : ∑ i, w i.castSucc * g i = 0) :
          0 ≤ star w ⬝ᵥ (H *ᵥ w) := by
        -- Any bordered vector whose top part is tangent inherits the tangent nonnegativity.
        have htop_nonneg :
            0 ≤ ∑ i, ∑ j, w i.castSucc * (Hessian f x hC2) i j * w j.castSucc :=
          htangent (fun i => w i.castSucc) (by simpa [g] using hw)
        rw [hquadratic_raw, bordered_matrix_quadratic_form (A := Hessian f x hC2) (g := g) (v := w)]
        simpa [hw] using htop_nonneg
      have hk_value :
          star ⇑(hHherm.eigenvectorBasis k) ⬝ᵥ (H *ᵥ ⇑(hHherm.eigenvectorBasis k)) =
            hHherm.eigenvalues k :=
        hermitian_quadratic_form_eigenvector H hHherm k
      have hL_linear (r s : ℝ) (a b : Fin (n + 1) → ℝ) :
          (∑ i, (r • a + s • b) i.castSucc * g i) =
            r * ∑ i, a i.castSucc * g i + s * ∑ i, b i.castSucc * g i :=
        bordered_tangent_functional_add_smul g r s a b
      let L : (Fin (n + 1) → ℝ) → ℝ := fun w => ∑ i, w i.castSucc * g i
      have hquadratic_expansion (w : Fin (n + 1) → ℝ) :
          star w ⬝ᵥ (H *ᵥ w) =
            ∑ i, hHherm.eigenvalues i *
              (inner ℝ (hHherm.eigenvectorBasis i) (WithLp.toLp 2 w)) ^ 2 := by
        -- Route correction: instead of searching for a bespoke coercion lemma, convert `w` with
        -- `WithLp.toLp` and use the orthonormal eigenbasis directly in Euclidean space.
        let v : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 w
        let T : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
          Matrix.toEuclideanLin H
        have hTsymm : T.IsSymmetric := by
          simpa [T] using (Matrix.isHermitian_iff_isSymmetric (A := H)).mp hHherm
        have hinner :
            star w ⬝ᵥ (H *ᵥ w) = inner ℝ (T v) v := by
          simpa [T, v, Matrix.toEuclideanLin_apply_piLp_toLp] using
            (EuclideanSpace.inner_toLp_toLp (x := H *ᵥ w) (y := w)).symm
        calc
          star w ⬝ᵥ (H *ᵥ w) = inner ℝ (T v) v := hinner
          _ = ∑ i, inner ℝ (T v) (hHherm.eigenvectorBasis i) *
                inner ℝ (hHherm.eigenvectorBasis i) v := by
                rw [← (hHherm.eigenvectorBasis).sum_inner_mul_inner (T v) v]
          _ = ∑ i, hHherm.eigenvalues i *
                (inner ℝ (hHherm.eigenvectorBasis i) v) ^ 2 := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hbasis :
                    T (hHherm.eigenvectorBasis i) =
                      (hHherm.eigenvalues i) • hHherm.eigenvectorBasis i := by
                  -- The bordered operator acts diagonally on its orthonormal eigenbasis.
                  simpa [T, Matrix.toEuclideanLin_apply] using
                    congrArg (WithLp.toLp 2) (hHherm.mulVec_eigenvectorBasis i)
                have hcoord :
                    inner ℝ (T v) (hHherm.eigenvectorBasis i) =
                      hHherm.eigenvalues i *
                        inner ℝ (hHherm.eigenvectorBasis i) v := by
                  -- Symmetry moves `T` to the right, where the eigenvector equation applies.
                  calc
                    inner ℝ (T v) (hHherm.eigenvectorBasis i) =
                        inner ℝ v (T (hHherm.eigenvectorBasis i)) := by
                          simpa [T] using hTsymm v (hHherm.eigenvectorBasis i)
                    _ = inner ℝ v ((hHherm.eigenvalues i) • hHherm.eigenvectorBasis i) := by
                          rw [hbasis]
                    _ = hHherm.eigenvalues i * inner ℝ v (hHherm.eigenvectorBasis i) := by
                          rw [inner_smul_right]
                    _ = hHherm.eigenvalues i *
                          inner ℝ (hHherm.eigenvectorBasis i) v := by
                          rw [real_inner_comm]
                rw [hcoord]
                ring
      have hquadratic_nonneg_of_orthogonal
          {k : Fin (n + 1)}
          (hkrest : ∀ j : Fin (n + 1), j ≠ k → 0 ≤ hHherm.eigenvalues j)
          {w : Fin (n + 1) → ℝ}
          (hworth : dotProduct (star ⇑(hHherm.eigenvectorBasis k)) w = 0) :
          0 ≤ star w ⬝ᵥ (H *ᵥ w) := by
        -- Orthogonality to the unique negative eigenvector removes its coefficient from the
        -- spectral expansion, so every remaining term is nonnegative.
        rw [hquadratic_expansion w]
        refine Finset.sum_nonneg ?_
        intro j hj
        by_cases hjk : j = k
        · have hworth_j :
              dotProduct (star ⇑(hHherm.eigenvectorBasis j)) w = 0 := by
            simpa [hjk] using hworth
          have hcoeff_zero :
              inner ℝ (hHherm.eigenvectorBasis j) (WithLp.toLp 2 w) = 0 := by
            rw [EuclideanSpace.inner_toLp_toLp]
            simpa [dotProduct_comm] using hworth_j
          subst hjk
          simpa [hcoeff_zero]
        · exact mul_nonneg (hkrest j hjk) (sq_nonneg _)
      have hnegative_eigenvector_not_tangent
          (htangent :
            ∀ y : Fin n → ℝ,
              (∑ i, y i * deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) →
                0 ≤ ∑ i, ∑ j, y i * (Hessian f x hC2) i j * y j)
          {i : Fin (n + 1)} (hi : hHherm.eigenvalues i < 0) :
          L ⇑(hHherm.eigenvectorBasis i) ≠ 0 := by
        -- A negative eigenvector cannot satisfy the tangent constraint, or else tangent
        -- nonnegativity would contradict its negative eigenvalue.
        intro hLi
        have hnonneg :
            0 ≤ star ⇑(hHherm.eigenvectorBasis i) ⬝ᵥ
              (H *ᵥ ⇑(hHherm.eigenvectorBasis i)) :=
          hbordered_nonneg_of_tangent htangent (by simpa [L] using hLi)
        have hvalue_i :
            star ⇑(hHherm.eigenvectorBasis i) ⬝ᵥ
              (H *ᵥ ⇑(hHherm.eigenvectorBasis i)) = hHherm.eigenvalues i :=
          hermitian_quadratic_form_eigenvector H hHherm i
        linarith
      constructor
      · intro htangent
        have hkrest : ∀ j : Fin (n + 1), j ≠ k → 0 ≤ hHherm.eigenvalues j := by
          intro j hkj
          by_contra hj_nonneg
          have hjneg : hHherm.eigenvalues j < 0 := by
            linarith
          let ek : Fin (n + 1) → ℝ := ⇑(hHherm.eigenvectorBasis k)
          let ej : Fin (n + 1) → ℝ := ⇑(hHherm.eigenvectorBasis j)
          let r : ℝ := L ej
          let s : ℝ := -L ek
          have hr_ne : r ≠ 0 := by
            simpa [L, r, ej] using hnegative_eigenvector_not_tangent htangent hjneg
          have hs_ne : s ≠ 0 := by
            simpa [L, s, ek] using hnegative_eigenvector_not_tangent htangent hkneg
          have hw_tangent : L (r • ek + s • ej) = 0 := by
            -- Choose the coefficients so the bordered tangent functional cancels.
            change ∑ i, (r • ek + s • ej) i.castSucc * g i = 0
            rw [hL_linear r s ek ej]
            simp [L, r, s]
            ring
          have hcomb_toLp :
              WithLp.toLp 2 (r • ek + s • ej) =
                r • hHherm.eigenvectorBasis k + s • hHherm.eigenvectorBasis j := by
            ext t
            simp [ek, ej]
          have hcoord_comb (t : Fin (n + 1)) :
              inner ℝ (hHherm.eigenvectorBasis t) (WithLp.toLp 2 (r • ek + s • ej)) =
                if t = k then r else if t = j then s else 0 := by
            -- The chosen vector has eigenbasis coordinates supported only on `k` and `j`.
            by_cases htk : t = k
            · have htj : t ≠ j := by
                intro htj
                apply hkj
                simpa [htk] using htj.symm
              have hcalc :
                  inner ℝ (hHherm.eigenvectorBasis t) (WithLp.toLp 2 (r • ek + s • ej)) = r := by
                rw [hcomb_toLp, inner_add_right, inner_smul_right, inner_smul_right]
                have hself :
                    inner ℝ (hHherm.eigenvectorBasis t) (hHherm.eigenvectorBasis k) = 1 := by
                  simpa [htk] using (hHherm.eigenvectorBasis.inner_eq_one k)
                have hzero :
                    inner ℝ (hHherm.eigenvectorBasis t) (hHherm.eigenvectorBasis j) = 0 := by
                  exact hHherm.eigenvectorBasis.inner_eq_zero htj
                rw [hself, hzero]
                ring
              simpa [htk, htj, hkj] using hcalc
            · by_cases htj : t = j
              · have htk' : t ≠ k := by
                  intro htk'
                  exact htk htk'
                have hcalc :
                    inner ℝ (hHherm.eigenvectorBasis t) (WithLp.toLp 2 (r • ek + s • ej)) = s := by
                  rw [hcomb_toLp, inner_add_right, inner_smul_right, inner_smul_right]
                  have hzero :
                      inner ℝ (hHherm.eigenvectorBasis t) (hHherm.eigenvectorBasis k) = 0 := by
                    exact hHherm.eigenvectorBasis.inner_eq_zero htk'
                  have hself :
                      inner ℝ (hHherm.eigenvectorBasis t) (hHherm.eigenvectorBasis j) = 1 := by
                    simpa [htj] using (hHherm.eigenvectorBasis.inner_eq_one j)
                  rw [hzero, hself]
                  ring
                simpa [htk, htj, hkj] using hcalc
              · have hzero_k :
                    inner ℝ (hHherm.eigenvectorBasis t) (hHherm.eigenvectorBasis k) = 0 := by
                    exact hHherm.eigenvectorBasis.inner_eq_zero htk
                have hzero_j :
                    inner ℝ (hHherm.eigenvectorBasis t) (hHherm.eigenvectorBasis j) = 0 := by
                    exact hHherm.eigenvectorBasis.inner_eq_zero htj
                calc
                  inner ℝ (hHherm.eigenvectorBasis t) (WithLp.toLp 2 (r • ek + s • ej))
                      = inner ℝ (hHherm.eigenvectorBasis t)
                          (r • hHherm.eigenvectorBasis k + s • hHherm.eigenvectorBasis j) := by
                            rw [hcomb_toLp]
                  _ = inner ℝ (hHherm.eigenvectorBasis t) (r • hHherm.eigenvectorBasis k) +
                        inner ℝ (hHherm.eigenvectorBasis t) (s • hHherm.eigenvectorBasis j) := by
                        rw [inner_add_right]
                  _ = r * inner ℝ (hHherm.eigenvectorBasis t) (hHherm.eigenvectorBasis k) +
                        s * inner ℝ (hHherm.eigenvectorBasis t) (hHherm.eigenvectorBasis j) := by
                        rw [inner_smul_right, inner_smul_right]
                  _ = 0 := by rw [hzero_k, hzero_j]; ring
                simpa [htk, htj] using hcalc
          have hform_eq :
              star (r • ek + s • ej) ⬝ᵥ (H *ᵥ (r • ek + s • ej)) =
                r ^ 2 * hHherm.eigenvalues k + s ^ 2 * hHherm.eigenvalues j := by
            -- Route correction: stay inside the span of the two chosen eigenvectors instead of
            -- reopening the global spectral-sum formula.
            have hmul_toLp :
                WithLp.toLp 2 (H *ᵥ (r • ek + s • ej)) =
                  (r * hHherm.eigenvalues k) • hHherm.eigenvectorBasis k +
                    (s * hHherm.eigenvalues j) • hHherm.eigenvectorBasis j := by
              -- The bordered matrix acts diagonally on each eigenvector, so the image of the
              -- chosen combination stays in the same 2-dimensional span.
              calc
                WithLp.toLp 2 (H *ᵥ (r • ek + s • ej))
                    = WithLp.toLp 2 (r • (H *ᵥ ek) + s • (H *ᵥ ej)) := by
                        simp [Matrix.mulVec_add, Matrix.mulVec_smul]
                _ = WithLp.toLp 2
                      (r • (hHherm.eigenvalues k • ek) + s • (hHherm.eigenvalues j • ej)) := by
                        rw [hHherm.mulVec_eigenvectorBasis k, hHherm.mulVec_eigenvectorBasis j]
                _ = (r * hHherm.eigenvalues k) • hHherm.eigenvectorBasis k +
                      (s * hHherm.eigenvalues j) • hHherm.eigenvectorBasis j := by
                        ext t
                        simp [ek, ej, mul_assoc]
            have hinner :
                star (r • ek + s • ej) ⬝ᵥ (H *ᵥ (r • ek + s • ej)) =
                  inner ℝ
                    (WithLp.toLp 2 (H *ᵥ (r • ek + s • ej)))
                    (WithLp.toLp 2 (r • ek + s • ej)) := by
              -- Rewrite the quadratic form as the Euclidean inner product on `WithLp.toLp`.
              simpa using
                (EuclideanSpace.inner_toLp_toLp (x := H *ᵥ (r • ek + s • ej))
                  (y := r • ek + s • ej)).symm
            have hkk :
                inner ℝ (hHherm.eigenvectorBasis k) (hHherm.eigenvectorBasis k) = 1 := by
              simpa using hHherm.eigenvectorBasis.inner_eq_one k
            have hjj :
                inner ℝ (hHherm.eigenvectorBasis j) (hHherm.eigenvectorBasis j) = 1 := by
              simpa using hHherm.eigenvectorBasis.inner_eq_one j
            have hkj_inner :
                inner ℝ (hHherm.eigenvectorBasis k) (hHherm.eigenvectorBasis j) = 0 := by
              exact hHherm.eigenvectorBasis.inner_eq_zero hkj.symm
            have hjk_inner :
                inner ℝ (hHherm.eigenvectorBasis j) (hHherm.eigenvectorBasis k) = 0 := by
              exact hHherm.eigenvectorBasis.inner_eq_zero hkj
            -- Expand the two-term inner product and use orthogonality to remove the mixed terms.
            rw [hinner, hmul_toLp, hcomb_toLp]
            calc
              inner ℝ
                  ((r * hHherm.eigenvalues k) • hHherm.eigenvectorBasis k +
                    (s * hHherm.eigenvalues j) • hHherm.eigenvectorBasis j)
                  (r • hHherm.eigenvectorBasis k + s • hHherm.eigenvectorBasis j)
                  =
                    (inner ℝ ((r * hHherm.eigenvalues k) • hHherm.eigenvectorBasis k)
                        (r • hHherm.eigenvectorBasis k) +
                      inner ℝ ((r * hHherm.eigenvalues k) • hHherm.eigenvectorBasis k)
                        (s • hHherm.eigenvectorBasis j)) +
                    (inner ℝ ((s * hHherm.eigenvalues j) • hHherm.eigenvectorBasis j)
                        (r • hHherm.eigenvectorBasis k) +
                      inner ℝ ((s * hHherm.eigenvalues j) • hHherm.eigenvectorBasis j)
                        (s • hHherm.eigenvectorBasis j)) := by
                          rw [inner_add_left, inner_add_right, inner_add_right]
              _ =
                    ((r * hHherm.eigenvalues k) * (r * inner ℝ
                      (hHherm.eigenvectorBasis k) (hHherm.eigenvectorBasis k)) +
                      (r * hHherm.eigenvalues k) * (s * inner ℝ
                        (hHherm.eigenvectorBasis k) (hHherm.eigenvectorBasis j))) +
                    ((s * hHherm.eigenvalues j) * (r * inner ℝ
                      (hHherm.eigenvectorBasis j) (hHherm.eigenvectorBasis k)) +
                      (s * hHherm.eigenvalues j) * (s * inner ℝ
                        (hHherm.eigenvectorBasis j) (hHherm.eigenvectorBasis j))) := by
                          simp [inner_smul_left, inner_smul_right]
                          ring
              _ = ((r * hHherm.eigenvalues k) * r + 0) + (0 + (s * hHherm.eigenvalues j) * s) := by
                    rw [hkk, hjj, hkj_inner, hjk_inner]
                    ring
              _ = r ^ 2 * hHherm.eigenvalues k + s ^ 2 * hHherm.eigenvalues j := by
                    ring
          have hnonneg :
              0 ≤ star (r • ek + s • ej) ⬝ᵥ (H *ᵥ (r • ek + s • ej)) :=
            hbordered_nonneg_of_tangent htangent (by simpa [L] using hw_tangent)
          rw [hform_eq] at hnonneg
          have hr_sq_pos : 0 < r ^ 2 := by
            nlinarith [sq_pos_of_ne_zero hr_ne]
          have hs_sq_pos : 0 < s ^ 2 := by
            nlinarith [sq_pos_of_ne_zero hs_ne]
          nlinarith
        exact ⟨hHsymm, k, hkneg, hkrest⟩
      · rintro ⟨hHsymm', k', hk'neg, hk'rest⟩ z hz_tangent
        have hk'neg' : hHherm.eigenvalues k' < 0 := by
          simpa using hk'neg
        have hk'rest' : ∀ j : Fin (n + 1), j ≠ k' → 0 ≤ hHherm.eigenvalues j := by
          intro j hj
          simpa using hk'rest j hj
        by_contra hz_nonneg
        have hz_neg :
            ∑ i, ∑ j, z i * (Hessian f x hC2) i j * z j < 0 := by
          linarith
        have hz_neg_dot : z ⬝ᵥ ((Hessian f x hC2) *ᵥ z) < 0 := by
          simpa [Matrix.dotProduct_mulVec, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
            using hz_neg
        let A : Matrix (Fin n) (Fin n) ℝ := Hessian f x hC2
        let qU : ℝ := u ⬝ᵥ (A *ᵥ u)
        let a : Fin (n + 1) → ℝ := Fin.lastCases (-(z ⬝ᵥ (A *ᵥ u))) (fun i => z i)
        let b : Fin (n + 1) → ℝ := Fin.lastCases (-1 - qU / 2) (fun i => u i)
        have hnegative_plane (r s : ℝ) :
            star (r • a + s • b) ⬝ᵥ (H *ᵥ (r • a + s • b)) =
              r ^ 2 * (z ⬝ᵥ (A *ᵥ z)) - 2 * s ^ 2 := by
          have hz_scaled : ∑ i, (r • z) i * g i = 0 := by
            -- Scaling preserves the tangent constraint on the top block.
            have hfactor :
                ∑ i, (r • z) i * g i = r * ∑ i, z i * g i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [Pi.smul_apply]
              ring
            rw [hfactor]
            simpa [g] using congrArg (fun t : ℝ => r * t) hz_tangent
          have hscale_quad :
              (r • z) ⬝ᵥ (A *ᵥ (r • z)) = r ^ 2 * (z ⬝ᵥ (A *ᵥ z)) := by
            simp [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
            ring
          let wplane : Fin (n + 1) → ℝ :=
            Fin.lastCases (-s - (r • z) ⬝ᵥ (A *ᵥ u) - (qU / 2) * s)
              (fun i => (r • z) i + s * u i)
          have hwplane :
              r • a + s • b = wplane := by
            -- Unfold the two spanning vectors and compare coordinates.
            ext i
            cases i using Fin.lastCases <;> simp [a, b, wplane, qU, Pi.smul_apply] <;> ring
          have hcomplete :
              ∑ i, ∑ j, wplane i * H i j * wplane j =
                (r • z) ⬝ᵥ (A *ᵥ (r • z)) + 2 * s * (-s) := by
            simpa [A, H, g, qU, wplane] using
              bordered_matrix_complete_square (A := A) (hA := hHess_symm) (g := g) (u := u)
                (z := r • z) hu hz_scaled s (-s)
          rw [hquadratic_raw, hwplane, hcomplete, hscale_quad]
          ring
        let ek : Fin (n + 1) → ℝ := ⇑(hHherm.eigenvectorBasis k')
        let α : ℝ := dotProduct (star ek) b
        let β : ℝ := dotProduct (star ek) a
        have hqa_neg : star a ⬝ᵥ (H *ᵥ a) < 0 := by
          -- The first spanning vector of the plane already carries the original negative tangent
          -- direction.
          have hqa_eq : star a ⬝ᵥ (H *ᵥ a) = z ⬝ᵥ (A *ᵥ z) := by
            simpa [A] using hnegative_plane 1 0
          rw [hqa_eq]
          exact hz_neg_dot
        by_cases hβ : β = 0
        · have ha_orth : dotProduct (star ek) a = 0 := by
            simpa [ek, β] using hβ
          have hnonneg_a := hquadratic_nonneg_of_orthogonal hk'rest' ha_orth
          linarith
        · have hw_orth :
              dotProduct (star ek) (α • a + (-β) • b) = 0 := by
            -- This is the standard 2D orthogonal combination against the negative eigenvector.
            simp [α, β, ek, sub_eq_add_neg, dotProduct_add, dotProduct_smul]
            ring
          have hqw_neg :
              star (α • a + (-β) • b) ⬝ᵥ (H *ᵥ (α • a + (-β) • b)) < 0 := by
            rw [hnegative_plane α (-β)]
            have hβ_sq_pos : 0 < β ^ 2 := by
              nlinarith [sq_pos_of_ne_zero hβ]
            nlinarith [hz_neg_dot, sq_nonneg α, hβ_sq_pos]
          have hnonneg_w := hquadratic_nonneg_of_orthogonal hk'rest' hw_orth
          linarith
    simpa [hgrad] using hnonzero_case

/-
Let f: ℝ^n → ℝ be twice differentiable at x ∈ dom f. Let ∇ f(x) be the ∇of f at x, ∇^2 f(x) the
Hessian at x, and S^n the set of n × n real symmetric matrices. For M ∈ S^n, write M succeq 0 when M
is positive semidefinite, and let λ_n(M) denote the smallest eigenvalue of M. Define H(x) = [ ∇^2
f(x) & ∇ f(x); ∇ f(x)ᵀ & 0 ]. Prove that the condition ∀ y ∈ ℝ^n, y ≠ 0 and yᵀ ∇ f(x) = 0 implies yᵀ
∇^2 f(x)y > 0 holds if and only if H(x) has exactly one nonpositive eigenvalue.
-/
theorem hessian_strict_tangent_pos_iff_H_has_exactly_one_nonpositive_eigenvalue
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hC2 : ContDiffAt ℝ 2 f x)
    (hHess_symm : (Hessian f x hC2).IsSymm) :
    (∀ y : Fin n → ℝ,
      y ≠ 0 →
      (∑ i, y i * deriv (fun t : ℝ => f (Function.update x i t)) (x i) = 0) →
      0 < ∑ i, ∑ j, y i * (Hessian f x hC2) i j * y j) ↔
    let H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j =>
        if hi : i.1 < n then
          if hj : j.1 < n then
            (Hessian f x hC2) ⟨i.1, hi⟩ ⟨j.1, hj⟩
          else
            deriv (fun t : ℝ => f (Function.update x ⟨i.1, hi⟩ t)) (x ⟨i.1, hi⟩)
        else if hj : j.1 < n then
          deriv (fun t : ℝ => f (Function.update x ⟨j.1, hj⟩ t)) (x ⟨j.1, hj⟩)
        else
          0
    ∃ hHsymm : H.IsSymm,
      let hHherm : H.IsHermitian := by
        simpa using hHsymm
      ∃ k : Fin (n + 1),
        hHherm.eigenvalues k ≤ 0 ∧
        ∀ j : Fin (n + 1), j ≠ k → 0 < hHherm.eigenvalues j := by
  sorry

/-
If B ∈ S^n and a ∈ ℝ^n, then λ_n([ B & a; aᵀ & 0 ]) ≤ λ_n(B).
-/
theorem smallest_eigenvalue_block_arrow_le_smallest_eigenvalue
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hn : 0 < n)
    (hB : Matrix.IsSymm B) :
    let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j =>
        if h1 : i.1 < n then
          if h2 : j.1 < n then
            B ⟨i.1, h1⟩ ⟨j.1, h2⟩
          else
            a ⟨i.1, h1⟩
        else
          if h2 : j.1 < n then
            a ⟨j.1, h2⟩
          else
            0
    ∃ hA : A.IsSymm,
      let hAHerm : A.IsHermitian := by
        simpa using hA
      let hBHerm : B.IsHermitian := by
        simpa using hB
      hAHerm.eigenvalues₀ (Fin.cast (by simp) (Fin.last n)) ≤
        hBHerm.eigenvalues₀
          (Fin.cast (by simp) ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩) := by
  intro A
  have hA : A.IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    by_cases hi : i.1 < n
    · by_cases hj : j.1 < n
      · simpa [A, hi, hj] using hB.apply ⟨i.1, hi⟩ ⟨j.1, hj⟩
      · simp [A, hi, hj]
    · by_cases hj : j.1 < n
      · simp [A, hi, hj]
      · simp [A, hi, hj]
  refine ⟨hA, ?_⟩
  let hAHerm : A.IsHermitian := by
    simpa using hA
  let hBHerm : B.IsHermitian := by
    simpa using hB
  let iA₀ : Fin (Fintype.card (Fin (n + 1))) := Fin.cast (by simp) (Fin.last n)
  let iB₀ : Fin (Fintype.card (Fin n)) :=
    Fin.cast (by simp) ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
  let iB : Fin n := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))) iB₀
  let u : Fin n → ℝ := ⇑(hBHerm.eigenvectorBasis iB)
  let w : Fin (n + 1) → ℝ := Fin.lastCases 0 fun i => u i
  have hu_inner : star u ⬝ᵥ u = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp (x := u) (y := u)]
    simpa [u] using hBHerm.eigenvectorBasis.inner_eq_one iB
  have hw_nonzero : (w : Fin (n + 1) → ℝ) ≠ 0 := by
    intro hw
    have hu_zero : u = 0 := by
      funext i
      simpa [w] using congrArg (fun v : Fin (n + 1) → ℝ => v i.castSucc) hw
    have : star u ⬝ᵥ u = 0 := by simp [hu_zero]
    linarith
  have hw_inner : star w ⬝ᵥ w = 1 := by
    rw [dotProduct, Fin.sum_univ_castSucc]
    simpa [w, dotProduct] using hu_inner
  have hsum :
      ∑ i, ∑ j, w i * A i j * w j = ∑ i, ∑ j, u i * B i j * u j := by
    simpa [A, w, u] using bordered_matrix_quadratic_form (A := B) (g := a) (v := w)
  have hBquad :
      ∑ i, ∑ j, u i * B i j * u j = hBHerm.eigenvalues iB := by
    simpa [u, Matrix.dotProduct_mulVec, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using
      hermitian_quadratic_form_eigenvector B hBHerm iB
  have hw_value :
      star w ⬝ᵥ (A *ᵥ w) = hBHerm.eigenvalues iB := by
    calc
      star w ⬝ᵥ (A *ᵥ w) = ∑ i, ∑ j, w i * A i j * w j := by
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      _ = ∑ i, ∑ j, u i * B i j * u j := hsum
      _ = hBHerm.eigenvalues iB := hBquad
  let T : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    Matrix.toEuclideanLin A
  have hTsymm : T.IsSymmetric := by
    simpa [T] using (Matrix.isHermitian_iff_isSymmetric (A := A)).mp hAHerm
  let μ : ℝ :=
    ⨅ x : {x : EuclideanSpace ℝ (Fin (n + 1)) // x ≠ 0},
      inner ℝ (T x) x / ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2
  have hμ_eig : Module.End.HasEigenvalue T μ := by
    simpa [μ] using LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional (T := T) hTsymm
  obtain ⟨j, hj⟩ := hTsymm.exists_eigenvalues_eq finrank_euclideanSpace hμ_eig
  have hmin_le_μ : hAHerm.eigenvalues₀ iA₀ ≤ μ := by
    have hlast :
        hAHerm.eigenvalues₀ iA₀ ≤ hAHerm.eigenvalues₀ j :=
      hAHerm.eigenvalues₀_antitone (show j ≤ iA₀ by
        change j.1 ≤ iA₀.1
        have hjlt : j.1 < n + 1 := by simpa using j.is_lt
        simpa [iA₀] using Nat.le_of_lt_succ hjlt)
    have hj' : hAHerm.eigenvalues₀ j = μ := by
      simpa [Matrix.IsHermitian.eigenvalues₀, μ] using hj
    exact hj' ▸ hlast
  have hw_toLp_nonzero : (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
    simpa using hw_nonzero
  have hμ_le_value : μ ≤ star w ⬝ᵥ (A *ᵥ w) := by
    let xw : {x : EuclideanSpace ℝ (Fin (n + 1)) // x ≠ 0} := ⟨WithLp.toLp 2 w, hw_toLp_nonzero⟩
    have hμ_bdd :
        BddBelow
          (Set.range fun x : {x : EuclideanSpace ℝ (Fin (n + 1)) // x ≠ 0} =>
            inner ℝ (T x) x / ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2) := by
      refine ⟨-‖T.toContinuousLinearMap‖, ?_⟩
      rintro _ ⟨x, rfl⟩
      have hbound :
          |inner ℝ (T x) x / ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2| ≤
            ‖T.toContinuousLinearMap‖ := by
        simpa [ContinuousLinearMap.rayleighQuotient] using
          ContinuousLinearMap.rayleighQuotient_le_norm (T := T.toContinuousLinearMap) x
      exact (abs_le.mp hbound).1
    have hle :
        μ ≤ inner ℝ (T (WithLp.toLp 2 w)) (WithLp.toLp 2 w) /
          ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 :=
      by
        simpa [μ, xw] using (ciInf_le hμ_bdd xw)
    have hnorm_sq :
        ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa [dotProduct, sq] using hw_inner
    have hrayleigh :
        inner ℝ (T (WithLp.toLp 2 w)) (WithLp.toLp 2 w) /
            ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 =
          star w ⬝ᵥ (A *ᵥ w) := by
      have hinner :
          inner ℝ (T (WithLp.toLp 2 w)) (WithLp.toLp 2 w) =
            star w ⬝ᵥ (A *ᵥ w) := by
        simpa [T] using
          (EuclideanSpace.inner_toLp_toLp (x := A *ᵥ w) (y := w)).symm
      rw [hinner, hnorm_sq]
      norm_num
    simpa [hrayleigh] using hle
  calc
    hAHerm.eigenvalues₀ iA₀ ≤ μ := hmin_le_μ
    _ ≤ star w ⬝ᵥ (A *ᵥ w) := hμ_le_value
    _ = hBHerm.eigenvalues iB := hw_value
    _ = hBHerm.eigenvalues₀ iB₀ := by
          simp [Matrix.IsHermitian.eigenvalues, iB, iB₀]

end «problem-17»
