import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-55»

/- [BLOCK Exercise 2.21-(c) | 27 | thm]
Let S^n denote the vector space of all n imes n real symmetric matrices. For X ∈ S^n, let
λ(X)=(λ_1(X),λ_2(X),ldots,λ_n(X)) ∈ ℝ^n denote the vector of eigenvalues of X. For a square matrix
M, let diag(M) ∈ ℝ^n denote the vector of diagonal entries of M. Let V be the set of all n imes n
orthogonal matrices V satisfying Vᵀ V = V Vᵀ = I. A permutation matrix is a matrix obtained by
permuting the rows of the identity matrix. A function f:ℝ^n o ℝ is symmetric if f(x)=f(Px) for every
permutation matrix P and every x ∈ ℝ^n. Let f:ℝ^n o ℝ be symmetric. If f is convex and X∈ S^n, show
that f(λ(X))=sup_{V∈V} figl(diag(Vᵀ X V)igr), where V is the set of n imes n orthogonal matrices.
-/
open Matrix

/-- The entrywise product of the columns of an orthogonal matrix defines a doubly stochastic matrix. -/
lemma squareEntryMatrix_mem_doublyStochastic
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℝ)
    (hUUt : U * U.transpose = 1)
    (hUtU : U.transpose * U = 1) :
    (fun i j => U j i * U j i : Matrix n n ℝ) ∈ doublyStochastic ℝ n := by
  let D : Matrix n n ℝ := fun i j => U j i * U j i
  -- The row sums are the diagonal entries of `Uᵀ U = 1`.
  have hrow : ∀ i, ∑ j, D i j = 1 := by
    intro i
    have hi : (U.transpose * U) i i = (1 : Matrix n n ℝ) i i := by
      simpa using congrFun (congrFun hUtU i) i
    simpa [D, Matrix.mul_apply] using hi
  -- The column sums are the diagonal entries of `U Uᵀ = 1`.
  have hcol : ∀ j, ∑ i, D i j = 1 := by
    intro j
    have hj : (U * U.transpose) j j = (1 : Matrix n n ℝ) j j := by
      simpa using congrFun (congrFun hUUt j) j
    simpa [D, Matrix.mul_apply] using hj
  -- Nonnegativity is immediate from the square form.
  exact (mem_doublyStochastic_iff_sum).2 ⟨by intro i j; exact mul_self_nonneg _, hrow, hcol⟩

/-- The diagonal of `Uᵀ (diag x) U` is the doubly stochastic action induced by the squared entries
of `U`. -/
lemma diag_transpose_diagonal_mul_eq_squareEntry_mulVec
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℝ)
    (x : n → ℝ) :
    (fun i => (U.transpose * Matrix.diagonal x * U) i i) =
      (fun i j => U j i * U j i : Matrix n n ℝ) *ᵥ x := by
  let D : Matrix n n ℝ := fun i j => U j i * U j i
  -- Expand the `(i,i)` entry of the triple product and collapse the diagonal matrix action.
  funext i
  calc
    (U.transpose * Matrix.diagonal x * U) i i
        = (U.transpose i) ⬝ᵥ (Matrix.diagonal x *ᵥ U.transpose i) := by
            simpa using Matrix.mul_mul_apply U.transpose (Matrix.diagonal x) U i i
    _ = ∑ j, U j i * (x j * U j i) := by
            simp [dotProduct, Matrix.mulVec_diagonal]
    _ = ∑ j, D i j * x j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [D, mul_left_comm, mul_comm]
    _ = (((fun i j => U j i * U j i : Matrix n n ℝ) *ᵥ x) i) := by
            simp [D, Matrix.mulVec, dotProduct]

/-- A symmetric convex function decreases under the action of a doubly stochastic matrix. -/
lemma symmetric_convex_le_of_mem_doublyStochastic
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : (n → ℝ) → ℝ)
    (hf_symm : ∀ (e : Equiv.Perm n) (x : n → ℝ), f x = f (fun i => x (e i)))
    (hf_convex : ConvexOn ℝ (Set.univ : Set (n → ℝ)) f)
    (D : Matrix n n ℝ)
    (hD : D ∈ doublyStochastic ℝ n)
    (x : n → ℝ) :
    f (D *ᵥ x) ≤ f x := by
  obtain ⟨w, hw0, hw1, hwD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  -- Rewrite the matrix action as a convex combination of permutation actions.
  have hsum : (∑ σ, w σ • (σ.permMatrix ℝ *ᵥ x)) = D *ᵥ x := by
    calc
      ∑ σ, w σ • (σ.permMatrix ℝ *ᵥ x)
          = ∑ σ, (w σ • σ.permMatrix ℝ) *ᵥ x := by
              refine Finset.sum_congr rfl ?_
              intro σ hσ
              rw [smul_mulVec]
      _ = (∑ σ, w σ • σ.permMatrix ℝ) *ᵥ x := by
              simpa using
                (Matrix.sum_mulVec Finset.univ (fun σ : Equiv.Perm n => w σ • σ.permMatrix ℝ) x).symm
      _ = D *ᵥ x := by rw [hwD]
  -- Jensen bounds the convex combination, and symmetry makes each summand equal to `f x`.
  calc
    f (D *ᵥ x) = f (∑ σ, w σ • (σ.permMatrix ℝ *ᵥ x)) := by rw [← hsum]
    _ ≤ ∑ σ, w σ • f (σ.permMatrix ℝ *ᵥ x) := by
      exact hf_convex.map_sum_le (fun σ _ => hw0 σ) (by simpa using hw1) (fun σ _ => Set.mem_univ _)
    _ = ∑ σ, w σ • f x := by
      refine Finset.sum_congr rfl ?_
      intro σ hσ
      congr 1
      rw [permMatrix_mulVec]
      exact (hf_symm σ x).symm
    _ = f x := by
      simp_rw [smul_eq_mul]
      calc
        ∑ σ, w σ * f x = (∑ σ, w σ) * f x := by rw [← Finset.sum_mul]
        _ = f x := by simp [hw1]

theorem symmetric_convex_eq_sup_diagonal_orthogonal
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : (n → ℝ) → ℝ)
    (hf_symm : ∀ (e : Equiv.Perm n) (x : n → ℝ), f x = f (fun i => x (e i)))
    (hf_convex : ConvexOn ℝ (Set.univ : Set (n → ℝ)) f)
    (X : Matrix n n ℝ)
    (hX : X.IsSymm)
    (lamX : n → ℝ)
    (hlamX : ∃ V : Matrix n n ℝ,
      V * V.transpose = 1 ∧ V.transpose * V = 1 ∧
      X = V * Matrix.diagonal lamX * V.transpose) :
    f lamX =
      sSup
        {r : ℝ |
          (∃ V : Matrix n n ℝ,
            V * V.transpose = 1 ∧ V.transpose * V = 1 ∧
            r = f (fun i => (V.transpose * X * V) i i)) ∧
          ∀ W : Matrix n n ℝ,
            W * W.transpose = 1 →
            W.transpose * W = 1 →
            f (fun i => (W.transpose * X * W) i i) ≤ r} := by
  classical
  obtain ⟨V, hVVt, hVtV, hXdiag⟩ := hlamX
  let S : Set ℝ :=
    {r : ℝ |
      (∃ V : Matrix n n ℝ,
        V * V.transpose = 1 ∧ V.transpose * V = 1 ∧
        r = f (fun i => (V.transpose * X * V) i i)) ∧
      ∀ W : Matrix n n ℝ,
        W * W.transpose = 1 →
        W.transpose * W = 1 →
        f (fun i => (W.transpose * X * W) i i) ≤ r}
  -- Every orthogonal diagonal value comes from a doubly stochastic action on `lamX`.
  have h_upper : ∀ W : Matrix n n ℝ,
      W * W.transpose = 1 →
      W.transpose * W = 1 →
      f (fun i => (W.transpose * X * W) i i) ≤ f lamX := by
    intro W hWWt hWtW
    let U : Matrix n n ℝ := V.transpose * W
    let D : Matrix n n ℝ := fun i j => U j i * U j i
    have hUUt : U * U.transpose = 1 := by
      -- Conjugating `WWᵀ = 1` by `Vᵀ` and `V` gives one orthogonality relation for `U`.
      calc
        U * U.transpose = V.transpose * (W * W.transpose) * V := by
          simp [U, Matrix.mul_assoc]
        _ = V.transpose * 1 * V := by rw [hWWt]
        _ = 1 := by simpa [Matrix.mul_assoc, hVtV]
    have hUtU : U.transpose * U = 1 := by
      -- Conjugating `VVᵀ = 1` by `Wᵀ` and `W` gives the second orthogonality relation for `U`.
      calc
        U.transpose * U = W.transpose * (V * V.transpose) * W := by
          simp [U, Matrix.mul_assoc]
        _ = W.transpose * 1 * W := by rw [hVVt]
        _ = 1 := by simpa [Matrix.mul_assoc, hWtW]
    have hD : D ∈ doublyStochastic ℝ n := by
      simpa [D] using squareEntryMatrix_mem_doublyStochastic U hUUt hUtU
    have hconj : W.transpose * X * W = U.transpose * Matrix.diagonal lamX * U := by
      -- Rewrite the orthogonal conjugate of `X` through the diagonalization witness `V`.
      simp [U, hXdiag, Matrix.mul_assoc]
    have hdiag : (fun i => (W.transpose * X * W) i i) = D *ᵥ lamX := by
      -- The diagonal is exactly the doubly stochastic image of the eigenvalue vector.
      calc
        (fun i => (W.transpose * X * W) i i)
            = fun i => (U.transpose * Matrix.diagonal lamX * U) i i := by
                funext i
                simpa using congrFun (congrFun hconj i) i
        _ = D *ᵥ lamX := by
                simpa [D] using diag_transpose_diagonal_mul_eq_squareEntry_mulVec U lamX
    calc
      f (fun i => (W.transpose * X * W) i i) = f (D *ᵥ lamX) := by rw [hdiag]
      _ ≤ f lamX := symmetric_convex_le_of_mem_doublyStochastic f hf_symm hf_convex D hD lamX
  -- The original diagonalizing matrix attains the eigenvalue vector on the diagonal.
  have hdiagV : (fun i => (V.transpose * X * V) i i) = lamX := by
    have hVV : V.transpose * X * V = Matrix.diagonal lamX := by
      -- Plug the diagonalization of `X` back into `Vᵀ X V` and simplify by orthogonality.
      calc
        V.transpose * X * V = V.transpose * (V * Matrix.diagonal lamX * V.transpose) * V := by
          rw [hXdiag]
        _ = ((V.transpose * V) * Matrix.diagonal lamX) * (V.transpose * V) := by
          simp [Matrix.mul_assoc]
        _ = Matrix.diagonal lamX := by simp [hVtV]
    funext i
    simpa using congrFun (congrFun hVV i) i
  have hmem : f lamX ∈ S := by
    -- The witness `V` both attains `f lamX` and satisfies the universal upper bound.
    refine ⟨?_, h_upper⟩
    refine ⟨V, hVVt, hVtV, ?_⟩
    rw [hdiagV]
  -- Any element of the set is squeezed between the witness value and the universal upper bound.
  have hset : S = {f lamX} := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨⟨W, hWWt, hWtW, rfl⟩, hmax⟩
      have hle : f (fun i => (W.transpose * X * W) i i) ≤ f lamX := h_upper W hWWt hWtW
      have hge : f lamX ≤ f (fun i => (W.transpose * X * W) i i) := by
        -- Compare against the distinguished witness `V`, which attains `lamX`.
        have := hmax V hVVt hVtV
        simpa [hdiagV] using this
      rw [Set.mem_singleton_iff]
      linarith
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      subst hr
      exact hmem
  -- The defining set is a singleton, so its supremum is exactly `f lamX`.
  change f lamX = sSup S
  rw [hset]
  simpa using (sSup_singleton (a := f lamX)).symm

/- [BLOCK Exercise 2.21-(c) | 28 | thm]
Let S^n denote the vector space of all n imes n real symmetric matrices. For X ∈ S^n, let
λ(X)=(λ_1(X),λ_2(X),ldots,λ_n(X)) ∈ ℝ^n denote the vector of eigenvalues of X. For a square matrix
M, let diag(M) ∈ ℝ^n denote the vector of diagonal entries of M. Let V be the set of all n imes n
orthogonal matrices V satisfying Vᵀ V = V Vᵀ = I. A permutation matrix is a matrix obtained by
permuting the rows of the identity matrix. A function f:ℝ^n o ℝ is symmetric if f(x)=f(Px) for every
permutation matrix P and every x ∈ ℝ^n. Let f:ℝ^n o ℝ be symmetric. If f is convex, show further
that the identity f(λ(X))=sup_{V∈V} figl(diag(Vᵀ X V)igr) implies that f(λ(X)) is convex in X.
-/
theorem symmetric_convex_eigenvalue_function_is_convex
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : (n → ℝ) → ℝ)
    (hf_symm : ∀ (e : Equiv.Perm n) (x : n → ℝ), f x = f (fun i => x (e i)))
    (hf_convex : ConvexOn ℝ (Set.univ : Set (n → ℝ)) f)
    (lam : Matrix n n ℝ → n → ℝ)
    (hlam : ∀ X : Matrix n n ℝ, X.IsSymm →
      ∃ V : Matrix n n ℝ,
        V * V.transpose = 1 ∧ V.transpose * V = 1 ∧
        X = V * Matrix.diagonal (lam X) * V.transpose) :
    ConvexOn ℝ
      {X : Matrix n n ℝ | X.IsSymm}
      (fun X => f (lam X)) := by
  constructor
  · intro X hX Y hY a b ha hb hab
    -- The symmetric matrices form a convex set because symmetry is preserved by scaling and addition.
    exact (hX.smul a).add (hY.smul b)
  · intro X hX Y hY a b ha hb hab
    -- Route correction: prove the convexity inequality directly from one diagonalization of
    -- `a • X + b • Y`, then compare its diagonal entries to the eigenvalue vectors of `X` and `Y`
    -- through the same doubly-stochastic majorization argument used in the previous theorem.
    set Z : Matrix n n ℝ := a • X + b • Y with hZdef
    have hZ : Z.IsSymm := by
      -- The convex combination stays inside the symmetric cone.
      rw [hZdef]
      exact (hX.smul a).add (hY.smul b)
    have h_upper :
        ∀ {M : Matrix n n ℝ}, M.IsSymm →
          ∀ W : Matrix n n ℝ,
            W * W.transpose = 1 →
            W.transpose * W = 1 →
            f (Matrix.diag (W.transpose * M * W)) ≤ f (lam M) := by
      intro M hM W hWWt hWtW
      obtain ⟨V, hVVt, hVtV, hMdiag⟩ := hlam M hM
      let U : Matrix n n ℝ := V.transpose * W
      let D : Matrix n n ℝ := fun i j => U j i * U j i
      have hUUt : U * U.transpose = 1 := by
        -- Conjugating `WWᵀ = 1` by `Vᵀ` and `V` transfers orthogonality to `U`.
        calc
          U * U.transpose = V.transpose * (W * W.transpose) * V := by
            simp [U, Matrix.mul_assoc]
          _ = V.transpose * 1 * V := by rw [hWWt]
          _ = 1 := by simp [hVtV]
      have hUtU : U.transpose * U = 1 := by
        -- Conjugating `VVᵀ = 1` by `Wᵀ` and `W` gives the second orthogonality relation.
        calc
          U.transpose * U = W.transpose * (V * V.transpose) * W := by
            simp [U, Matrix.mul_assoc]
          _ = W.transpose * 1 * W := by rw [hVVt]
          _ = 1 := by simp [hWtW]
      have hD : D ∈ doublyStochastic ℝ n := by
        -- Squared entries of an orthogonal matrix produce a doubly stochastic matrix.
        simpa [D] using squareEntryMatrix_mem_doublyStochastic U hUUt hUtU
      have hconj : W.transpose * M * W = U.transpose * Matrix.diagonal (lam M) * U := by
        -- Rewrite the orthogonal conjugate of `M` through the diagonalizing matrix from `hlam`.
        have hMconj :
            W.transpose * M * W
              = W.transpose * (V * Matrix.diagonal (lam M) * V.transpose) * W := by
          exact congrArg (fun T => W.transpose * T * W) hMdiag
        calc
          W.transpose * M * W = W.transpose * (V * Matrix.diagonal (lam M) * V.transpose) * W := hMconj
          _ = (W.transpose * V) * Matrix.diagonal (lam M) * (V.transpose * W) := by
            simp [Matrix.mul_assoc]
          _ = U.transpose * Matrix.diagonal (lam M) * U := by
            simp [U, Matrix.mul_assoc]
      have hdiag :
          Matrix.diag (W.transpose * M * W) = D *ᵥ lam M := by
        -- The diagonal entries are exactly the doubly stochastic image of `lam M`.
        calc
          Matrix.diag (W.transpose * M * W)
              = Matrix.diag (U.transpose * Matrix.diagonal (lam M) * U) := by rw [hconj]
          _ = D *ᵥ lam M := by
              simpa [Matrix.diag, D] using
                diag_transpose_diagonal_mul_eq_squareEntry_mulVec U (lam M)
      calc
        f (Matrix.diag (W.transpose * M * W)) = f (D *ᵥ lam M) := by rw [hdiag]
        _ ≤ f (lam M) :=
          symmetric_convex_le_of_mem_doublyStochastic f hf_symm hf_convex D hD (lam M)
    obtain ⟨V, hVVt, hVtV, hZdiag⟩ := hlam Z hZ
    have hdiagZ :
        Matrix.diag (V.transpose * Z * V) = lam Z := by
      have hconjZ : V.transpose * Z * V = Matrix.diagonal (lam Z) := by
        -- Multiplying the diagonalization of `Z` by `Vᵀ` and `V` recovers the diagonal matrix.
        have hZconj :
            V.transpose * Z * V
              = V.transpose * (V * Matrix.diagonal (lam Z) * V.transpose) * V := by
          exact congrArg (fun T => V.transpose * T * V) hZdiag
        calc
          V.transpose * Z * V = V.transpose * (V * Matrix.diagonal (lam Z) * V.transpose) * V := hZconj
          _ = ((V.transpose * V) * Matrix.diagonal (lam Z)) * (V.transpose * V) := by
                  simp [Matrix.mul_assoc]
          _ = Matrix.diagonal (lam Z) := by simp [hVtV]
      simpa using congrArg Matrix.diag hconjZ
    have hdiag_linear :
        Matrix.diag (V.transpose * Z * V)
          = a • Matrix.diag (V.transpose * X * V) + b • Matrix.diag (V.transpose * Y * V) := by
      -- The diagonal map respects the linear expansion of the conjugated convex combination.
      rw [hZdef]
      calc
        Matrix.diag (V.transpose * (a • X + b • Y) * V)
            = Matrix.diag (a • (V.transpose * X * V) + b • (V.transpose * Y * V)) := by
                simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
        _ = a • Matrix.diag (V.transpose * X * V) + b • Matrix.diag (V.transpose * Y * V) := by
                rw [Matrix.diag_add, Matrix.diag_smul, Matrix.diag_smul]
    have hconv_diag :
        f (a • Matrix.diag (V.transpose * X * V) + b • Matrix.diag (V.transpose * Y * V))
          ≤ a * f (Matrix.diag (V.transpose * X * V))
              + b * f (Matrix.diag (V.transpose * Y * V)) := by
      -- Convexity of `f` on all vectors applies to the diagonal vectors in this fixed basis.
      have hconv0 :=
        hf_convex.2
          (by simp : Matrix.diag (V.transpose * X * V) ∈ (Set.univ : Set (n → ℝ)))
          (by simp : Matrix.diag (V.transpose * Y * V) ∈ (Set.univ : Set (n → ℝ)))
          ha hb hab
      simpa [smul_eq_mul] using hconv0
    have hupperX : f (Matrix.diag (V.transpose * X * V)) ≤ f (lam X) := by
      -- Compare the diagonal entries of `X` in the `V` basis to its eigenvalue vector.
      exact h_upper hX V hVVt hVtV
    have hupperY : f (Matrix.diag (V.transpose * Y * V)) ≤ f (lam Y) := by
      -- The same majorization bound applies to `Y` in the same orthogonal basis.
      exact h_upper hY V hVVt hVtV
    have hscaledX :
        a * f (Matrix.diag (V.transpose * X * V)) ≤ a * f (lam X) := by
      -- Nonnegative weights preserve the upper bound after scaling.
      nlinarith
    have hscaledY :
        b * f (Matrix.diag (V.transpose * Y * V)) ≤ b * f (lam Y) := by
      -- The second scaled upper bound is identical.
      nlinarith
    simpa [smul_eq_mul] using
      (calc
        f (lam Z) = f (Matrix.diag (V.transpose * Z * V)) := by rw [hdiagZ]
        _ = f (a • Matrix.diag (V.transpose * X * V) + b • Matrix.diag (V.transpose * Y * V)) := by
            rw [hdiag_linear]
        _ ≤ a * f (Matrix.diag (V.transpose * X * V))
              + b * f (Matrix.diag (V.transpose * Y * V)) := hconv_diag
        _ ≤ a * f (lam X) + b * f (lam Y) := by linarith)

end «problem-55»
