import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-166»
/-
Let K = [ P & Aᵀ; A & 0 ], where P ∈ S_ + ^n, A ∈ ℝ^{p× n}, and rank(A) = p < n. Let N(M) = {x| Mx =
0} and R(M) denote the nullspace and range of a matrix M, respectively. Prove that the following
statements are equivalent: K is nonsingular, N(P)cap N(A) = {0}, ∀ x∈ ℝ^n, Ax = 0 and xne 0 implies
xᵀ P x > 0, Fᵀ P F succ 0 for any F∈ ℝ^{n× (n - p)} satisfying R(F) = N(A), ∃ Q ∈ S_ + ^p such that
P + Aᵀ
Q A succ 0.
-/
/-- The quadratic nonnegativity hypothesis packages into positive semidefiniteness. -/
lemma posSemidef_of_quadratic_nonneg
    {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP_symm : P.IsSymm)
    (hP_psd : ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (P.mulVec x)) :
    P.PosSemidef := by
  -- This is the standard matrix-order characterization of positive semidefiniteness.
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (by simpa using hP_symm) hP_psd

/-- Full row rank makes the transpose action injective. -/
lemma transpose_mulVec_injective_of_rank
    {n p : ℕ} (A : Matrix (Fin p) (Fin n) ℝ) (hA_rank : Matrix.rank A = p) :
    Function.Injective Aᵀ.mulVec := by
  -- The rows are linearly independent because the rank equals the number of rows.
  rw [Matrix.mulVec_injective_iff]
  rw [linearIndependent_iff_card_eq_finrank_span]
  simpa [Set.finrank, Matrix.rank_eq_finrank_span_row, Matrix.col_transpose] using hA_rank.symm

/-- Rank-nullity computes the dimension of the kernel under the full-row-rank hypothesis. -/
lemma finrank_ker_toLin'_eq
    {n p : ℕ} (A : Matrix (Fin p) (Fin n) ℝ) (hA_rank : Matrix.rank A = p) :
    Module.finrank ℝ ↥(LinearMap.ker A.toLin') = n - p := by
  -- The range has dimension `p`, so rank-nullity gives the remaining `n - p` dimensions.
  have hsum := LinearMap.finrank_range_add_finrank_ker (A.toLin')
  have hrange : Module.finrank ℝ ↥(LinearMap.range A.toLin') = p := by
    rw [Matrix.range_toLin']
    simpa [Matrix.rank_eq_finrank_span_cols] using hA_rank
  have hdomain : Module.finrank ℝ (Fin n → ℝ) = n := by
    simp
  omega

/-- A basis of `ker A` yields a matrix whose range is exactly that kernel. -/
lemma exists_kernel_parameter_matrix
    {n p : ℕ} (A : Matrix (Fin p) (Fin n) ℝ) (hA_rank : Matrix.rank A = p) :
    ∃ F0 : Matrix (Fin n) (Fin (n - p)) ℝ,
      LinearMap.range F0.toLin' = LinearMap.ker A.toLin' := by
  -- Choose a basis of the kernel indexed by `Fin (n - p)` and use its coordinate map.
  let bKer : Module.Basis (Fin (n - p)) ℝ (LinearMap.ker A.toLin') :=
    Module.finBasisOfFinrankEq ℝ (LinearMap.ker A.toLin') (finrank_ker_toLin'_eq A hA_rank)
  let f : (Fin (n - p) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    (LinearMap.ker A.toLin').subtype.comp bKer.equivFun.symm.toLinearMap
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  ext x
  constructor
  · rintro ⟨u, hu⟩
    -- Elements in the range come from the subtype map into the kernel.
    rw [show Matrix.toLin' (LinearMap.toMatrix' f) = f by simp] at hu
    rw [← hu]
    exact (LinearMap.ker A.toLin').coe_mem _
  · intro hx
    -- Every kernel vector is hit by the inverse coordinate map of the chosen basis.
    refine ⟨bKer.equivFun ⟨x, hx⟩, ?_⟩
    rw [show Matrix.toLin' (LinearMap.toMatrix' f) = f by simp]
    simp [f, bKer]

/-- A parametrization whose range is `ker A` is injective on coefficient vectors. -/
lemma kernel_parameter_injective
    {n p : ℕ} (A : Matrix (Fin p) (Fin n) ℝ) (hA_rank : Matrix.rank A = p)
    (F : Matrix (Fin n) (Fin (n - p)) ℝ)
    (hF_range : LinearMap.range F.toLin' = LinearMap.ker A.toLin') :
    Function.Injective F.mulVec := by
  -- Equal domain and range dimensions force the parametrization to have trivial kernel.
  have hrange : Module.finrank ℝ ↥(LinearMap.range F.toLin') = n - p := by
    rw [hF_range]
    simpa using finrank_ker_toLin'_eq A hA_rank
  have hsum := LinearMap.finrank_range_add_finrank_ker (F.toLin')
  have hdomain : Module.finrank ℝ (Fin (n - p) → ℝ) = n - p := by
    simp
  have hker : Module.finrank ℝ ↥(LinearMap.ker F.toLin') = 0 := by
    omega
  simpa [Matrix.toLin'_apply] using
    ((LinearMap.ker_eq_bot).mp (Submodule.finrank_eq_zero.mp hker) : Function.Injective F.toLin')

/-- Restricting a quadratic form along a matrix map preserves the expected quadratic value. -/
lemma quadratic_restriction_mulVec
    {n m : Type*} [Fintype n] [Fintype m]
    (P : Matrix n n ℝ) (F : Matrix n m ℝ) (u : m → ℝ) :
    dotProduct u ((Fᵀ * P * F).mulVec u) = dotProduct (F.mulVec u) (P.mulVec (F.mulVec u)) := by
  -- This is the standard `uᵀ(FᵀPF)u = (Fu)ᵀP(Fu)` identity.
  have hmul : (Fᵀ * P * F).mulVec u = Fᵀ.mulVec ((P * F).mulVec u) := by
    rw [Matrix.mul_assoc, Matrix.mulVec_mulVec]
  rw [hmul, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]

theorem kkt_matrix_nonsingular_iff_conditions
    {n p : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin p) (Fin n) ℝ)
    (hP_symm : P.IsSymm) (hP_psd : ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (P.mulVec x))
    (hA_rank : Matrix.rank A = p) (hpn : p < n) :
    let K := Matrix.fromBlocks P Aᵀ A (0 : Matrix (Fin p) (Fin p) ℝ)
    let cond1 : Prop := K.det ≠ 0
    let cond2 : Prop :=
      ((LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
        (LinearMap.ker A.toLin' : Submodule ℝ (Fin n → ℝ)) = ⊥)
    let cond3 : Prop :=
      ∀ x : Fin n → ℝ, A.mulVec x = 0 → x ≠ 0 → 0 < dotProduct x (P.mulVec x)
    let cond4 : Prop :=
      ∀ F : Matrix (Fin n) (Fin (n - p)) ℝ,
        LinearMap.range F.toLin' = LinearMap.ker A.toLin' →
        Matrix.PosDef (Fᵀ * P * F)
    let cond5 : Prop :=
      ∃ Q : Matrix (Fin p) (Fin p) ℝ,
        Q.IsSymm ∧
        (∀ y : Fin p → ℝ, 0 ≤ dotProduct y (Q.mulVec y)) ∧
        Matrix.PosDef (P + Aᵀ * Q * A)
    (cond1 ↔ cond2) ∧
    (cond1 ↔ cond3) ∧
    (cond1 ↔ cond4) ∧
    (cond1 ↔ cond5) := by
  dsimp
  have _ : p < n := hpn
  let K := Matrix.fromBlocks P Aᵀ A (0 : Matrix (Fin p) (Fin p) ℝ)
  have hPsemidef : P.PosSemidef := posSemidef_of_quadratic_nonneg P hP_symm hP_psd
  have hAt_inj : Function.Injective Aᵀ.mulVec := transpose_mulVec_injective_of_rank A hA_rank
  -- First compute the determinant condition in terms of `ker P ∩ ker A`.
  have h12 :
      K.det ≠ 0 ↔
        ((LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
          (LinearMap.ker A.toLin' : Submodule ℝ (Fin n → ℝ)) = ⊥) := by
    constructor
    · intro hK
      -- A vector in the intersection gives a kernel vector of the block matrix.
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hxP : P.mulVec x = 0 := by
        simpa [LinearMap.mem_ker] using hx.1
      have hxA : A.mulVec x = 0 := by
        simpa [LinearMap.mem_ker] using hx.2
      let z : Fin n ⊕ Fin p → ℝ := Sum.elim x 0
      have hzK : K.mulVec z = 0 := by
        ext i
        cases i <;>
          simp [K, z, Matrix.fromBlocks_mulVec, hxP, hxA]
      have hz0 : z = 0 := Matrix.eq_zero_of_mulVec_eq_zero (M := K) hK hzK
      ext i
      simpa [z] using congrArg (fun v => v (Sum.inl i)) hz0
    · intro hker
      -- A nontrivial block-kernel vector would produce a nonzero vector in `ker P ∩ ker A`.
      by_contra hdet0
      obtain ⟨z, hz_ne, hzK⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := K)).mpr hdet0
      let x : Fin n → ℝ := z ∘ Sum.inl
      let y : Fin p → ℝ := z ∘ Sum.inr
      have hzBlocks :
          Sum.elim (P.mulVec x + Aᵀ.mulVec y) (A.mulVec x) = 0 := by
        simpa [K, x, y, Matrix.fromBlocks_mulVec] using hzK
      have htop : P.mulVec x + Aᵀ.mulVec y = 0 := by
        ext i
        simpa using congrArg (fun v => v (Sum.inl i)) hzBlocks
      have hbottom : A.mulVec x = 0 := by
        ext i
        simpa using congrArg (fun v => v (Sum.inr i)) hzBlocks
      have hcross : dotProduct x (Aᵀ.mulVec y) = 0 := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hbottom, zero_dotProduct]
      have hquad_zero : dotProduct x (P.mulVec x) = 0 := by
        have hdot := congrArg (fun v => dotProduct x v) htop
        simpa [dotProduct_add, hcross] using hdot
      have hxP : P.mulVec x = 0 := by
        exact (hPsemidef.dotProduct_mulVec_zero_iff x).mp (by simpa using hquad_zero)
      have hx_ne : x ≠ 0 := by
        intro hx0
        have hy0 : y = 0 := by
          apply hAt_inj
          simpa [x, hx0] using htop
        apply hz_ne
        funext i
        cases i with
        | inl i =>
            change x i = 0
            simp [hx0]
        | inr i =>
            change y i = 0
            simp [hy0]
      have hx_mem :
          x ∈ ((LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
            (LinearMap.ker A.toLin' : Submodule ℝ (Fin n → ℝ))) := by
        refine ⟨?_, ?_⟩
        · simpa [LinearMap.mem_ker] using hxP
        · simpa [LinearMap.mem_ker] using hbottom
      have hx_zero : x = 0 := by
        have : x ∈ (⊥ : Submodule ℝ (Fin n → ℝ)) := by
          simpa [hker] using hx_mem
        simpa using this
      exact hx_ne hx_zero
  -- Next translate the trivial intersection into strict positivity on `ker A \ {0}`.
  have h23 :
      (((LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
          (LinearMap.ker A.toLin' : Submodule ℝ (Fin n → ℝ)) = ⊥) ↔
        ∀ x : Fin n → ℝ, A.mulVec x = 0 → x ≠ 0 → 0 < dotProduct x (P.mulVec x)) := by
    constructor
    · intro hker x hxA hx_ne
      -- Zero quadratic value would force `x` into `ker P ∩ ker A`, contradicting `x ≠ 0`.
      have hnonneg : 0 ≤ dotProduct x (P.mulVec x) := hP_psd x
      have hnonzero : dotProduct x (P.mulVec x) ≠ 0 := by
        intro hzero
        have hxP : P.mulVec x = 0 := by
          exact (hPsemidef.dotProduct_mulVec_zero_iff x).mp (by simpa using hzero)
        have hx_mem :
            x ∈ ((LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
              (LinearMap.ker A.toLin' : Submodule ℝ (Fin n → ℝ))) := by
          refine ⟨?_, ?_⟩
          · simpa [LinearMap.mem_ker] using hxP
          · simpa [LinearMap.mem_ker] using hxA
        have hx_zero : x = 0 := by
          have : x ∈ (⊥ : Submodule ℝ (Fin n → ℝ)) := by
            simpa [hker] using hx_mem
          simpa using this
        exact hx_ne hx_zero
      exact lt_of_le_of_ne hnonneg (Ne.symm hnonzero)
    · intro hpos
      -- A nonzero vector in the intersection would violate strict positivity on the kernel.
      rw [Submodule.eq_bot_iff]
      intro x hx
      by_contra hx_ne
      have hxP : P.mulVec x = 0 := by
        simpa [LinearMap.mem_ker] using hx.1
      have hxA : A.mulVec x = 0 := by
        simpa [LinearMap.mem_ker] using hx.2
      have : 0 < (0 : ℝ) := by
        simpa [hxP] using hpos x hxA hx_ne
      exact (lt_irrefl 0) this
  -- Then compare positivity on `ker A` with positivity of every kernel parametrization.
  have h34 :
      (∀ x : Fin n → ℝ, A.mulVec x = 0 → x ≠ 0 → 0 < dotProduct x (P.mulVec x)) ↔
        ∀ F : Matrix (Fin n) (Fin (n - p)) ℝ,
          LinearMap.range F.toLin' = LinearMap.ker A.toLin' →
          Matrix.PosDef (Fᵀ * P * F) := by
    constructor
    · intro hpos F hF_range
      -- Positivity on `ker A` transfers to the pulled-back quadratic form along any parametrization.
      refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
      · simpa using Matrix.isHermitian_conjTranspose_mul_mul F (by simpa using hP_symm)
      · intro u hu
        have hFinj : Function.Injective F.mulVec := kernel_parameter_injective A hA_rank F hF_range
        have hFu_ne : F.mulVec u ≠ 0 := by
          intro hFu
          apply hu
          exact hFinj (by simpa using hFu)
        have hFu_ker : A.mulVec (F.mulVec u) = 0 := by
          have : F.mulVec u ∈ LinearMap.range F.toLin' := ⟨u, rfl⟩
          rw [hF_range] at this
          simpa [LinearMap.mem_ker] using this
        simpa [quadratic_restriction_mulVec P F u] using hpos (F.mulVec u) hFu_ker hFu_ne
    · intro hrestrict x hxA hx_ne
      -- Choose one parametrization of `ker A`, pull `x` back to coefficient space, and transfer positivity.
      obtain ⟨F0, hF0_range⟩ := exists_kernel_parameter_matrix A hA_rank
      have hF0inj : Function.Injective F0.mulVec := kernel_parameter_injective A hA_rank F0 hF0_range
      have hx_range : x ∈ LinearMap.range F0.toLin' := by
        rw [hF0_range]
        simpa [LinearMap.mem_ker] using hxA
      obtain ⟨u, rfl⟩ := hx_range
      have hu_ne : u ≠ 0 := by
        intro hu0
        apply hx_ne
        simp [hu0]
      have hpos_u := (hrestrict F0 hF0_range).dotProduct_mulVec_pos hu_ne
      simpa [quadratic_restriction_mulVec P F0 u] using hpos_u
  -- Finally compare positivity on `ker A` with adding the explicit quadratic penalty `Q = 1`.
  have h35 :
      (∀ x : Fin n → ℝ, A.mulVec x = 0 → x ≠ 0 → 0 < dotProduct x (P.mulVec x)) ↔
        ∃ Q : Matrix (Fin p) (Fin p) ℝ,
          Q.IsSymm ∧
          (∀ y : Fin p → ℝ, 0 ≤ dotProduct y (Q.mulVec y)) ∧
          Matrix.PosDef (P + Aᵀ * Q * A) := by
    constructor
    · intro hpos
      refine ⟨1, ?_, ?_, ?_⟩
      · -- The identity penalty matrix is symmetric.
        exact Matrix.isSymm_one
      · -- Its quadratic form is the Euclidean norm square.
        intro y
        simpa using
          (Matrix.PosSemidef.one.dotProduct_mulVec_nonneg y :
            0 ≤ dotProduct y ((1 : Matrix (Fin p) (Fin p) ℝ).mulVec y))
      · -- Route correction: instead of searching for a general `Q`, use the explicit witness `Q = 1`.
        refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
        · have hPherm : P.IsHermitian := by
            simpa using hP_symm
          have hAherm : (Aᵀ * (1 : Matrix (Fin p) (Fin p) ℝ) * A).IsHermitian := by
            simpa using Matrix.isHermitian_conjTranspose_mul_mul A
              ((Matrix.PosDef.one : Matrix.PosDef (1 : Matrix (Fin p) (Fin p) ℝ)).1)
          exact hPherm.add hAherm
        · intro x hx_ne
          have hPnonneg : 0 ≤ dotProduct x (P.mulVec x) := hP_psd x
          have hAnorm_nonneg : 0 ≤ dotProduct (A.mulVec x) (A.mulVec x) := by
            simpa using dotProduct_self_star_nonneg (A.mulVec x)
          have hAquad :
              dotProduct x ((Aᵀ * (1 : Matrix (Fin p) (Fin p) ℝ) * A).mulVec x) =
                dotProduct (A.mulVec x) (A.mulVec x) := by
            simpa using quadratic_restriction_mulVec (1 : Matrix (Fin p) (Fin p) ℝ) A x
          have hquad :
              dotProduct x ((P + Aᵀ * (1 : Matrix (Fin p) (Fin p) ℝ) * A).mulVec x) =
                dotProduct x (P.mulVec x) + dotProduct (A.mulVec x) (A.mulVec x) := by
            rw [Matrix.add_mulVec, dotProduct_add, hAquad]
          have hquad' :
              star x ⬝ᵥ (P + Aᵀ * (1 : Matrix (Fin p) (Fin p) ℝ) * A).mulVec x =
                dotProduct x (P.mulVec x) + dotProduct (A.mulVec x) (A.mulVec x) := by
            simpa using hquad
          by_cases hxA : A.mulVec x = 0
          · have hPx : 0 < dotProduct x (P.mulVec x) := hpos x hxA hx_ne
            have hAnorm_zero : dotProduct (A.mulVec x) (A.mulVec x) = 0 := by
              simp [hxA]
            rw [hquad', hAnorm_zero]
            simpa using hPx
          · have hAnorm_ne : dotProduct (A.mulVec x) (A.mulVec x) ≠ 0 := by
              intro hzero
              exact hxA ((dotProduct_self_eq_zero).mp (by simpa using hzero))
            have hAnorm_pos : 0 < dotProduct (A.mulVec x) (A.mulVec x) :=
              lt_of_le_of_ne hAnorm_nonneg (Ne.symm hAnorm_ne)
            rw [hquad']
            linarith
    · rintro ⟨Q, hQ_symm, hQ_psd, hposQ⟩ x hxA hx_ne
      -- On `ker A`, the penalty term vanishes and only the original quadratic form remains.
      have hposx := hposQ.dotProduct_mulVec_pos hx_ne
      have hpenalty :
          dotProduct x ((Aᵀ * Q * A).mulVec x) = 0 := by
        rw [quadratic_restriction_mulVec Q A x]
        simp [hxA]
      have hquad :
          dotProduct x ((P + Aᵀ * Q * A).mulVec x) = dotProduct x (P.mulVec x) := by
        rw [Matrix.add_mulVec, dotProduct_add, hpenalty, add_zero]
      simpa [hquad] using hposx
  -- Package the four equivalences by using `cond3` as the hub.
  simpa [K] using
    (show
      (K.det ≠ 0 ↔
          ((LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
            (LinearMap.ker A.toLin' : Submodule ℝ (Fin n → ℝ)) = ⊥)) ∧
        ((K.det ≠ 0) ↔
          ∀ x : Fin n → ℝ, A.mulVec x = 0 → x ≠ 0 → 0 < dotProduct x (P.mulVec x)) ∧
        ((K.det ≠ 0) ↔
          ∀ F : Matrix (Fin n) (Fin (n - p)) ℝ,
            LinearMap.range F.toLin' = LinearMap.ker A.toLin' →
            Matrix.PosDef (Fᵀ * P * F)) ∧
        ((K.det ≠ 0) ↔
          ∃ Q : Matrix (Fin p) (Fin p) ℝ,
            Q.IsSymm ∧
            (∀ y : Fin p → ℝ, 0 ≤ dotProduct y (Q.mulVec y)) ∧
            Matrix.PosDef (P + Aᵀ * Q * A))
      from
        ⟨h12, h12.trans h23, h12.trans (h23.trans h34), h12.trans (h23.trans h35)⟩)

end «problem-166»
