import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-34»
/- [BLOCK Exercise 3.33-(a) | 31 | defn]
For a constrained optimization problem, a point x is feasible if it satisfies all the constraints.
-/
def IsFeasible {α : Type*} (constraints : Set (α → Prop)) (x : α) : Prop :=
  ∀ c ∈ constraints, c x

/- [BLOCK Exercise 3.33-(a) | 32 | opt_prob]
A semidefinite program is an optimization problem of the form
aligned
minimizequad & tr(CX) ;
subject\ toquad & tr(A_iX)=bᵢ,quad i=1,ldots,m,;
& Xsucceq 0,
aligned
where X ∈ S^n, C,A₁,ldots,Aₘ ∈ S^n, and b₁,
ldots,bₘ ∈ ℝ.
-/
structure SemidefiniteProgram (n m : ℕ) where
  C : Matrix (Fin n) (Fin n) ℝ
  A : Fin m → Matrix (Fin n) (Fin n) ℝ
  b : Fin m → ℝ
  C_symm : C.IsSymm
  A_symm : ∀ i, (A i).IsSymm

def SemidefiniteProgram.isFeasible {n m : ℕ} (p : SemidefiniteProgram n m)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsSymm ∧
  Matrix.PosSemidef X ∧
  ∀ i : Fin m, Matrix.trace (p.A i * X) = p.b i

def SemidefiniteProgram.objective {n m : ℕ} (p : SemidefiniteProgram n m)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (p.C * X)

/- [BLOCK Exercise 3.33-(a) | 33 | thm]
Let S^n be the set of real symmetric n × n matrices, and for M ∈ S^n, let M succeq 0 mean that M is
positive semidefinite. Consider the semidefinite program alignedminimizequad & tr(CX) ; subject\
toquad & tr(A_iX)=bᵢ,quad i=1,ldots,m,; & Xsucceq 0,aligned where X ∈ S^n, C,A₁,ldots,Aₘ ∈ S^n, and
b₁,ldots,bₘ ∈ ℝ. Let hat X ∈ S^n be a feasible point of rank r, and suppose that hat X=[Q₁ &
Q₂][Lambda_1 & 0; 0 & 0][Q₁ & Q₂]ᵀ, where [Q₁ & Q₂] is an orthogonal n × n matrix, Q₁ has r columns,
Q₂ has n-r columns, and Lambda_1 is a diagonal r × r matrix with strictly positive diagonal entries.
Show that a matrix V ∈ S^n satisfies tr(A_iV)=0 quad (i=1,ldots,m), hat X+Vsucceq 0, hat X-Vsucceq 0
if and only if there exists Y ∈ S^r such that V=Q_1YQ_1ᵀ, and tr(Q_1ᵀA_iQ_1Y)=0 quad (i=1,ldots,m),
Lambda_1+Ysucceq 0, Lambda_1-Ysucceq 0.
-/
theorem sdp_feasible_perturbation_iff_compressed
    {n m r : ℕ}
    (p : SemidefiniteProgram n m)
    (Xhat V : Matrix (Fin n) (Fin n) ℝ)
    (Q₁ : Matrix (Fin n) (Fin r) ℝ)
    (Q₂ : Matrix (Fin n) (Fin (n - r)) ℝ)
    (Λ₁ : Matrix (Fin r) (Fin r) ℝ)
    (hV_symm : V.IsSymm)
    (hQ₁_orthonormal : Q₁.transpose * Q₁ = 1)
    (hQ₂_orthonormal : Q₂.transpose * Q₂ = 1)
    (hQ₁Q₂_orthogonal : Q₁.transpose * Q₂ = 0)
    (hQ₂Q₁_orthogonal : Q₂.transpose * Q₁ = 0)
    (h_complete : Q₁ * Q₁.transpose + Q₂ * Q₂.transpose = 1)
    (hΛ₁_diag : Λ₁.IsDiag)
    (hΛ₁_pos : ∀ i : Fin r, 0 < Λ₁ i i)
    (hXhat_decomp : Xhat = Q₁ * Λ₁ * Q₁.transpose)
    (hXhat_feas : p.isFeasible Xhat) :
    ((∀ i : Fin m, Matrix.trace (p.A i * V) = 0) ∧
      Matrix.PosSemidef (Xhat + V) ∧
      Matrix.PosSemidef (Xhat - V)) ↔
    ∃ Y : Matrix (Fin r) (Fin r) ℝ,
      Y.IsSymm ∧
      V = Q₁ * Y * Q₁.transpose ∧
      (∀ i : Fin m, Matrix.trace (Q₁.transpose * p.A i * Q₁ * Y) = 0) ∧
      Matrix.PosSemidef (Λ₁ + Y) ∧
      Matrix.PosSemidef (Λ₁ - Y) := by
  -- The trace constraint is the same before and after compression by `Q₁`.
  have htrace_cycle :
      ∀ i : Fin m, ∀ Y : Matrix (Fin r) (Fin r) ℝ,
        Matrix.trace (p.A i * (Q₁ * Y * Q₁.transpose)) =
          Matrix.trace (Q₁.transpose * p.A i * Q₁ * Y) := by
    intro i Y
    calc
      Matrix.trace (p.A i * (Q₁ * Y * Q₁.transpose))
          = Matrix.trace ((p.A i * Q₁) * Y * Q₁.transpose) := by
              simp [Matrix.mul_assoc]
      _ = Matrix.trace (Q₁.transpose * (p.A i * Q₁) * Y) := by
            rw [Matrix.trace_mul_cycle (p.A i * Q₁) Y Q₁.transpose]
      _ = Matrix.trace (Q₁.transpose * p.A i * Q₁ * Y) := by
            simp [Matrix.mul_assoc]
  constructor
  · rintro ⟨htraceV, hplus, hminus⟩
    -- The `Q₂`-directions lie in the kernel of `Xhat`.
    have hXhatQ₂ : Xhat * Q₂ = 0 := by
      calc
        Xhat * Q₂ = (Q₁ * Λ₁ * Q₁.transpose) * Q₂ := by rw [hXhat_decomp]
        _ = Q₁ * Λ₁ * (Q₁.transpose * Q₂) := by simp [Matrix.mul_assoc]
        _ = 0 := by simp [hQ₁Q₂_orthogonal]
    -- Testing the PSD inequalities on the `Q₂`-range forces `V` to vanish there.
    have hVQ₂ : V * Q₂ = 0 := by
      ext i j
      let x : Fin n → ℝ := Q₂ *ᵥ (Pi.single j 1)
      have hxhat_zero : Xhat *ᵥ x = 0 := by
        dsimp [x]
        simpa [Matrix.mulVec_mulVec] using congrArg (fun M => M *ᵥ (Pi.single j 1)) hXhatQ₂
      have hplus_nonneg : 0 ≤ star x ⬝ᵥ ((Xhat + V) *ᵥ x) :=
        hplus.dotProduct_mulVec_nonneg x
      have hminus_nonneg : 0 ≤ star x ⬝ᵥ ((Xhat - V) *ᵥ x) :=
        hminus.dotProduct_mulVec_nonneg x
      have hquad_nonneg : 0 ≤ star x ⬝ᵥ (V *ᵥ x) := by
        simpa [Matrix.add_mulVec, hxhat_zero] using hplus_nonneg
      have hneg_nonneg : 0 ≤ star x ⬝ᵥ ((-V) *ᵥ x) := by
        simpa [sub_eq_add_neg, Matrix.add_mulVec, hxhat_zero] using hminus_nonneg
      have hquad_nonpos : 0 ≤ -(star x ⬝ᵥ (V *ᵥ x)) := by
        simpa [Matrix.neg_mulVec] using hneg_nonneg
      have hquad_zero : star x ⬝ᵥ (V *ᵥ x) = 0 := by
        linarith
      have hplus_zero : star x ⬝ᵥ ((Xhat + V) *ᵥ x) = 0 := by
        simpa [Matrix.add_mulVec, hxhat_zero] using hquad_zero
      have hVx_zero : V *ᵥ x = 0 := by
        have hsum_zero : (Xhat + V) *ᵥ x = 0 :=
          (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hplus x).mp hplus_zero
        simpa [Matrix.add_mulVec, hxhat_zero] using hsum_zero
      have hi : (V *ᵥ x) i = 0 := by simpa using congrFun hVx_zero i
      simpa [x, Matrix.mul_apply, Matrix.mulVec_single_one] using hi
    -- Symmetry lets us turn the right-kernel statement into a left-kernel statement.
    have hQ₂V : Q₂.transpose * V = 0 := by
      simpa [Matrix.transpose_mul, hV_symm.eq] using congrArg Matrix.transpose hVQ₂
    -- The completeness relation shows that `V` is supported entirely on the `Q₁`-block.
    have hQ₂_left : Q₂ * Q₂.transpose * V = 0 := by
      calc
        Q₂ * Q₂.transpose * V = Q₂ * (Q₂.transpose * V) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hQ₂V, Matrix.mul_zero]
    have hQ₂_right : V * (Q₂ * Q₂.transpose) = 0 := by
      calc
        V * (Q₂ * Q₂.transpose) = (V * Q₂) * Q₂.transpose := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hVQ₂, Matrix.zero_mul]
    have hV_left : V = (Q₁ * Q₁.transpose) * V := by
      have h := congrArg (fun M => M * V) h_complete
      simpa [Matrix.add_mul, Matrix.mul_assoc, hQ₂_left] using h.symm
    have hV_right : V = V * (Q₁ * Q₁.transpose) := by
      have h := congrArg (fun M => V * M) h_complete
      simpa [Matrix.mul_add, Matrix.mul_assoc, hQ₂_right] using h.symm
    have hV_eq_raw : V = Q₁ * (Q₁.transpose * V * Q₁) * Q₁.transpose := by
      calc
        V = (Q₁ * Q₁.transpose) * V := hV_left
        _ = (Q₁ * Q₁.transpose) * (V * (Q₁ * Q₁.transpose)) := by
              exact congrArg (fun M => (Q₁ * Q₁.transpose) * M) hV_right
        _ = Q₁ * (Q₁.transpose * V * Q₁) * Q₁.transpose := by
              simp [Matrix.mul_assoc]
    let Y : Matrix (Fin r) (Fin r) ℝ := Q₁.transpose * V * Q₁
    have hV_eq : V = Q₁ * Y * Q₁.transpose := by
      simpa [Y] using hV_eq_raw
    have hY_symm : Y.IsSymm := by
      -- Compression by `Q₁` preserves symmetry.
      simpa [Matrix.IsSymm, Y, Matrix.transpose_mul, Matrix.mul_assoc, hV_symm.eq]
    have hXhat_compressed : Q₁.transpose * Xhat * Q₁ = Λ₁ := by
      calc
        Q₁.transpose * Xhat * Q₁ = Q₁.transpose * (Q₁ * Λ₁ * Q₁.transpose) * Q₁ := by
          rw [hXhat_decomp]
        _ = (Q₁.transpose * Q₁) * Λ₁ * (Q₁.transpose * Q₁) := by
              simp [Matrix.mul_assoc]
        _ = Λ₁ := by
              simp [hQ₁_orthonormal]
    have hplus_compressed : Matrix.PosSemidef (Λ₁ + Y) := by
      -- Congruence with `Q₁ᵀ` transfers PSD from the full space to the compressed block.
      have hcompressed : Matrix.PosSemidef (Q₁.transpose * (Xhat + V) * Q₁) :=
        Matrix.PosSemidef.conjTranspose_mul_mul_same hplus Q₁
      have hrewrite : Q₁.transpose * (Xhat + V) * Q₁ = Λ₁ + Y := by
        calc
          Q₁.transpose * (Xhat + V) * Q₁
              = Q₁.transpose * Xhat * Q₁ + Q₁.transpose * V * Q₁ := by
                  simp [Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
          _ = Λ₁ + Y := by
                simpa [Y] using congrArg (fun M => M + Q₁.transpose * V * Q₁) hXhat_compressed
      simpa [hrewrite] using hcompressed
    have hminus_compressed : Matrix.PosSemidef (Λ₁ - Y) := by
      -- The same congruence argument works for `Xhat - V`.
      have hcompressed : Matrix.PosSemidef (Q₁.transpose * (Xhat - V) * Q₁) :=
        Matrix.PosSemidef.conjTranspose_mul_mul_same hminus Q₁
      have hrewrite : Q₁.transpose * (Xhat - V) * Q₁ = Λ₁ - Y := by
        calc
          Q₁.transpose * (Xhat - V) * Q₁
              = Q₁.transpose * Xhat * Q₁ - Q₁.transpose * V * Q₁ := by
                  simp [sub_eq_add_neg, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
          _ = Λ₁ - Y := by
                simpa [Y] using congrArg (fun M => M - Q₁.transpose * V * Q₁) hXhat_compressed
      simpa [hrewrite] using hcompressed
    refine ⟨Y, hY_symm, hV_eq, ?_, hplus_compressed, hminus_compressed⟩
    intro i
    calc
      Matrix.trace (Q₁.transpose * p.A i * Q₁ * Y)
          = Matrix.trace (p.A i * (Q₁ * Y * Q₁.transpose)) := by
              symm
              exact htrace_cycle i Y
      _ = Matrix.trace (p.A i * V) := by rw [hV_eq]
      _ = 0 := htraceV i
  · rintro ⟨Y, hY_symm, hV_eq, htraceY, hplusY, hminusY⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      calc
        Matrix.trace (p.A i * V) = Matrix.trace (p.A i * (Q₁ * Y * Q₁.transpose)) := by
          rw [hV_eq]
        _ = Matrix.trace (Q₁.transpose * p.A i * Q₁ * Y) := htrace_cycle i Y
        _ = 0 := htraceY i
    · -- Lifting the compressed PSD condition back through `Q₁` recovers `Xhat + V ⪰ 0`.
      have hrewrite : Xhat + V = Q₁ * (Λ₁ + Y) * Q₁.transpose := by
        rw [hXhat_decomp, hV_eq]
        simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
      rw [hrewrite]
      simpa using hplusY.mul_mul_conjTranspose_same Q₁
    · -- The same lifting argument gives `Xhat - V ⪰ 0`.
      have hrewrite : Xhat - V = Q₁ * (Λ₁ - Y) * Q₁.transpose := by
        rw [hXhat_decomp, hV_eq]
        simp [sub_eq_add_neg, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
      rw [hrewrite]
      simpa using hminusY.mul_mul_conjTranspose_same Q₁

end «problem-34»
