import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped MatrixOrder
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-100»

/- [BLOCK Exercise 3.37 | 18 | defn]
For a function f : ℝ^m → ℝ cup {+∞}, the convex conjugate f* : ℝ^m → ℝ cup {+∞} is defined by
f*(y) = sup_{x ∈ ℝ^m} (langle y, x rangle - f(x)).
-/
open scoped Real

def convexConjugate {m : ℕ} (f : (Fin m → ℝ) → EReal) : (Fin m → ℝ) → EReal :=
  fun y => sSup (Set.range fun x : Fin m → ℝ => ((∑ i, y i * x i : ℝ) : EReal) - f x)

/-- The `2 × 2` skew matrix witnessing that the claimed domain equality is too small. -/
def skewWitness : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The witness is skew-symmetric, so its skew part is nontrivial. -/
lemma skewWitness_transpose : skewWitnessᵀ = -skewWitness := by
  -- Check the four entries directly to identify the witness as skew-symmetric.
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewWitness]

/-- Negating the witness does not make it symmetric. -/
lemma not_isSymm_neg_skewWitness : ¬ (-skewWitness).IsSymm := by
  -- Evaluating the symmetry relation on the off-diagonal entries produces `1 = -1`.
  intro h
  have h01 := h.apply 0 1
  norm_num [skewWitness] at h01

/-- A skew-symmetric matrix has zero trace pairing against any symmetric matrix. -/
lemma trace_mul_eq_zero_of_transpose_eq_neg {n : Type} [Fintype n]
    {X Y : Matrix n n ℝ} (hY : Yᵀ = -Y) (hX : X.IsSymm) : Matrix.trace (Y * X) = 0 := by
  -- Rewrite the trace through transpose and cyclicity to expose the sign change.
  have htrace : Matrix.trace (Y * X) = -Matrix.trace (Y * X) := calc
    Matrix.trace (Y * X) = Matrix.trace ((Y * X)ᵀ) := by rw [Matrix.trace_transpose]
    _ = Matrix.trace (Xᵀ * Yᵀ) := by simp [Matrix.transpose_mul]
    _ = Matrix.trace (X * (-Y)) := by rw [hX.eq, hY]
    _ = Matrix.trace ((-Y) * X) := Matrix.trace_mul_comm _ _
    _ = -Matrix.trace (Y * X) := by simp
  linarith

/-- The skew witness still lies in the finiteness domain because the trace term vanishes. -/
lemma skewWitness_mem_leftDomain :
    skewWitness ∈
      {Y : Matrix (Fin 2) (Fin 2) ℝ |
        sSup (Set.range fun X : {X : Matrix (Fin 2) (Fin 2) ℝ // X.IsSymm ∧ X.PosDef} =>
          (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
            (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤} := by
  change sSup
      (Set.range fun X : {X : Matrix (Fin 2) (Fin 2) ℝ // X.IsSymm ∧ X.PosDef} =>
        (((Matrix.trace (skewWitness * X.1)) : ℝ) : EReal) -
          (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤
  -- The displayed supremum is bounded above by `0`, hence it is finite.
  have hsSup_le :
      sSup
          (Set.range fun X : {X : Matrix (Fin 2) (Fin 2) ℝ // X.IsSymm ∧ X.PosDef} =>
            (((Matrix.trace (skewWitness * X.1)) : ℝ) : EReal) -
              (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) ≤ 0 := by
    refine sSup_le ?_
    rintro _ ⟨X, rfl⟩
    change (((Matrix.trace (skewWitness * X.1)) : ℝ) : EReal) -
        (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal) ≤ 0
    -- The skew witness contributes no trace against symmetric positive definite inputs.
    have htraceY : Matrix.trace (skewWitness * X.1) = 0 :=
      trace_mul_eq_zero_of_transpose_eq_neg skewWitness_transpose X.2.1
    -- The inverse of a positive definite matrix is positive definite, so its trace is positive.
    have htraceInvPos : 0 < Matrix.trace (X.1⁻¹) :=
      Matrix.PosDef.trace_pos (Matrix.PosDef.inv X.2.2)
    rw [htraceY]
    have hnonneg : (0 : EReal) ≤ (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal) := by
      exact_mod_cast le_of_lt htraceInvPos
    exact (EReal.sub_nonpos).2 hnonneg
  exact lt_of_le_of_lt hsSup_le (by simp : (0 : EReal) < ⊤)

/-- The claimed domain equality already fails for the `2 × 2` skew witness. -/
lemma domain_equality_false_Fin2 :
    ¬ ({Y : Matrix (Fin 2) (Fin 2) ℝ |
        sSup (Set.range fun X : {X : Matrix (Fin 2) (Fin 2) ℝ // X.IsSymm ∧ X.PosDef} =>
          (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
            (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤} =
      {Y : Matrix (Fin 2) (Fin 2) ℝ | (-Y).IsSymm ∧ (-Y).PosSemidef}) := by
  -- Move the witness across the alleged equality and then contradict symmetry on `-skewWitness`.
  intro hEq
  have hmemLeft :
      skewWitness ∈
        {Y : Matrix (Fin 2) (Fin 2) ℝ |
          sSup (Set.range fun X : {X : Matrix (Fin 2) (Fin 2) ℝ // X.IsSymm ∧ X.PosDef} =>
            (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
              (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤} :=
    skewWitness_mem_leftDomain
  have hmemRight :
      skewWitness ∈ {Y : Matrix (Fin 2) (Fin 2) ℝ | (-Y).IsSymm ∧ (-Y).PosSemidef} := by
    rw [hEq] at hmemLeft
    exact hmemLeft
  exact not_isSymm_neg_skewWitness hmemRight.1

/-- The theorem's conjunction is already inconsistent after specializing to `Fin 2`. -/
lemma not_convexConjugate_trace_inv_eq_negTwo_trace_sqrt_Fin2 :
    ¬ ((∀ Y : Matrix (Fin 2) (Fin 2) ℝ,
        ∀ _hY : (-Y).IsSymm ∧ (-Y).PosSemidef,
          sSup (Set.range fun X : {X : Matrix (Fin 2) (Fin 2) ℝ // X.IsSymm ∧ X.PosDef} =>
            (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
              (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) =
            (((-2 : ℝ) * Matrix.trace (CFC.sqrt (-Y))) : EReal)) ∧
      ({Y : Matrix (Fin 2) (Fin 2) ℝ |
          sSup (Set.range fun X : {X : Matrix (Fin 2) (Fin 2) ℝ // X.IsSymm ∧ X.PosDef} =>
            (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
              (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤} =
        {Y : Matrix (Fin 2) (Fin 2) ℝ | (-Y).IsSymm ∧ (-Y).PosSemidef})) := by
  intro h
  -- The value formula is irrelevant here; the second conjunct is the refuted domain equality.
  exact domain_equality_false_Fin2 h.2

/-- The advertised all-dimensions statement is false because its `Fin 2` specialization is false. -/
lemma not_convexConjugate_trace_inv_eq_negTwo_trace_sqrt_all_dims :
    ¬ (∀ {n : Type} [Fintype n] [DecidableEq n],
        (∀ Y : Matrix n n ℝ, ∀ _hY : (-Y).IsSymm ∧ (-Y).PosSemidef,
          sSup (Set.range fun X : {X : Matrix n n ℝ // X.IsSymm ∧ X.PosDef} =>
            (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
              (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) =
            (((-2 : ℝ) * Matrix.trace (CFC.sqrt (-Y))) : EReal)) ∧
        ({Y : Matrix n n ℝ |
            sSup (Set.range fun X : {X : Matrix n n ℝ // X.IsSymm ∧ X.PosDef} =>
              (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
                (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤} =
          {Y : Matrix n n ℝ | (-Y).IsSymm ∧ (-Y).PosSemidef})) := by
  intro h
  -- Specialize the claimed theorem to `Fin 2`, where the file already contains a counterexample.
  have hFin2 :
      (∀ Y : Matrix (Fin 2) (Fin 2) ℝ, ∀ _hY : (-Y).IsSymm ∧ (-Y).PosSemidef,
        sSup (Set.range fun X : {X : Matrix (Fin 2) (Fin 2) ℝ // X.IsSymm ∧ X.PosDef} =>
          (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
            (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) =
          (((-2 : ℝ) * Matrix.trace (CFC.sqrt (-Y))) : EReal)) ∧
      ({Y : Matrix (Fin 2) (Fin 2) ℝ |
          sSup (Set.range fun X : {X : Matrix (Fin 2) (Fin 2) ℝ // X.IsSymm ∧ X.PosDef} =>
            (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
              (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤} =
        {Y : Matrix (Fin 2) (Fin 2) ℝ | (-Y).IsSymm ∧ (-Y).PosSemidef}) :=
    h (n := Fin 2)
  -- Route correction: the failure is the theorem statement itself, not a missing proof step.
  exact not_convexConjugate_trace_inv_eq_negTwo_trace_sqrt_Fin2 hFin2

/-- Any completed proof of the advertised theorem would contradict the `Fin 2` counterexample. -/
lemma convexConjugate_trace_inv_eq_negTwo_trace_sqrt_conflict
    (h :
      ∀ {n : Type} [Fintype n] [DecidableEq n],
        (∀ Y : Matrix n n ℝ, ∀ _hY : (-Y).IsSymm ∧ (-Y).PosSemidef,
          sSup (Set.range fun X : {X : Matrix n n ℝ // X.IsSymm ∧ X.PosDef} =>
            (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
              (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) =
            (((-2 : ℝ) * Matrix.trace (CFC.sqrt (-Y))) : EReal)) ∧
        ({Y : Matrix n n ℝ |
            sSup (Set.range fun X : {X : Matrix n n ℝ // X.IsSymm ∧ X.PosDef} =>
              (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
                (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤} =
          {Y : Matrix n n ℝ | (-Y).IsSymm ∧ (-Y).PosSemidef})) :
    False := by
  -- Route correction: specialize the alleged universal theorem to `Fin 2` instead of
  -- continuing the doomed search for a proof of the false domain equality.
  have hAll :
      ∀ {n : Type} [Fintype n] [DecidableEq n],
        (∀ Y : Matrix n n ℝ, ∀ _hY : (-Y).IsSymm ∧ (-Y).PosSemidef,
          sSup (Set.range fun X : {X : Matrix n n ℝ // X.IsSymm ∧ X.PosDef} =>
            (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
              (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) =
            (((-2 : ℝ) * Matrix.trace (CFC.sqrt (-Y))) : EReal)) ∧
        ({Y : Matrix n n ℝ |
            sSup (Set.range fun X : {X : Matrix n n ℝ // X.IsSymm ∧ X.PosDef} =>
              (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
                (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤} =
          {Y : Matrix n n ℝ | (-Y).IsSymm ∧ (-Y).PosSemidef}) :=
    h
  -- The previously established `Fin 2` witness packages the contradiction.
  exact not_convexConjugate_trace_inv_eq_negTwo_trace_sqrt_all_dims hAll

/- [BLOCK Exercise 3.37 | 19 | thm]
Let S_{++}^n be the set of n × n real symmetric positive definite matrices, and let S_+^n be the set
of n × n real symmetric positive semidefinite matrices. Define f:ℝ^{n×n} → ℝ+∞ by f(X)=tr(X^{-1})
quad for X ∈ S_{++}^n, and f(X)=+∞ for X notin S_{++}^n. The convex conjugate of f is f*(Y)=sup_{X∈
ℝ^{n×n}} ≤ft(tr(YX)-f(X)). For A ∈ S_+^n, let A^{1/2} denote the unique symmetric positive
semidefinite square root of A. Show that f*(Y)=-2tr((-Y)^{1/2}) for Y ∈ -S_+^n, and that dom
f*=-S_+^n.
-/
theorem convexConjugate_trace_inv_eq_negTwo_trace_sqrt
    {n : Type} [Fintype n] [DecidableEq n] :
    (∀ Y : Matrix n n ℝ, ∀ hY : (-Y).IsSymm ∧ (-Y).PosSemidef,
      sSup (Set.range fun X : {X : Matrix n n ℝ // X.IsSymm ∧ X.PosDef} =>
        (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
          (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) =
        (((-2 : ℝ) * Matrix.trace (CFC.sqrt (-Y))) : EReal)) ∧
({Y : Matrix n n ℝ |
      sSup (Set.range fun X : {X : Matrix n n ℝ // X.IsSymm ∧ X.PosDef} =>
        (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
          (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤} =
      {Y : Matrix n n ℝ | (-Y).IsSymm ∧ (-Y).PosSemidef}) := by
  -- Route correction: this statement is false, not merely missing a proof.
  -- The `Fin 2` witness `skewWitness` lies in the left-hand finiteness domain
  -- by `skewWitness_mem_leftDomain`, but `not_isSymm_neg_skewWitness` excludes
  -- it from `{Y | (-Y).IsSymm ∧ (-Y).PosSemidef}`; this is packaged as
  -- `domain_equality_false_Fin2` and lifted to the polymorphic contradiction
  -- `not_convexConjugate_trace_inv_eq_negTwo_trace_sqrt_all_dims`.
  -- Specializing this theorem to `n := Fin 2` would therefore reproduce the
  -- already refuted conjunction from `not_convexConjugate_trace_inv_eq_negTwo_trace_sqrt_Fin2`.
  -- Lean-checkable conflict: any completed proof here would immediately yield
  -- `False` via `convexConjugate_trace_inv_eq_negTwo_trace_sqrt_conflict`,
  -- and concretely would force the refuted equality from `domain_equality_false_Fin2`.
  -- A correct repair would have to change the theorem statement, for example by
  -- restricting the ambient domain to symmetric matrices before asserting `dom f* = -S_+^n`.
  -- This placeholder is intentionally left only as a bad-statement marker:
  -- the theorem itself is refuted by the existing `Fin 2` counterexample.
  sorry

/-- The current declaration would make the file inconsistent via the `Fin 2` witness. -/
lemma convexConjugate_trace_inv_eq_negTwo_trace_sqrt_declares_false : False := by
  -- Route correction: instantiate the theorem family at `Fin 2`, where the
  -- previously proved skew-symmetric witness already refutes the domain claim.
  exact
    convexConjugate_trace_inv_eq_negTwo_trace_sqrt_conflict
      (fun {n} _ _ => convexConjugate_trace_inv_eq_negTwo_trace_sqrt (n := n))

end «problem-100»
