import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-117»
/-
Let S^n be the set of real symmetric n×n matrices. For X∈S^n let λ₁(X) ≥ ··· ≥ λ_n(X) be its
eigenvalues. Fix 1 ≤ k ≤ n and assume ∑_{i = 1}^k λ_i(X) = sup{tr(VᵀXV): V∈ℝ^{n×k}, VᵀV = Iₖ}. Prove
that X↦∑_{i = 1}^k λ_i(X) is convex on S^n.
-/
open scoped Matrix
theorem sum_top_k_eigenvalues_convex_on_symmetric
    (n k : ℕ)
    (hk1 : 1 ≤ k)
    (hkn : k ≤ n)
    (topKEigenvalueSum : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hvariational :
      ∀ X : Matrix (Fin n) (Fin n) ℝ,
        Matrix.IsSymm X →
          topKEigenvalueSum X =
            sSup {r : ℝ |
              ∃ V : Matrix (Fin n) (Fin k) ℝ,
                V.transpose * V = 1 ∧ r = Matrix.trace (V.transpose * X * V)}) :
    ConvexOn ℝ
      {X : Matrix (Fin n) (Fin n) ℝ | Matrix.IsSymm X}
      topKEigenvalueSum := by
  classical
  let admissible :
      Matrix (Fin n) (Fin n) ℝ → Set ℝ := fun X =>
        {r : ℝ |
          ∃ V : Matrix (Fin n) (Fin k) ℝ,
            V.transpose * V = 1 ∧ r = Matrix.trace (V.transpose * X * V)}
  -- The convexity domain is the linear subspace of symmetric matrices.
  refine ⟨?_, ?_⟩
  · intro X hX Y hY a b ha hb hab
    exact (hX.smul a).add (hY.smul b)
  · intro X hX Y hY a b ha hb hab
    have hXY : Matrix.IsSymm (a • X + b • Y) := (hX.smul a).add (hY.smul b)
    -- We use the first `k` columns of the identity as a concrete orthonormal frame.
    have hframe : ∃ V : Matrix (Fin n) (Fin k) ℝ, V.transpose * V = 1 := by
      let V : Matrix (Fin n) (Fin k) ℝ := (1 : Matrix (Fin n) (Fin n) ℝ).submatrix id (Fin.castLE hkn)
      refine ⟨V, ?_⟩
      have hmul := Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) ℝ)
        (1 : Matrix (Fin n) (Fin n) ℝ) (Fin.castLE hkn) (Equiv.refl (Fin n)) (Fin.castLE hkn)
      simpa [V, Matrix.submatrix_one, Fin.castLE_injective] using hmul
    -- This witness makes every admissible trace set nonempty, which is needed for `csSup_le`.
    have hnonempty : ∀ Z : Matrix (Fin n) (Fin n) ℝ, (admissible Z).Nonempty := by
      intro Z
      rcases hframe with ⟨V, hV⟩
      exact ⟨Matrix.trace (V.transpose * Z * V), ⟨V, hV, rfl⟩⟩
    -- Every admissible frame has entries bounded by `1` because each column has squared norm `1`.
    have hentry :
        ∀ {V : Matrix (Fin n) (Fin k) ℝ}, V.transpose * V = 1 →
          ∀ i : Fin n, ∀ j : Fin k, |V i j| ≤ 1 := by
      intro V hV i j
      have hdiag := congr_fun (congr_fun hV j) j
      simp [Matrix.mul_apply] at hdiag
      have hsplit :
          V i j * V i j + Finset.sum (Finset.univ.erase i) (fun x => V x j * V x j) =
            (∑ x, V x j * V x j) := by
        simpa using
          Finset.add_sum_erase Finset.univ (fun x : Fin n => V x j * V x j) (Finset.mem_univ i)
      have hrest_nonneg :
          0 ≤ Finset.sum (Finset.univ.erase i) (fun x => V x j * V x j) := by
        refine Finset.sum_nonneg ?_
        intro x hx
        nlinarith [sq_nonneg (V x j)]
      have hdiag' :
          V i j * V i j + Finset.sum (Finset.univ.erase i) (fun x => V x j * V x j) = 1 := by
        rw [hsplit]
        exact hdiag
      have hsq_le : V i j * V i j ≤ 1 := by
        nlinarith
      nlinarith [abs_mul_abs_self (V i j), hsq_le]
    -- A crude finite-sum estimate supplies the `BddAbove` side condition for `le_csSup`.
    have hbdd :
        ∀ Z : Matrix (Fin n) (Fin n) ℝ, BddAbove (admissible Z) := by
      intro Z
      refine ⟨∑ j : Fin k, ∑ i : Fin n, ∑ l : Fin n, |Z l i|, ?_⟩
      intro r hr
      rcases hr with ⟨V, hV, rfl⟩
      have hmul_bound :
          ∀ j : Fin k, |((V.transpose * Z * V) j j)| ≤ ∑ i : Fin n, ∑ l : Fin n, |Z l i| := by
        intro j
        calc
          |((V.transpose * Z * V) j j)| = |∑ i : Fin n, ((V.transpose * Z) j i) * V i j| := by
            simp [Matrix.mul_apply]
          _ ≤ ∑ i : Fin n, |((V.transpose * Z) j i) * V i j| := by
            simpa using
              Finset.abs_sum_le_sum_abs (fun i : Fin n => ((V.transpose * Z) j i) * V i j)
                Finset.univ
          _ = ∑ i : Fin n, |(V.transpose * Z) j i| * |V i j| := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [abs_mul]
          _ ≤ ∑ i : Fin n, ∑ l : Fin n, |Z l i| := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hleft : |((V.transpose * Z) j i)| ≤ ∑ l : Fin n, |Z l i| := by
              calc
                |((V.transpose * Z) j i)| = |∑ l : Fin n, V l j * Z l i| := by
                  simp [Matrix.mul_apply]
                _ ≤ ∑ l : Fin n, |V l j * Z l i| := by
                  simpa using
                    Finset.abs_sum_le_sum_abs (fun l : Fin n => V l j * Z l i) Finset.univ
                _ = ∑ l : Fin n, |V l j| * |Z l i| := by
                  refine Finset.sum_congr rfl ?_
                  intro l hl
                  rw [abs_mul]
                _ ≤ ∑ l : Fin n, 1 * |Z l i| := by
                  refine Finset.sum_le_sum ?_
                  intro l hl
                  exact mul_le_mul_of_nonneg_right (hentry hV l j) (abs_nonneg _)
                _ = ∑ l : Fin n, |Z l i| := by simp
            calc
              |(V.transpose * Z) j i| * |V i j| ≤ |(V.transpose * Z) j i| * 1 := by
                exact mul_le_mul_of_nonneg_left (hentry hV i j) (abs_nonneg _)
              _ ≤ ∑ l : Fin n, |Z l i| := by
                simpa using hleft
      calc
        Matrix.trace (V.transpose * Z * V) = ∑ j : Fin k, (V.transpose * Z * V) j j := by
          simp [Matrix.trace]
        _ ≤ ∑ j : Fin k, |(V.transpose * Z * V) j j| := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact le_abs_self _
        _ ≤ ∑ j : Fin k, ∑ i : Fin n, ∑ l : Fin n, |Z l i| := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact hmul_bound j
    -- For a fixed admissible frame, the trace functional is affine in the matrix argument.
    have htrace_affine :
        ∀ (V : Matrix (Fin n) (Fin k) ℝ) (A B : Matrix (Fin n) (Fin n) ℝ) (u v : ℝ),
          Matrix.trace (V.transpose * (u • A + v • B) * V) =
            u * Matrix.trace (V.transpose * A * V) + v * Matrix.trace (V.transpose * B * V) := by
      intro V A B u v
      calc
        Matrix.trace (V.transpose * (u • A + v • B) * V)
            = Matrix.trace (((u • (V.transpose * A)) + (v • (V.transpose * B))) * V) := by
                simp [Matrix.mul_add]
        _ = Matrix.trace ((u • (V.transpose * A)) * V + (v • (V.transpose * B)) * V) := by
              simpa using
                congrArg Matrix.trace
                  (Matrix.add_mul (u • (V.transpose * A)) (v • (V.transpose * B)) V)
        _ = Matrix.trace (u • ((V.transpose * A) * V) + v • ((V.transpose * B) * V)) := by
              simp
        _ = u * Matrix.trace ((V.transpose * A) * V) + v * Matrix.trace ((V.transpose * B) * V) := by
              simp [Matrix.trace_add, Matrix.trace_smul]
        _ = u * Matrix.trace (V.transpose * A * V) + v * Matrix.trace (V.transpose * B * V) := by
              simp [Matrix.mul_assoc]
    -- Rewrite the variational formulas and compare each admissible trace with the corresponding supremum.
    rw [hvariational (a • X + b • Y) hXY, hvariational X hX, hvariational Y hY]
    refine csSup_le (hnonempty (a • X + b • Y)) ?_
    intro r hr
    rcases hr with ⟨V, hV, rfl⟩
    rw [htrace_affine V X Y a b]
    have hXle : Matrix.trace (V.transpose * X * V) ≤ sSup (admissible X) := by
      exact le_csSup (hbdd X) ⟨V, hV, rfl⟩
    have hYle : Matrix.trace (V.transpose * Y * V) ≤ sSup (admissible Y) := by
      exact le_csSup (hbdd Y) ⟨V, hV, rfl⟩
    have hsum :
        a * Matrix.trace (V.transpose * X * V) + b * Matrix.trace (V.transpose * Y * V) ≤
          a * sSup (admissible X) + b * sSup (admissible Y) := by
      nlinarith
    simpa [smul_eq_mul] using hsum

end «problem-117»
