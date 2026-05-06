import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-60»

def l2Norm {m : ℕ} (u : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, (u i) ^ 2)

def l1Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, |x j|

def linfNorm {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  sSup (Set.range fun j : Fin n => |z j|)

/-
Given a primal problem with Lagrangian $L(x, lambda)$, the dual function is $g(lambda) = inf_x L(x,
lambda)$. The Lagrange dual problem is to maximize $g(lambda)$ over the admissible dual variables.
-/
def lagrangeDualFunction {X Lam : Type*} (L : X → Lam → ℝ) : Lam → EReal :=
  fun lam => sInf (Set.range fun x : X => (L x lam : EReal))

structure L2L1PrimalProblem where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  γ : ℝ

def L2L1PrimalProblem.objective (p : L2L1PrimalProblem) :
    ((Fin p.n → ℝ) × (Fin p.m → ℝ)) → ℝ :=
  fun xy => l2Norm xy.2 + p.γ * l1Norm xy.1

def L2L1PrimalProblem.feasibleSet (p : L2L1PrimalProblem) :
    Set ((Fin p.n → ℝ) × (Fin p.m → ℝ)) :=
  {xy | p.A.mulVec xy.1 - p.b = xy.2}

/-
Let (A in mathbf{R}^{m \times n}), (b in mathbf{R}^m), and (gamma > 0). For (u in mathbf{R}^m),
define (|u |_2 = (\sum_{i = 1}^m u_i^2)^{1/2}); for (x in mathbf{R}^n), define (|x |_1 = \sum_{j =
1}^n |x_j|); and for (z in mathbf{R}^n), define (|z |_ infty = max_{1 le j le n} |z_j|).
Consider the primal ll2 - ll1 problem. Prove that its Lagrange dual problem is [ begin{array}{ll}
mbox{maximize} & - b^T nu mbox{subject to} & | nu |_2 le 1, & |A^T nu |_ infty le gamma, end{array}
] with dual variable (nu in mathbf{R}^m).
-/
/-- Rewriting the Lagrangian isolates the `x`-part, `y`-part, and constant term. -/
lemma lagrangian_split (p : L2L1PrimalProblem) (x : Fin p.n → ℝ) (y ν : Fin p.m → ℝ) :
    l2Norm y + p.γ * l1Norm x +
      ∑ i : Fin p.m, ν i * ((p.A.mulVec x - p.b - y) i) =
    (l2Norm y - ν ⬝ᵥ y) + (p.γ * l1Norm x + (p.Aᵀ *ᵥ ν) ⬝ᵥ x) -
      ∑ i : Fin p.m, p.b i * ν i := by
  -- Route correction: first expand the residual sum into separate pieces, then rewrite the matrix
  -- pairing using the transpose identity.
  have hmatrix : ∑ i : Fin p.m, ν i * (p.A.mulVec x) i = (p.Aᵀ *ᵥ ν) ⬝ᵥ x := by
    -- The matrix term is exactly the transpose action paired against `x`.
    simpa [dotProduct, Matrix.mulVec_transpose] using
      (Matrix.dotProduct_mulVec ν p.A x)
  -- After expansion, only a scalar rearrangement remains.
  calc
    l2Norm y + p.γ * l1Norm x + ∑ i : Fin p.m, ν i * ((p.A.mulVec x - p.b - y) i)
        = l2Norm y + p.γ * l1Norm x +
            ((∑ i : Fin p.m, ν i * (p.A.mulVec x) i) -
              ∑ i : Fin p.m, ν i * p.b i -
              ∑ i : Fin p.m, ν i * y i) := by
          simp [sub_eq_add_neg, mul_add, Finset.sum_add_distrib]
    _ = l2Norm y + p.γ * l1Norm x +
          (((p.Aᵀ *ᵥ ν) ⬝ᵥ x) - ∑ i : Fin p.m, p.b i * ν i - ν ⬝ᵥ y) := by
          rw [hmatrix]
          simp [dotProduct, mul_comm]
    _ = (l2Norm y - ν ⬝ᵥ y) + (p.γ * l1Norm x + (p.Aᵀ *ᵥ ν) ⬝ᵥ x) -
          ∑ i : Fin p.m, p.b i * ν i := by
          ring

/-- The dot product is bounded by the product of the Euclidean norms. -/
lemma dotProduct_le_l2Norm_mul_l2Norm {m : ℕ} (u v : Fin m → ℝ) :
    u ⬝ᵥ v ≤ l2Norm u * l2Norm v := by
  -- This is Cauchy-Schwarz written in the file's custom `l2Norm` notation.
  simpa [l2Norm, dotProduct] using
    (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v)

/-- Each coordinate magnitude is bounded by the `linfNorm`. -/
lemma abs_le_linfNorm {n : ℕ} (z : Fin n → ℝ) (j : Fin n) :
    |z j| ≤ linfNorm z := by
  -- The `linfNorm` is the supremum of the coordinate magnitudes.
  unfold linfNorm
  exact le_csSup (Finite.bddAbove_range fun k : Fin n => |z k|) (Set.mem_range_self j)

/-- The dot product is bounded by the `linfNorm` of one factor times the `l1Norm` of the other. -/
lemma abs_dotProduct_le_linfNorm_mul_l1Norm {n : ℕ} (z x : Fin n → ℝ) :
    |z ⬝ᵥ x| ≤ linfNorm z * l1Norm x := by
  -- Route correction: bound each summand by the common supremum before summing the absolute values.
  calc
    |z ⬝ᵥ x| = |∑ j : Fin n, z j * x j| := by
      simp [dotProduct]
    _ ≤ ∑ j : Fin n, |z j * x j| := by
      simpa using (Finset.abs_sum_le_sum_abs (fun j : Fin n => z j * x j) Finset.univ)
    _ = ∑ j : Fin n, |z j| * |x j| := by
      simp [abs_mul]
    _ ≤ ∑ j : Fin n, linfNorm z * |x j| := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact mul_le_mul_of_nonneg_right (abs_le_linfNorm z j) (abs_nonneg (x j))
    _ = linfNorm z * l1Norm x := by
      simp [l1Norm, Finset.mul_sum]

theorem l2l1_primalProblem_has_lagrangeDual
    (p : L2L1PrimalProblem) (hγ : 0 < p.γ) :
    -- The dual objective is g(ν) = - bᵀν for all admissible ν
    ∀ ν : Fin p.m → ℝ,
      l2Norm ν ≤ 1 →
      linfNorm (Matrix.mulVec p.Aᵀ ν) ≤ p.γ →
      lagrangeDualFunction
        (fun xy : (Fin p.n → ℝ) × (Fin p.m → ℝ) => fun ν : Fin p.m → ℝ =>
          l2Norm xy.2 + p.γ * l1Norm xy.1 +
            ∑ i : Fin p.m, ν i * ((p.A.mulVec xy.1 - p.b - xy.2) i))
        ν =
      (-∑ i : Fin p.m, p.b i * ν i : ℝ) := by
  intro ν hν hAν
  -- We compare the infimum with the claimed value by showing `(0, 0)` attains it and every other
  -- Lagrangian value lies above it.
  simp [lagrangeDualFunction]
  apply le_antisymm
  · -- The witness `(0, 0)` gives the claimed upper bound on the infimum.
    refine csInf_le' ?_
    refine ⟨(0, 0), ?_⟩
    -- The zero primal variables kill both norm terms and leave only the constant contribution.
    simp [l2Norm, l1Norm, sub_eq_add_neg, mul_comm]
  · -- Every Lagrangian value is at least `-bᵀν`, so the infimum is also at least `-bᵀν`.
    refine le_csInf ?_ ?_
    · exact Set.range_nonempty fun xy : (Fin p.n → ℝ) × (Fin p.m → ℝ) =>
        ((l2Norm xy.2 + p.γ * l1Norm xy.1 +
          ∑ i : Fin p.m, ν i * ((p.A.mulVec xy.1 - p.b - xy.2) i)) : EReal)
    · intro r hr
      rcases hr with ⟨xy, rfl⟩
      rcases xy with ⟨x, y⟩
      have hy_nonneg : 0 ≤ l2Norm y := by
        -- The `l2` norm is a square root, hence nonnegative.
        unfold l2Norm
        exact Real.sqrt_nonneg _
      have hx_nonneg : 0 ≤ l1Norm x := by
        -- The `l1` norm is a sum of nonnegative terms.
        unfold l1Norm
        exact Finset.sum_nonneg fun j hj => abs_nonneg (x j)
      have hy_part_nonneg : 0 ≤ l2Norm y - ν ⬝ᵥ y := by
        -- Cauchy-Schwarz and the admissibility condition `‖ν‖₂ ≤ 1` control the `y`-part.
        have hdot : ν ⬝ᵥ y ≤ l2Norm ν * l2Norm y :=
          dotProduct_le_l2Norm_mul_l2Norm ν y
        have hdot' : ν ⬝ᵥ y ≤ l2Norm y := by
          calc
            ν ⬝ᵥ y ≤ l2Norm ν * l2Norm y := hdot
            _ ≤ 1 * l2Norm y := by
              exact mul_le_mul_of_nonneg_right hν hy_nonneg
            _ = l2Norm y := by ring
        exact sub_nonneg.mpr hdot'
      have hx_abs_bound : |(p.Aᵀ *ᵥ ν) ⬝ᵥ x| ≤ p.γ * l1Norm x := by
        -- The `l∞-l1` estimate converts the matrix admissibility condition into the `x`-bound.
        calc
          |(p.Aᵀ *ᵥ ν) ⬝ᵥ x| ≤ linfNorm (p.Aᵀ *ᵥ ν) * l1Norm x :=
            abs_dotProduct_le_linfNorm_mul_l1Norm (p.Aᵀ *ᵥ ν) x
          _ ≤ p.γ * l1Norm x := by
            simpa using mul_le_mul_of_nonneg_right hAν hx_nonneg
      have hx_part_nonneg : 0 ≤ p.γ * l1Norm x + (p.Aᵀ *ᵥ ν) ⬝ᵥ x := by
        -- The dot product cannot be less than the negative of its absolute value.
        have hlower : -(p.γ * l1Norm x) ≤ (p.Aᵀ *ᵥ ν) ⬝ᵥ x := by
          have hneg : -(p.γ * l1Norm x) ≤ -|(p.Aᵀ *ᵥ ν) ⬝ᵥ x| := by
            exact neg_le_neg hx_abs_bound
          exact hneg.trans (neg_abs_le _)
        linarith
      -- The split form exposes the two nonnegative pieces, so the whole value is bounded below
      -- by the constant term.
      have hreal :
          (-∑ i : Fin p.m, p.b i * ν i : ℝ) ≤
            l2Norm y + p.γ * l1Norm x + ∑ i : Fin p.m, ν i * ((p.A.mulVec x - p.b - y) i) := by
        calc
          (-∑ i : Fin p.m, p.b i * ν i : ℝ)
              ≤ (l2Norm y - ν ⬝ᵥ y) + (p.γ * l1Norm x + (p.Aᵀ *ᵥ ν) ⬝ᵥ x) -
                  ∑ i : Fin p.m, p.b i * ν i := by
                    linarith
          _ = l2Norm y + p.γ * l1Norm x + ∑ i : Fin p.m, ν i * ((p.A.mulVec x - p.b - y) i) := by
                rw [← lagrangian_split p x y ν]
      exact EReal.coe_le_coe hreal

end «problem-60»
