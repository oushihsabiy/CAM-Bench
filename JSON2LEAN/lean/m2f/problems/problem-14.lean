import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-14»
open scoped RealInnerProductSpace

def dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  { z | ∀ ⦃x⦄, x ∈ K → 0 ≤ ⟪z, x⟫ }

def Kpol (k : ℕ) : Set (EuclideanSpace ℝ (Fin (2 * k + 1))) :=
  { x |
    ∀ t : ℝ,
      0 ≤
        (∑ i : Fin (2 * k + 1), (x i) * (t ^ (i.1 : ℕ))) }

def hankelMatrix (k : ℕ) (z : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  fun i j => z ⟨i.1 + j.1, by
    have hi : i.1 < k + 1 := i.2
    have hj : j.1 < k + 1 := j.2
    have hsum : i.1 + j.1 ≤ 2 * k := by
      have hi' : i.1 ≤ k := Nat.le_of_lt_succ hi
      have hj' : j.1 ≤ k := Nat.le_of_lt_succ hj
      calc
        i.1 + j.1 ≤ k + k := Nat.add_le_add hi' hj'
        _ = 2 * k := by omega
    exact Nat.lt_of_le_of_lt hsum (Nat.lt_succ_self (2 * k))⟩

def Khan (k : ℕ) : Set (EuclideanSpace ℝ (Fin (2 * k + 1))) :=
  { z | Matrix.PosSemidef (hankelMatrix k z) }

/-- The polynomial whose coefficients are the entries of a finite vector. -/
def polyOfVec {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : Polynomial ℝ :=
  ∑ i : Fin n, Polynomial.C (x i) * Polynomial.X ^ (i.1 : ℕ)

/-- The coefficient vector of the square of `polyOfVec v`, truncated at degree `2 * k`. -/
def squareCoeffVector (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    EuclideanSpace ℝ (Fin (2 * k + 1)) :=
  (EuclideanSpace.equiv (Fin (2 * k + 1)) ℝ).symm fun m : Fin (2 * k + 1) =>
    ((polyOfVec v) ^ 2).coeff m.1

/-- The polynomial attached to a finite vector has the expected coefficients. -/
lemma polyOfVec_coeff {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    (polyOfVec x).coeff m = if h : m < n then x ⟨m, h⟩ else 0 := by
  classical
  -- Each summand contributes only in its own degree.
  calc
    (polyOfVec x).coeff m =
        ∑ i : Fin n, (Polynomial.C (x i) * Polynomial.X ^ (i.1 : ℕ)).coeff m := by
          simp [polyOfVec]
    _ = if h : m < n then x ⟨m, h⟩ else 0 := by
      by_cases hm : m < n
      · have hsum :
            ∑ i : Fin n, (Polynomial.C (x i) * Polynomial.X ^ (i.1 : ℕ)).coeff m = x ⟨m, hm⟩ := by
          have hsum0 :
              ∑ i : Fin n, (Polynomial.C (x i) * Polynomial.X ^ (i.1 : ℕ)).coeff m =
                (Polynomial.C (x ⟨m, hm⟩) * Polynomial.X ^ (m : ℕ)).coeff m := by
            refine Finset.sum_eq_single
              (s := (Finset.univ : Finset (Fin n)))
              (a := (⟨m, hm⟩ : Fin n))
              (f := fun i : Fin n => (Polynomial.C (x i) * Polynomial.X ^ (i.1 : ℕ)).coeff m) ?_ ?_
            · intro i hi hne
              have hmi : m ≠ i.1 := by
                intro hmi
                apply hne
                exact Fin.ext hmi.symm
              simp [hmi]
            · simp
          exact hsum0.trans (by simp)
        simpa [hm] using hsum
      · have hsum :
            ∑ i : Fin n, (Polynomial.C (x i) * Polynomial.X ^ (i.1 : ℕ)).coeff m = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          have hmi : m ≠ i.1 := by
            intro hmi
            exact hm (hmi.symm ▸ i.2)
          simp [hmi]
        simpa [hm] using hsum

/-- The polynomial attached to a `Fin (k + 1)` vector has degree at most `k`. -/
lemma polyOfVec_natDegree_le (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    (polyOfVec v).natDegree ≤ k := by
  -- Bound the degree termwise and then take the finite maximum.
  simpa [polyOfVec] using
    (Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin (k + 1))))
      (f := fun i => Polynomial.C (v i) * Polynomial.X ^ (i.1 : ℕ))
      (n := k) fun i hi => (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ i.2))

/-- Evaluating `polyOfVec` reproduces the expected coefficient sum. -/
lemma eval_polyOfVec {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (polyOfVec x).eval t = ∑ i : Fin n, x i * t ^ (i.1 : ℕ) := by
  -- Expand evaluation termwise.
  calc
    (polyOfVec x).eval t =
        ∑ i : Fin n, (Polynomial.C (x i) * Polynomial.X ^ (i.1 : ℕ)).eval t := by
          rw [polyOfVec, Polynomial.eval_finset_sum]
    _ = ∑ i : Fin n, x i * t ^ (i.1 : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp

/-- The square-coefficient vector corresponds exactly to the squared polynomial. -/
lemma polyOfVec_squareCoeffVector (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    polyOfVec (squareCoeffVector k v) = (polyOfVec v) ^ 2 := by
  classical
  -- Compare coefficients degree by degree; degrees above `2 * k` vanish on both sides.
  ext m
  by_cases hm : m < 2 * k + 1
  · have hm' : m ≤ 2 * k := Nat.lt_succ_iff.mp hm
    simp [polyOfVec_coeff, squareCoeffVector, EuclideanSpace.equiv, hm]
  · have hm' : 2 * k + 1 ≤ m := Nat.not_lt.mp hm
    have hdeg :
        ((polyOfVec v) ^ 2).natDegree < m := by
      have hle : ((polyOfVec v) ^ 2).natDegree ≤ 2 * k := by
        calc
          ((polyOfVec v) ^ 2).natDegree ≤ 2 * (polyOfVec v).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ 2 * k := Nat.mul_le_mul_left _ (polyOfVec_natDegree_le k v)
      exact lt_of_le_of_lt hle (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hm')
    -- Above degree `2 * k`, both the truncation polynomial and the square have zero coefficients.
    simp [polyOfVec_coeff, squareCoeffVector, EuclideanSpace.equiv, hm,
      Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]

/-- The truncated square-coefficient vector belongs to the cone of globally nonnegative polynomials. -/
lemma squareCoeffVector_mem_Kpol (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    squareCoeffVector k v ∈ Kpol k := by
  intro t
  -- Reinterpret the coefficient sum as evaluation of the squared polynomial.
  have hpoly := congrArg (fun p : Polynomial ℝ => p.eval t) (polyOfVec_squareCoeffVector k v)
  have hpoly' :
      ∑ i : Fin (2 * k + 1), squareCoeffVector k v i * t ^ (i.1 : ℕ) = ((polyOfVec v) ^ 2).eval t := by
    simpa [eval_polyOfVec] using hpoly
  rw [hpoly']
  -- A square is nonnegative at every real point.
  simpa using sq_nonneg ((polyOfVec v).eval t)

/-- The Hankel matrix is Hermitian because its entries depend only on `i + j`. -/
lemma hankelMatrix_isHermitian (k : ℕ) (z : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    (hankelMatrix k z).IsHermitian := by
  -- Over `ℝ`, Hermitian reduces to symmetry.
  ext i j
  simp [hankelMatrix, add_comm]

/-- A polynomial of degree at most `k` is recovered from its first `k + 1` coefficients. -/
lemma polyOfVec_coeffs_of_natDegree_le (k : ℕ) (q : Polynomial ℝ)
    (hq : q.natDegree ≤ k) :
    polyOfVec ((EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm fun i => q.coeff i.1) = q := by
  -- Compare coefficients degree by degree and use the degree bound above `k`.
  ext m
  by_cases hm : m < k + 1
  · simp [polyOfVec_coeff, hm]
  · have hmk : k < m := by
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.not_lt.mp hm)
    have hdeg : q.natDegree < m := lt_of_le_of_lt hq hmk
    simp [polyOfVec_coeff, hm, Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]

/-- A globally nonnegative real polynomial has every real root with multiplicity at least two. -/
lemma sq_dvd_of_nonneg_eval_zero (p : Polynomial ℝ) (a : ℝ)
    (hnonneg : ∀ t : ℝ, 0 ≤ p.eval t) (ha : p.eval a = 0) :
    (Polynomial.X - Polynomial.C a) ^ 2 ∣ p := by
  by_cases hp : p = 0
  · -- The zero polynomial is divisible by every polynomial power.
    simp [hp]
  -- A global minimum at `a` forces the derivative to vanish there as well.
  have hminOn : IsMinOn (fun t : ℝ => p.eval t) Set.univ a := by
    intro x hx
    simpa [ha] using hnonneg x
  have hmin : IsLocalMin (fun t : ℝ => p.eval t) a :=
    hminOn.isLocalMin (by simp)
  have hderiv_zero : Polynomial.eval a (Polynomial.derivative p) = 0 := by
    have hderiv : deriv (fun t : ℝ => p.eval t) a = 0 := IsLocalMin.deriv_eq_zero hmin
    simpa [Polynomial.deriv] using hderiv
  have hroot : p.IsRoot a := by
    simp [Polynomial.IsRoot, ha]
  have hroot_deriv : (Polynomial.derivative p).IsRoot a := by
    simp [Polynomial.IsRoot, hderiv_zero]
  have hmultiplicity : 1 < Polynomial.rootMultiplicity a p := by
    exact (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).2 ⟨hroot, hroot_deriv⟩
  have hpow : (Polynomial.X - Polynomial.C a) ^ Polynomial.rootMultiplicity a p ∣ p :=
    Polynomial.pow_rootMultiplicity_dvd p a
  -- Any power at least two contains the square factor we need.
  exact dvd_trans
    (pow_dvd_pow (Polynomial.X - Polynomial.C a) (Nat.succ_le_of_lt hmultiplicity))
    hpow

/-- The quadratic factor coming from a nonreal complex root is a sum of two squares. -/
lemma quadratic_from_nonreal_root_is_sum_two_squares (a b : ℝ) :
    (Polynomial.X ^ 2 - Polynomial.C (2 * a) * Polynomial.X + Polynomial.C (a ^ 2 + b ^ 2) :
      Polynomial ℝ) =
      (Polynomial.X - Polynomial.C a) ^ 2 + (Polynomial.C b) ^ 2 := by
  -- Compare the two polynomials by evaluation and expand both sides explicitly.
  apply Polynomial.funext
  intro t
  simp [pow_two]
  ring

/-- The quadratic factor attached to a nonreal root is strictly positive on `ℝ`. -/
lemma quadratic_from_nonreal_root_eval_pos (a b t : ℝ) (hb : b ≠ 0) :
    0 <
      (Polynomial.X ^ 2 - Polynomial.C (2 * a) * Polynomial.X + Polynomial.C (a ^ 2 + b ^ 2) :
        Polynomial ℝ).eval t := by
  -- Rewrite the quadratic as `(t - a)^2 + b^2` and use that `b^2` is positive.
  rw [quadratic_from_nonreal_root_is_sum_two_squares]
  simp [pow_two]
  nlinarith [sq_nonneg (t - a), sq_pos_of_ne_zero hb]

/-- Dividing a strictly positive polynomial by the positive quadratic from a nonreal root preserves
strict positivity. -/
lemma quadratic_from_nonreal_root_quot_eval_pos (p : Polynomial ℝ) (a b : ℝ)
    (hpos : ∀ t : ℝ, 0 < p.eval t) (hb : b ≠ 0)
    (hdiv :
      (Polynomial.X ^ 2 - Polynomial.C (2 * a) * Polynomial.X + Polynomial.C (a ^ 2 + b ^ 2) :
        Polynomial ℝ) ∣ p) :
    ∀ t : ℝ,
      0 <
        (p /ₘ
            (Polynomial.X ^ 2 - Polynomial.C (2 * a) * Polynomial.X +
              Polynomial.C (a ^ 2 + b ^ 2))).eval t := by
  let q : Polynomial ℝ :=
    Polynomial.X ^ 2 - Polynomial.C (2 * a) * Polynomial.X + Polynomial.C (a ^ 2 + b ^ 2)
  have hq_monic : q.Monic := by
    -- The quadratic divisor is monic, so `divByMonic` computes the exact quotient.
    dsimp [q]
    exact (Polynomial.isMonicOfDegree_sub_add_two (2 * a) (a ^ 2 + b ^ 2)).monic
  rcases hdiv with ⟨r, rfl⟩
  intro t
  have hqpos : 0 < q.eval t := by
    -- The nonreal quadratic is pointwise positive on `ℝ`.
    dsimp [q]
    simpa using quadratic_from_nonreal_root_eval_pos a b t hb
  have hmulpos : 0 < (q * r).eval t := hpos t
  have hquot : (q * r) /ₘ q = r := Polynomial.mul_divByMonic_cancel_left r hq_monic
  -- Divide the positive product by the positive quadratic factor.
  rw [hquot]
  have hrpos : 0 < r.eval t := by
    by_contra hr_nonpos
    have hmul_nonpos : q.eval t * r.eval t ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hqpos.le (le_of_not_gt hr_nonpos)
    have : ¬ q.eval t * r.eval t ≤ 0 := not_le_of_gt (by simpa [Polynomial.eval_mul] using hmulpos)
    exact this hmul_nonpos
  simpa using hrpos

/-- The monomial moment vector has a rank-one Hankel matrix, so it belongs to `Khan`. -/
lemma monomialMomentVector_mem_Khan (k : ℕ) (t : ℝ) :
    ((EuclideanSpace.equiv (Fin (2 * k + 1)) ℝ).symm fun m : Fin (2 * k + 1) => t ^ (m.1 : ℕ)) ∈
      Khan k := by
  let zt : EuclideanSpace ℝ (Fin (2 * k + 1)) :=
    (EuclideanSpace.equiv (Fin (2 * k + 1)) ℝ).symm fun m : Fin (2 * k + 1) => t ^ (m.1 : ℕ)
  let w : EuclideanSpace ℝ (Fin (k + 1)) :=
    (EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm fun i : Fin (k + 1) => t ^ (i.1 : ℕ)
  have hmatrix : hankelMatrix k zt = Matrix.vecMulVec w.ofLp w.ofLp := by
    -- Compare entries: both sides are the monomial `t^(i+j)`.
    ext i j
    simp [zt, hankelMatrix, w, Matrix.vecMulVec, pow_add]
  -- A rank-one outer product is positive semidefinite.
  change Matrix.PosSemidef (hankelMatrix k zt)
  rw [hmatrix]
  simpa using Matrix.posSemidef_vecMulVec_self_star w.ofLp

/-- Any functional nonnegative on `Khan` is nonnegative on every monomial test vector, hence lies
in `Kpol`. -/
lemma dualCone_Khan_subset_Kpol (k : ℕ) : dualCone (Khan k) ⊆ Kpol k := by
  intro x hx t
  let mvec : EuclideanSpace ℝ (Fin (2 * k + 1)) :=
    (EuclideanSpace.equiv (Fin (2 * k + 1)) ℝ).symm fun m : Fin (2 * k + 1) => t ^ (m.1 : ℕ)
  have hmvec : mvec ∈ Khan k := by
    -- Reuse the rank-one Hankel witness for the monomial moment vector.
    simpa [mvec] using monomialMomentVector_mem_Khan k t
  have hnonneg : 0 ≤ ⟪x, mvec⟫ := hx hmvec
  -- Pairing with the moment vector is exactly polynomial evaluation at `t`.
  simpa [mvec, Kpol, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, eval_polyOfVec, mul_comm]
    using hnonneg

variable {k : ℕ}

/-- The zero vector has zero Hankel matrix, hence lies in `Khan`. -/
lemma zero_mem_Khan (k : ℕ) : (0 : EuclideanSpace ℝ (Fin (2 * k + 1))) ∈ Khan k := by
  -- The zero matrix is positive semidefinite.
  simpa [Khan, hankelMatrix] using
    (Matrix.PosSemidef.zero : Matrix.PosSemidef (0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ))

/-- `Khan` is closed under addition because positive semidefinite matrices are. -/
lemma add_mem_Khan (k : ℕ)
    {z w : EuclideanSpace ℝ (Fin (2 * k + 1))} (hz : z ∈ Khan k) (hw : w ∈ Khan k) :
    z + w ∈ Khan k := by
  -- Rewrite the Hankel matrix of a sum entrywise and use closure of `PosSemidef` under addition.
  have hadd : hankelMatrix k (z + w) = hankelMatrix k z + hankelMatrix k w := by
    ext i j
    simp [hankelMatrix]
  change Matrix.PosSemidef (hankelMatrix k (z + w))
  rw [hadd]
  exact hz.add hw

/-- Positive scaling preserves `Khan` because positive semidefinite matrices form a cone. -/
lemma smul_mem_Khan (k : ℕ) {c : ℝ} (hc : 0 < c)
    {z : EuclideanSpace ℝ (Fin (2 * k + 1))} (hz : z ∈ Khan k) :
    c • z ∈ Khan k := by
  -- Rewrite the Hankel matrix of a scalar multiple entrywise and scale the PSD witness.
  have hsmul : hankelMatrix k (c • z) = c • hankelMatrix k z := by
    ext i j
    simp [hankelMatrix]
  change Matrix.PosSemidef (hankelMatrix k (c • z))
  rw [hsmul]
  exact hz.smul (le_of_lt hc)

/-- The Hankel-positive-semidefinite vectors form a convex cone. -/
def khanConvexCone (k : ℕ) : ConvexCone ℝ (EuclideanSpace ℝ (Fin (2 * k + 1))) where
  carrier := Khan k
  smul_mem' := fun {_} hc {_} hz => smul_mem_Khan k hc hz
  add_mem' := fun {_} hz {_} hw => add_mem_Khan k hz hw

/-- The positive-semidefinite cone of square matrices is closed. -/
lemma isClosed_posSemidef_matrix (n : Type*) [Fintype n] [DecidableEq n] :
    IsClosed {X : Matrix n n ℝ | X.PosSemidef} := by
  -- Positive semidefiniteness is Hermitian symmetry plus nonnegativity of every quadratic form.
  have hhermitian_closed : IsClosed {X : Matrix n n ℝ | X.IsHermitian} := by
    simpa [Matrix.IsHermitian] using
      (isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id)
  have hquadratic_closed (x : n →₀ ℝ) :
      IsClosed
        {X : Matrix n n ℝ |
          0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * X i j * xj} := by
    let q : Matrix n n ℝ → ℝ :=
      fun X => x.support.sum fun i => x.support.sum fun j => star (x i) * X i j * x j
    have hq_cont : Continuous q := by
      refine continuous_finset_sum _ ?_
      intro i hi
      refine continuous_finset_sum _ ?_
      intro j hj
      have hterm : Continuous fun X : Matrix n n ℝ => star (x i) * X i j * x j := by
        fun_prop
      simpa [q] using hterm
    have hq_eq :
        q = fun X : Matrix n n ℝ =>
          x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * X i j * xj := by
      funext X
      simp [q, Finsupp.sum]
    rw [show {X : Matrix n n ℝ |
          0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * X i j * xj} =
            {X : Matrix n n ℝ | 0 ≤ q X} by
          ext X
          simp [hq_eq]]
    exact isClosed_le continuous_const hq_cont
  have hEq :
      {X : Matrix n n ℝ | X.PosSemidef} =
        {X : Matrix n n ℝ | X.IsHermitian} ∩
          ⋂ x : n →₀ ℝ,
            {X : Matrix n n ℝ |
              0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * X i j * xj} := by
    ext X
    simp [Matrix.PosSemidef]
  simpa [hEq] using hhermitian_closed.inter (isClosed_iInter hquadratic_closed)

/-- The Hankel-positive-semidefinite cone is closed because `hankelMatrix` depends continuously on
the moment vector. -/
lemma isClosed_Khan (k : ℕ) :
    IsClosed (Khan k : Set (EuclideanSpace ℝ (Fin (2 * k + 1)))) := by
  -- The Hankel map is entrywise continuous, so we pull back the closed PSD cone along it.
  have hcont : Continuous (hankelMatrix k) := by
    refine continuous_matrix ?_
    intro i j
    let ij : Fin (2 * k + 1) :=
      ⟨i.1 + j.1, by
        have hi : i.1 < k + 1 := i.2
        have hj : j.1 < k + 1 := j.2
        have hsum : i.1 + j.1 ≤ 2 * k := by
          have hi' : i.1 ≤ k := Nat.le_of_lt_succ hi
          have hj' : j.1 ≤ k := Nat.le_of_lt_succ hj
          calc
            i.1 + j.1 ≤ k + k := Nat.add_le_add hi' hj'
            _ = 2 * k := by omega
        exact Nat.lt_of_le_of_lt hsum (Nat.lt_succ_self (2 * k))⟩
    simpa [hankelMatrix] using
      ((continuous_apply ij).comp (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (2 * k + 1))).continuous :
        Continuous fun z : EuclideanSpace ℝ (Fin (2 * k + 1)) => z ij)
  simpa [Khan] using (isClosed_posSemidef_matrix (Fin (k + 1))).preimage hcont

/-- Any functional nonnegative on `Kpol` already lies in `Khan`. -/
lemma dualCone_Kpol_subset_Khan (k : ℕ) : dualCone (Kpol k) ⊆ Khan k := by
  intro z hz
  by_contra hzK
  -- Separate `z` from the closed cone `Khan k`.
  obtain ⟨y, hydual, hyneg⟩ :=
    ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem
      (K := khanConvexCone k) (by simpa [khanConvexCone] using ⟨0, zero_mem_Khan k⟩)
      (isClosed_Khan k) hzK
  have hydual' : y ∈ dualCone (Khan k) := by
    -- Convert the separator into the `dualCone` convention by commuting the real inner product.
    intro x hx
    have hxy : 0 ≤ ⟪x, y⟫ := hydual x hx
    simpa [real_inner_comm] using hxy
  have hyKpol : y ∈ Kpol k := dualCone_Khan_subset_Kpol k hydual'
  have hnonneg : 0 ≤ ⟪y, z⟫ := by
    -- Apply the assumed dual inequality of `z` to the separating test vector `y`.
    simpa [real_inner_comm] using hz hyKpol
  exact (not_le_of_gt hyneg) hnonneg

/-- The coefficient polynomial determines a moment vector uniquely. -/
lemma polyOfVec_injective {k : ℕ} {x y : EuclideanSpace ℝ (Fin (2 * k + 1))}
    (hxy : polyOfVec x = polyOfVec y) :
    x = y := by
  -- Compare coefficients in each degree below `2 * k + 1`.
  ext i
  -- The `i`-th coordinate is exactly the `i`-th coefficient of `polyOfVec`.
  have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff i.1) hxy
  simpa [polyOfVec_coeff, i.2] using hcoeff

/-- Pairing against a squared coefficient vector expands to a finite coefficient sum. -/
lemma inner_squareCoeffVector_eq_coeffSum (k : ℕ)
    (z : EuclideanSpace ℝ (Fin (2 * k + 1))) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    ⟪z, squareCoeffVector k v⟫ =
      ∑ m : Fin (2 * k + 1), z m * ((polyOfVec v) ^ 2).coeff m.1 := by
  -- Expand the inner product and unfold the definition of `squareCoeffVector`.
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, squareCoeffVector, mul_comm]

/-- The Hankel quadratic form is the double sum indexed by the coefficient positions. -/
lemma hankelQuadratic_eq_sum (k : ℕ)
    (z : EuclideanSpace ℝ (Fin (2 * k + 1))) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    star v.ofLp ⬝ᵥ (hankelMatrix k z *ᵥ v.ofLp) =
      ∑ i : Fin (k + 1), ∑ j : Fin (k + 1), v i * (z ⟨i.1 + j.1, by
        have hi : i.1 < k + 1 := i.2
        have hj : j.1 < k + 1 := j.2
        have hsum : i.1 + j.1 ≤ 2 * k := by
          have hi' : i.1 ≤ k := Nat.le_of_lt_succ hi
          have hj' : j.1 ≤ k := Nat.le_of_lt_succ hj
          calc
            i.1 + j.1 ≤ k + k := Nat.add_le_add hi' hj'
            _ = 2 * k := by omega
        exact Nat.lt_of_le_of_lt hsum (Nat.lt_succ_self (2 * k))⟩ * v j) := by
  -- Expand the matrix-vector product and then the outer dot product.
  simp only [dotProduct, Matrix.mulVec]
  -- Over `ℝ`, all stars disappear and the result is the expected double sum.
  simp [hankelMatrix, Finset.mul_sum, mul_left_comm]

/-- A nonnegative constant polynomial is a sum of two polynomial squares of degree `0`. -/
lemma constant_sum_two_squares_of_nonneg_eval (q : Polynomial ℝ) (hq : q.natDegree ≤ 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ q.eval t) :
    ∃ p r : Polynomial ℝ, q = p ^ 2 + r ^ 2 ∧ p.natDegree ≤ 0 ∧ r.natDegree ≤ 0 := by
  -- Collapse `q` to its constant coefficient and take a square root of that constant.
  have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hq
  have hcoeff_nonneg : 0 ≤ q.coeff 0 := by
    have h0 := hnonneg 0
    rwa [hqC, Polynomial.eval_C] at h0
  refine ⟨Polynomial.C (Real.sqrt (q.coeff 0)), 0, ?_, by simp, by simp⟩
  -- Route correction: the base case is handled directly as a constant polynomial rather than by
  -- forcing the general root-removal argument into degree `0`.
  calc
    q = Polynomial.C (q.coeff 0) := hqC
    _ = Polynomial.C ((Real.sqrt (q.coeff 0)) ^ 2) := by
      congr
      exact (Real.sq_sqrt hcoeff_nonneg).symm
    _ = (Polynomial.C (Real.sqrt (q.coeff 0))) ^ 2 + (0 : Polynomial ℝ) ^ 2 := by
      simp [pow_two]

/-- The product of two sums of two squares is again a sum of two squares. -/
lemma sum_two_squares_mul (a b c d : Polynomial ℝ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  -- Expand the Brahmagupta identity in the polynomial ring.
  ring

/-- A strictly positive real polynomial of degree at most `2 * k` is a sum of two squares whose
summands have degree at most `k`. -/
lemma strictPos_sum_two_squares_of_natDegree_le (k : ℕ) (q : Polynomial ℝ)
    (hq : q.natDegree ≤ 2 * k) (hpos : ∀ t : ℝ, 0 < q.eval t) :
    ∃ p r : Polynomial ℝ, q = p ^ 2 + r ^ 2 ∧ p.natDegree ≤ k ∧ r.natDegree ≤ k := by
  induction k generalizing q with
  | zero =>
      -- Route correction: the degree-zero case is handled directly as a constant polynomial.
      have hq0 : q.natDegree ≤ 0 := by simpa using hq
      have hnonneg : ∀ t : ℝ, 0 ≤ q.eval t := fun t => (hpos t).le
      simpa using constant_sum_two_squares_of_nonneg_eval q hq0 hnonneg
  | succ k ih =>
      by_cases hconst : q.natDegree ≤ 0
      · -- If the polynomial is already constant, reuse the base-case decomposition.
        have hnonneg : ∀ t : ℝ, 0 ≤ q.eval t := fun t => (hpos t).le
        rcases constant_sum_two_squares_of_nonneg_eval q hconst hnonneg with
          ⟨p, r, hqr, hpdeg, hrdeg⟩
        exact ⟨p, r, hqr, hpdeg.trans (Nat.zero_le _), hrdeg.trans (Nat.zero_le _)⟩
      · -- Otherwise the strictly positive polynomial has positive degree, hence a complex root.
        have hq_ne : q ≠ 0 := by
          intro hzero
          simpa [hzero] using hpos 0
        have hq_natDegree_pos : 0 < q.natDegree := by
          exact Nat.pos_of_ne_zero fun h0 => hconst h0.le
        have hq_deg_pos : 0 < q.degree := by
          exact Polynomial.natDegree_pos_iff_degree_pos.mp hq_natDegree_pos
        obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ q (ne_of_gt hq_deg_pos)
        have hz_im : z.im ≠ 0 := by
          intro hzim
          have hz_eq : (z.re : ℂ) = z := by
            apply Complex.ext <;> simp [hzim]
          have hz_eval₂ : q.eval₂ (algebraMap ℝ ℂ) (z.re : ℂ) = 0 := by
            -- A strictly positive polynomial cannot vanish at a real point.
            simpa [hz_eq] using hz
          have hz_eval : q.eval z.re = 0 := by
            have hz_eval₂' := hz_eval₂
            change Polynomial.eval₂ (algebraMap ℝ ℂ) (algebraMap ℝ ℂ z.re) q = 0 at hz_eval₂'
            rw [Polynomial.eval₂_at_apply] at hz_eval₂'
            exact Complex.ofReal_injective hz_eval₂'
          exact (ne_of_gt (hpos z.re)) hz_eval
        let quad : Polynomial ℝ :=
          Polynomial.X ^ 2 - Polynomial.C (2 * z.re) * Polynomial.X +
            Polynomial.C (z.re ^ 2 + z.im ^ 2)
        have hquad_monic : quad.Monic := by
          -- The quadratic factor attached to the nonreal root is monic.
          dsimp [quad]
          exact (Polynomial.isMonicOfDegree_sub_add_two (2 * z.re) (z.re ^ 2 + z.im ^ 2)).monic
        have hquad_natDegree : quad.natDegree = 2 := by
          -- Its degree is exactly two, matching the two-step induction drop.
          dsimp [quad]
          exact (Polynomial.isMonicOfDegree_sub_add_two (2 * z.re) (z.re ^ 2 + z.im ^ 2)).natDegree_eq
        have hquad_dvd : quad ∣ q := by
          -- Rewrite the standard quadratic divisor from the complex root theorem into the
          -- explicit `re^2 + im^2` form used below.
          have hnorm :
              Polynomial.C (z.re ^ 2 + z.im ^ 2) = Polynomial.C (‖z‖ ^ 2) := by
            congr 1
            calc
              z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
                simp [Complex.normSq_apply, pow_two]
              _ = ‖z‖ ^ 2 := by
                simpa using (Complex.sq_norm z).symm
          simpa [quad, hnorm] using
            (Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero q hz hz_im)
        have hquot_pos : ∀ t : ℝ, 0 < (q /ₘ quad).eval t := by
          -- Dividing by the pointwise positive quadratic preserves strict positivity.
          simpa [quad] using
            quadratic_from_nonreal_root_quot_eval_pos q z.re z.im hpos hz_im hquad_dvd
        have hquot_deg : (q /ₘ quad).natDegree ≤ 2 * k := by
          -- The monic quadratic divisor drops the degree by exactly two.
          rw [Polynomial.natDegree_divByMonic q hquad_monic, hquad_natDegree]
          omega
        rcases ih (q /ₘ quad) hquot_deg hquot_pos with ⟨p, r, hqr, hpdeg, hrdeg⟩
        let a : Polynomial ℝ := Polynomial.X - Polynomial.C z.re
        let b : Polynomial ℝ := Polynomial.C z.im
        have hquad_expand : quad = a ^ 2 + b ^ 2 := by
          -- Rewrite the quadratic factor as a sum of two polynomial squares.
          simpa [a, b, quad] using quadratic_from_nonreal_root_is_sum_two_squares z.re z.im
        have hmod : q %ₘ quad = 0 := by
          exact (Polynomial.modByMonic_eq_zero_iff_dvd hquad_monic).2 hquad_dvd
        have hfactor : q = quad * (q /ₘ quad) := by
          -- Since the remainder vanishes, division by the monic quadratic is exact.
          have hdiv := Polynomial.modByMonic_add_div q hquad_monic
          rw [hmod, zero_add] at hdiv
          exact hdiv.symm
        refine ⟨a * p - b * r, a * r + b * p, ?_, ?_, ?_⟩
        · -- Combine the quadratic factor and the recursive quotient decomposition.
          calc
            q = quad * (q /ₘ quad) := hfactor
            _ = quad * (p ^ 2 + r ^ 2) := by rw [hqr]
            _ = (a ^ 2 + b ^ 2) * (p ^ 2 + r ^ 2) := by rw [hquad_expand]
            _ = (a * p - b * r) ^ 2 + (a * r + b * p) ^ 2 := by
              simpa [a, b, mul_comm, mul_left_comm, mul_assoc] using sum_two_squares_mul a b p r
        · -- The first new summand is built from terms of degrees `1 + k` and `0 + k`.
          have ha_deg : a.natDegree ≤ 1 := by
            simp [a]
          have hb_deg : b.natDegree ≤ 0 := by
            simp [b]
          have hap_deg : (a * p).natDegree ≤ k + 1 := by
            simpa [Nat.add_comm] using
              (Polynomial.natDegree_mul_le_of_le (p := a) (q := p) (m := 1) (n := k) ha_deg hpdeg)
          have hbr_deg : (b * r).natDegree ≤ k + 1 := by
            have : (b * r).natDegree ≤ 0 + k := by
              exact Polynomial.natDegree_mul_le_of_le (p := b) (q := r) (m := 0) (n := k) hb_deg hrdeg
            omega
          simpa using Polynomial.natDegree_sub_le_of_le hap_deg hbr_deg
        · -- The second new summand is handled similarly.
          have ha_deg : a.natDegree ≤ 1 := by
            simp [a]
          have hb_deg : b.natDegree ≤ 0 := by
            simp [b]
          have har_deg : (a * r).natDegree ≤ k + 1 := by
            simpa [Nat.add_comm] using
              (Polynomial.natDegree_mul_le_of_le (p := a) (q := r) (m := 1) (n := k) ha_deg hrdeg)
          have hbp_deg : (b * p).natDegree ≤ k + 1 := by
            have : (b * p).natDegree ≤ 0 + k := by
              exact Polynomial.natDegree_mul_le_of_le (p := b) (q := p) (m := 0) (n := k) hb_deg hpdeg
            omega
          simpa using Polynomial.natDegree_add_le_of_le har_deg hbp_deg

/-- If every positive perturbation `a + ε b` is nonnegative, then `a` is nonnegative. -/
lemma nonneg_of_forall_pos_perturb (a b : ℝ)
    (h : ∀ ε > 0, 0 ≤ a + ε * b) : 0 ≤ a := by
  -- Route correction: isolate the `ε → 0+` argument as a scalar inequality rather than leaving it
  -- embedded in the final cone proof.
  by_contra ha
  have ha_lt : a < 0 := lt_of_not_ge ha
  by_cases hb : b ≤ 0
  · -- If `b` is nonpositive, the perturbation only decreases `a`, so `ε = 1` already contradicts
    -- the assumed nonnegativity.
    have h1 := h 1 zero_lt_one
    have hneg : a + 1 * b < 0 := by
      nlinarith
    exact (not_le_of_gt hneg) h1
  · -- If `b` is positive, choose a small enough perturbation so that the sum is still negative.
    have hb_pos : 0 < b := lt_of_not_ge hb
    let ε : ℝ := -a / (2 * b)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      have hneg_a : 0 < -a := by
        nlinarith
      positivity
    have hε := h ε hε_pos
    have hcalc : a + ε * b = a / 2 := by
      dsimp [ε]
      field_simp [hb_pos.ne']
      ring
    have hhalf_neg : a / 2 < 0 := by
      nlinarith
    exact (not_le_of_gt (hcalc ▸ hhalf_neg)) hε

/- - The dual of the nonnegative polynomial cone is the Hankel positive semidefinite cone. -/
theorem dualCone_Kpol_eq_Khan (k: ℕ): dualCone (Kpol k) = Khan k := by
  apply Set.Subset.antisymm
  · -- The closed-cone separation argument gives the inclusion toward `Khan`.
    exact dualCone_Kpol_subset_Khan k
  · intro z hz
    -- Route correction: the separation route has now been used to discharge the easy inclusion
    -- `dualCone (Kpol k) ⊆ Khan k`, so the only remaining task is the SOS-style converse.
    intro x hx
    let q : Polynomial ℝ := polyOfVec x
    -- Repackage membership in `Kpol` as pointwise polynomial nonnegativity.
    have hnonneg : ∀ t : ℝ, 0 ≤ q.eval t := by
      intro t
      simpa [q, eval_polyOfVec] using hx t
    -- Record the ambient degree bound supplied by the coefficient vector length.
    have hqdeg : q.natDegree ≤ 2 * k := by
      simpa [q] using polyOfVec_natDegree_le (2 * k) x
    let e0 : EuclideanSpace ℝ (Fin (2 * k + 1)) :=
      (EuclideanSpace.equiv (Fin (2 * k + 1)) ℝ).symm fun m : Fin (2 * k + 1) =>
        if m.1 = 0 then (1 : ℝ) else 0
    have hsq_nonneg (v : EuclideanSpace ℝ (Fin (k + 1))) :
        0 ≤ ⟪z, squareCoeffVector k v⟫ := by
      -- Route correction: use positive semidefiniteness of the Hankel matrix and let the
      -- coefficient-to-quadratic rewrite be handled by simplification on the final identity.
      have hzpsd : Matrix.PosSemidef (hankelMatrix k z) := by
        simpa [Khan] using hz
      -- The Hankel quadratic form is nonnegative on every vector because `z ∈ Khan k`.
      have hquad_nonneg : 0 ≤ star v.ofLp ⬝ᵥ (hankelMatrix k z *ᵥ v.ofLp) :=
        hzpsd.dotProduct_mulVec_nonneg v.ofLp
      have hpair_eq :
          ⟪z, squareCoeffVector k v⟫ = star v.ofLp ⬝ᵥ (hankelMatrix k z *ᵥ v.ofLp) := by
        calc
          ⟪z, squareCoeffVector k v⟫ =
              ∑ m : Fin (2 * k + 1), z m * ((polyOfVec v) ^ 2).coeff m.1 := by
                -- Start from the explicit coefficient-sum formula for the pairing.
                rw [inner_squareCoeffVector_eq_coeffSum]
          _ = ∑ i : Fin (k + 1), ∑ j : Fin (k + 1), v i * (z ⟨i.1 + j.1, by
                have hi : i.1 < k + 1 := i.2
                have hj : j.1 < k + 1 := j.2
                have hsum : i.1 + j.1 ≤ 2 * k := by
                  have hi' : i.1 ≤ k := Nat.le_of_lt_succ hi
                  have hj' : j.1 ≤ k := Nat.le_of_lt_succ hj
                  calc
                    i.1 + j.1 ≤ k + k := Nat.add_le_add hi' hj'
                    _ = 2 * k := by omega
                exact Nat.lt_of_le_of_lt hsum (Nat.lt_succ_self (2 * k))⟩ * v j) := by
                -- Expand the square of `polyOfVec v` into monomials and read off the
                -- coefficient at degree `i + j`.
                simp [polyOfVec, pow_two, Finset.sum_mul, Finset.mul_sum,
                  Polynomial.C_mul_X_pow_eq_monomial, Polynomial.monomial_mul_monomial,
                  Polynomial.coeff_monomial]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl ?_
                intro j hj
                have hij_lt : i.1 + j.1 < 2 * k + 1 := by
                  have hi' : i.1 ≤ k := Nat.le_of_lt_succ i.2
                  have hj' : j.1 ≤ k := Nat.le_of_lt_succ j.2
                  have hsum : i.1 + j.1 ≤ 2 * k := by
                    calc
                      i.1 + j.1 ≤ k + k := Nat.add_le_add hi' hj'
                      _ = 2 * k := by omega
                  exact Nat.lt_of_le_of_lt hsum (Nat.lt_succ_self (2 * k))
                let m : Fin (2 * k + 1) := ⟨i.1 + j.1, hij_lt⟩
                have hm :
                    ∑ x : Fin (2 * k + 1),
                      (if j.1 + i.1 = x.1 then z.ofLp x * (v.ofLp j * v.ofLp i) else 0) =
                        z.ofLp m * (v.ofLp j * v.ofLp i) := by
                  -- Only the index `m = i + j` contributes to the coefficient sum.
                  rw [Finset.sum_eq_single m]
                  · simp [m, add_comm]
                  · intro x hx hxne
                    have hxval : j.1 + i.1 ≠ x.1 := by
                      intro h
                      apply hxne
                      exact Fin.ext <| by simpa [m, add_comm] using h.symm
                    simp [hxval]
                  · simp [m, add_comm]
                simpa [m, mul_assoc, mul_left_comm, mul_comm, add_comm] using hm
          _ = star v.ofLp ⬝ᵥ (hankelMatrix k z *ᵥ v.ofLp) := by
                -- The remaining double sum is exactly the Hankel quadratic form.
                rw [hankelQuadratic_eq_sum]
      -- Reinterpret the quadratic form bound as the desired pairing bound.
      rw [hpair_eq]
      exact hquad_nonneg
    have hpert_nonneg : ∀ ε : ℝ, ε > 0 → 0 ≤ ⟪z, x + ε • e0⟫ := by
      intro ε hε
      let qε : Polynomial ℝ := q + Polynomial.C ε
      have hqε_deg : qε.natDegree ≤ 2 * k := by
        -- Adding a constant does not increase the degree bound.
        dsimp [qε]
        exact (Polynomial.natDegree_add_le q (Polynomial.C ε)).trans <| by
          exact max_le hqdeg (by simp)
      have hqε_pos : ∀ t : ℝ, 0 < qε.eval t := by
        -- The positive constant perturbation turns nonnegativity into strict positivity.
        intro t
        dsimp [qε]
        rw [Polynomial.eval_add, Polynomial.eval_C]
        exact add_pos_of_nonneg_of_pos (hnonneg t) hε
      rcases strictPos_sum_two_squares_of_natDegree_le k qε hqε_deg hqε_pos with
        ⟨pε, rε, hqε_repr, hpε_deg, hrε_deg⟩
      let vpε : EuclideanSpace ℝ (Fin (k + 1)) :=
        (EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm fun i => pε.coeff i.1
      let vrε : EuclideanSpace ℝ (Fin (k + 1)) :=
        (EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm fun i => rε.coeff i.1
      have hvpε : polyOfVec vpε = pε := by
        -- Recover the first SOS polynomial from its coefficient vector.
        simpa [vpε] using polyOfVec_coeffs_of_natDegree_le k pε hpε_deg
      have hvrε : polyOfVec vrε = rε := by
        -- Recover the second SOS polynomial from its coefficient vector.
        simpa [vrε] using polyOfVec_coeffs_of_natDegree_le k rε hrε_deg
      have hpert_poly : polyOfVec (x + ε • e0) = qε := by
        -- Only the constant coefficient is perturbed.
        ext m
        by_cases hm : m < 2 * k + 1
        · by_cases h0 : m = 0
          · subst h0
            simp [qε, q, e0, polyOfVec_coeff]
          · simp [qε, q, polyOfVec_coeff, hm, e0, h0, Polynomial.coeff_C]
        · have hcoeff_x : (polyOfVec x).coeff m = 0 := by
            simp [polyOfVec_coeff, hm]
          have hm0 : m ≠ 0 := by
            intro hm0
            subst hm0
            exact hm (by omega)
          simp [qε, q, polyOfVec_coeff, hm, hcoeff_x, Polynomial.coeff_C, hm0]
      have hpert_sum :
          x + ε • e0 = squareCoeffVector k vpε + squareCoeffVector k vrε := by
        -- Compare the perturbed vector and the SOS vector by their coefficient polynomials.
        apply polyOfVec_injective
        calc
          polyOfVec (x + ε • e0) = qε := hpert_poly
          _ = pε ^ 2 + rε ^ 2 := hqε_repr
          _ = polyOfVec (squareCoeffVector k vpε) + polyOfVec (squareCoeffVector k vrε) := by
            rw [polyOfVec_squareCoeffVector, polyOfVec_squareCoeffVector, hvpε, hvrε]
          _ = polyOfVec (squareCoeffVector k vpε + squareCoeffVector k vrε) := by
            simp [polyOfVec, Finset.sum_add_distrib, add_mul]
      -- The perturbed vector is a sum of two square-coefficient vectors, so the pairing is
      -- nonnegative by Hankel PSD.
      rw [hpert_sum, inner_add_right]
      exact add_nonneg (hsq_nonneg vpε) (hsq_nonneg vrε)
    -- Apply the scalar perturbation lemma to the family `x + ε e0`.
    have hinner_expand : ∀ ε : ℝ, ⟪z, x + ε • e0⟫ = ⟪z, x⟫ + ε * ⟪z, e0⟫ := by
      intro ε
      rw [inner_add_right, inner_smul_right]
    have hmain : 0 ≤ ⟪z, x⟫ := by
      apply nonneg_of_forall_pos_perturb (a := ⟪z, x⟫) (b := ⟪z, e0⟫)
      intro ε hε
      simpa [hinner_expand ε] using hpert_nonneg ε hε
    exact hmain
end «problem-14»
