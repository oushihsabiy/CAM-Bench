theorem ComplexPNormApproximationP1SOCP_equiv
    (P : ComplexPNormApproximation) :
    P.p = 1 →
    ∃ Q : ComplexPNormApproximationP1SOCP, Q.objectiveSource = P := by
  intro hp
  refine ⟨{
    n := P.n
    objectiveSource := P
    h_n := rfl
    m := P.n
    h_m := rfl
    h_p := hp
    u := fun _ => 0
    v := fun _ => 0
    t := fun i =>
      Real.sqrt
        ((Complex.re (P.residual (fun j => ((0 : ℝ) : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) i)) ^ 2 +
         (Complex.im (P.residual (fun j => ((0 : ℝ) : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) i)) ^ 2)
    r := fun i =>
      Complex.re (P.residual (fun j => ((0 : ℝ) : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) i)
    s := fun i =>
      Complex.im (P.residual (fun j => ((0 : ℝ) : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) i)
    residual_real := by
      intro i
      rfl
    residual_imag := by
      intro i
      rfl
    coneConstraint := by
      intro i
      exact le_rfl
  }, rfl⟩

/- [BLOCK Exercise 4.24 | 15 | opt_prob]
For p=2, this is equivalent to the real SOCP
array{ll}
minimize & t ;
subject to & sqrt{sum_{i=1}^m (rᵢ^2+sᵢ^2)}≤ t,
array
with variables u,v∈ mathbf ℝ^n and t∈ mathbf R. Equivalently, it is the QCQP
array{ll}
minimize & t ;
subject to & sum_{i=1}^m (rᵢ^2+sᵢ^2)≤ t^2, quad t≥ 0.
array
-/
structure ComplexPNormApproximationP2Model where
  n : ℕ
  objectiveSource : ComplexPNormApproximation
  h_n : objectiveSource.n = n
  m : ℕ
  h_m : m = objectiveSource.n
  h_p : objectiveSource.p = 2
  u : Fin n → ℝ
  v : Fin n → ℝ
  t : ℝ
  r : Fin m → ℝ
  s : Fin m → ℝ
  residual_real :
    ∀ i : Fin m,
      r i = Complex.re (objectiveSource.residual (fun j =>
        (u (Fin.cast h_n j) : ℂ) + Complex.I * (v (Fin.cast h_n j) : ℂ))
        (Fin.cast h_m i))
  residual_imag :
    ∀ i : Fin m,
      s i = Complex.im (objectiveSource.residual (fun j =>
        (u (Fin.cast h_n j) : ℂ) + Complex.I * (v (Fin.cast h_n j) : ℂ))
        (Fin.cast h_m i))
  socConstraint : Prop
  socConstraint_def :
    socConstraint ↔
      Real.sqrt (Finset.univ.sum (fun i : Fin m => (r i) ^ 2 + (s i) ^ 2)) ≤ t
  qcqpConstraint : Prop
  qcqpConstraint_def :
    qcqpConstraint ↔
      (Finset.univ.sum (fun i : Fin m => (r i) ^ 2 + (s i) ^ 2)) ≤ t ^ 2 ∧ 0 ≤ t