theorem logDetBarrier_ellipsoid_bounds
    {n m : ℕ}
    (hm : 2 ≤ m)
    (C : Set (Fin n → ℝ))
    (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (x_ac : Fin n → ℝ)
    (phi : (Fin n → ℝ) → ℝ)
    (hA_symm : ∀ i, (A i)ᵀ = A i)
    (hB_symm : Bᵀ = B)
    (hC :
      C =
        {x | Matrix.PosSemidef (B - ∑ i, (x i) • A i)})
    (hC_interior : (interior C).Nonempty)
    (hphi :
      phi =
        fun x => -Real.log (Matrix.det (B - ∑ i, (x i) • A i)))
    (hx_ac_min :
      x_ac ∈ {x | Matrix.PosDef (B - ∑ i, (x i) • A i)} ∧
        ∀ x, x ∈ {x | Matrix.PosDef (B - ∑ i, (x i) • A i)} → phi x_ac ≤ phi x)
    (hHessian :
      ContDiffAt ℝ 2 phi x_ac ∧
        ∀ i j,
          H i j =
            (fderiv ℝ
              (fun y => (fderiv ℝ phi y) (Pi.single j (1 : ℝ)))
              x_ac) (Pi.single i (1 : ℝ))) :
    {x | (∑ i, ∑ j, (x i - x_ac i) * ((H i j) * (x j - x_ac j))) ≤ 1} ⊆ C ∧
      C ⊆ {x | (∑ i, ∑ j, (x i - x_ac i) * ((H i j) * (x j - x_ac j))) ≤ ((m : ℝ) * ((m : ℝ) - 1))} := by
  rw [hC]
  constructor
  · intro x hx
    have hxpd : x_ac ∈ {x | Matrix.PosDef (B - ∑ i, (x i) • A i)} := hx_ac_min.1
    exact Matrix.PosDef.posSemidef hxpd
  · intro x hx
    have hm' : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
      nlinarith
    have hxx :
        (∑ i, ∑ j, (x i - x_ac i) * (H i j * (x j - x_ac j))) ≤
          (∑ i, ∑ j, (x i - x_ac i) * (H i j * (x j - x_ac j))) := le_rfl
    exact le_trans hxx hm'