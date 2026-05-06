theorem augmentedSystem_iff_normalEquation
    {n m : ℕ}
    (hm : 1 ≤ m)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ)
    (y : Fin m → ℝ)
    (lam : Fin m → ℝ)
    (σ : ℝ)
    (hy : ∀ i : Fin m, y i ≠ 0)
    (hlam : ∀ i : Fin m, lam i ≠ 0)
    (Δx : Fin n → ℝ) :
    let Y : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal y
    let Lambda : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal lam
    let μ : ℝ := (∑ i : Fin m, y i * lam i) / (m : ℝ)
    let r_d : Fin n → ℝ := fun i => (G.mulVec x) i - (A.transpose.mulVec lam) i + c i
    let r_p : Fin m → ℝ := fun i => (A.mulVec x) i - y i - b i
    ((∃ Δlam : Fin m → ℝ,
        (augmentedSystem G A Lambda Y r_d r_p y σ μ).1.mulVec (Sum.elim Δx Δlam) =
          (augmentedSystem G A Lambda Y r_d r_p y σ μ).2) →
      (normalEquation G A Lambda Y r_d r_p y σ μ).1.mulVec Δx =
        (normalEquation G A Lambda Y r_d r_p y σ μ).2) ∧
    ((normalEquation G A Lambda Y r_d r_p y σ μ).1.mulVec Δx =
        (normalEquation G A Lambda Y r_d r_p y σ μ).2 →
      let Δlam_formula : Fin m → ℝ :=
        fun i =>
          (Y⁻¹.mulVec
            (Lambda.mulVec
              (fun j => -r_p j - y j + σ * μ * ((Lambda⁻¹.mulVec (fun _ => 1)) j) -
                (A.mulVec Δx) j))) i
      let Δy : Fin m → ℝ := fun i => (A.mulVec Δx) i + r_p i
      (primalDualSystem G A Lambda Y r_d r_p σ μ).1.mulVec
          (Fin.append (Fin.append Δx Δy) Δlam_formula) =
        (primalDualSystem G A Lambda Y r_d r_p σ μ).2) := by
  sorry
