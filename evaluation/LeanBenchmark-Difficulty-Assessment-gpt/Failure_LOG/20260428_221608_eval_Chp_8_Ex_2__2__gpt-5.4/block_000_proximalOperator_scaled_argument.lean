theorem proximalOperator_scaled_argument
    {n : ℕ} (g : (Fin n → ℝ) → EReal)
    (hproper : ∃ x : Fin n → ℝ, g x ≠ ⊤ ∧ g x ≠ ⊥)
    (hlsc : LowerSemicontinuous g)
    (hconv : Convex ℝ {p : (Fin n → ℝ) × ℝ | g p.1 ≤ (p.2 : EReal)})
    (lam : ℝ) (hlam : 0 < lam) :
    let h : (Fin n → ℝ) → EReal := fun x => (lam : EReal) * g (fun i => x i / lam)
    ∀ x : Fin n → ℝ,
      proximalOperator h x =
        Set.image
          (fun z : Fin n → ℝ => lam • z)
          (proximalOperator (fun u => ((lam⁻¹ : ℝ) : EReal) * g u) (fun i => x i / lam)) := by
  sorry
