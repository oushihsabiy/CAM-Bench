theorem proximalOperator_comp_affine
    {n : ℕ} (g : (Fin n → ℝ) → EReal) (lam : ℝ) (a x : Fin n → ℝ) (hlam : lam ≠ 0) :
    proximalOperator (fun z => g (fun i => lam * z i + a i)) x =
      {u | (fun i => lam * u i + a i) ∈
        proximalOperator (fun z => (lam ^ 2 : EReal) * g z) (fun i => lam * x i + a i)} := by
  sorry
