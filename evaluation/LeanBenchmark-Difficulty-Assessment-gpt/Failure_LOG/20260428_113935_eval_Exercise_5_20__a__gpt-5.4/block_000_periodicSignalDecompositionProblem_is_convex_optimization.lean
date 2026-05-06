theorem periodicSignalDecompositionProblem_is_convex_optimization
    (n pMax : ℕ)
    (hpMax_pos : 1 ≤ pMax)
    (hpMax_lt : pMax < n)
    (y : Fin n → ℝ)
    (w : Fin pMax → ℝ)
    (hw_nonneg : ∀ p : Fin pMax, 0 ≤ w p)
    (hw_mono : Monotone w)
    (L : Fin pMax → Set (Fin n → ℝ))
    (hL_periodic :
      ∀ p : Fin pMax,
        L p =
          {x | ∀ i : Fin (n - (p.1 + 1)), x ⟨i.1 + (p.1 + 1), by
              have hi : i.1 < n - (p.1 + 1) := i.2
              have hp : p.1 + 1 ≤ n := Nat.succ_le_of_lt (lt_of_lt_of_le p.2 (Nat.le_of_lt hpMax_lt))
              omega⟩ = x ⟨i.1, by
                exact lt_of_lt_of_le i.2 (Nat.sub_le n (p.1 + 1))⟩}) :
    let feasibleSet : Set ((Fin n → ℝ) × (Fin pMax → Fin n → ℝ)) :=
      {z | (z.1 = fun i => ∑ p, z.2 p i) ∧ ∀ p, z.2 p ∈ L p}
    let objective : ((Fin n → ℝ) × (Fin pMax → Fin n → ℝ)) → ℝ :=
      fun z => (∑ i, (y i - z.1 i) ^ 2) + ∑ p, w p * ‖z.2 p‖
    Convex ℝ feasibleSet ∧ ConvexOn ℝ feasibleSet objective := by
  sorry

/- [BLOCK Exercise 5.20-(a) | 26 | thm]
Let n,p_{max} ∈ N satisfy 1 ≤ p_{max} < n. For each integer p with 1 ≤ p ≤ p_{max}, define
L_p={x∈ ℝ^n | x_{i+p}=xᵢ for i=1,ldots,n-p}.
Let y∈ ℝ^n and w=(w₁,ldots,w_{p_{max}})∈ ℝ^{p_{max}} satisfy 0≤ w₁≤ w₂≤ ·s ≤ w_{p_{max}}. Consider
the periodic signal decomposition problem. Moreover, if (hat y*,(x^{(p),*})_{p=1}^{p_{max}}) is an
optimal solution, then an approximate recovery of the latent periods is given by
mathcal P={p∈ {1,ldots,p_{max}}| x^{(p),*}neq 0},
and an approximate recovery of the latent periodic signals is given by the nonzero optimal
components x^{(p),*} for p∈ mathcal P.
-/
