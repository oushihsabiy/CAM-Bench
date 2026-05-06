theorem primalDualMatrix_nonsingular_of_LICQ_strictComplementarity_secondOrder
    {n mₑ mᵢ : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (cE : Fin mₑ → (Fin n → ℝ) → ℝ)
    (cI : Fin mᵢ → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ)
    (s : Fin mᵢ → ℝ)
    (y : Fin mₑ → ℝ)
    (z : Fin mᵢ → ℝ)
    (hNLP : IsNonlinearProgrammingProblem n mₑ mᵢ f cE cI)
    (hxeq : ∀ i, cE i x = 0)
    (hxs : ∀ i, cI i x - s i = 0)
    (hs_nonneg : ∀ i, 0 ≤ s i)
    (hz_nonneg : ∀ i, 0 ≤ z i)
    (hcomp : ∀ i, s i * z i = 0)
    (hSC : StrictComplementarity mᵢ s z)
    (hLICQ :
      LinearIndependent ℝ
        (fun k : (Fin mₑ) ⊕ {i : Fin mᵢ // s i = 0} =>
          match k with
          | Sum.inl i => fderiv ℝ (cE i) x
          | Sum.inr i => fderiv ℝ (cI i.1) x))
    (hC2 :
      ContDiffAt ℝ 2
        (fun x' =>
          f x'
            - ∑ ie : Fin mₑ, y ie * cE ie x'
            - ∑ ii : Fin mᵢ, z ii * cI ii x')
        x)
    (hpos :
      let H : Matrix (Fin n) (Fin n) ℝ :=
        fun i j =>
          fderiv ℝ
            (fun x' =>
              fderiv ℝ
                (fun x'' =>
                  f x''
                    - ∑ ie : Fin mₑ, y ie * cE ie x''
                    - ∑ ii : Fin mᵢ, z ii * cI ii x'')
                x' (Pi.single j (1 : ℝ)))
            x (Pi.single i (1 : ℝ))
      let A : Matrix ((Fin mₑ) ⊕ {i : Fin mᵢ // s i = 0}) (Fin n) ℝ :=
        fun i j =>
          match i with
          | Sum.inl ie => fderiv ℝ (cE ie) x (Pi.single j (1 : ℝ))
          | Sum.inr ii => fderiv ℝ (cI ii.1) x (Pi.single j (1 : ℝ))
      ∀ d : Fin n → ℝ,
        A.mulVec d = 0 →
        d ≠ 0 →
        0 < dotProduct d (H.mulVec d)) :
    let AE : Matrix (Fin mₑ) (Fin n) ℝ :=
      fun i j => fderiv ℝ (cE i) x (Pi.single j (1 : ℝ))
    let AI : Matrix (Fin mᵢ) (Fin n) ℝ :=
      fun i j => fderiv ℝ (cI i) x (Pi.single j (1 : ℝ))
    let H : Matrix (Fin n) (Fin n) ℝ :=
      fun i j =>
        fderiv ℝ
          (fun x' =>
            fderiv ℝ
              (fun x'' =>
                f x''
                  - ∑ ie : Fin mₑ, y ie * cE ie x''
                  - ∑ ii : Fin mᵢ, z ii * cI ii x'')
              x' (Pi.single j (1 : ℝ)))
          x (Pi.single i (1 : ℝ))
    let Z : Matrix (Fin mᵢ) (Fin mᵢ) ℝ := Matrix.diagonal z
    let S : Matrix (Fin mᵢ) (Fin mᵢ) ℝ := Matrix.diagonal s
    let e_left : (Fin n ⊕ Fin mᵢ) ≃ Fin (n + mᵢ) := @finSumFinEquiv n mᵢ
    let e_mid : ((Fin n ⊕ Fin mᵢ) ⊕ Fin mₑ) ≃ Fin ((n + mᵢ) + mₑ) :=
      (Equiv.sumCongr e_left (Equiv.refl _)).trans (@finSumFinEquiv (n + mᵢ) mₑ)
    let e : (((Fin n ⊕ Fin mᵢ) ⊕ Fin mₑ) ⊕ Fin mᵢ) ≃ Fin (((n + mᵢ) + mₑ) + mᵢ) :=
      (Equiv.sumCongr e_mid (Equiv.refl _)).trans (@finSumFinEquiv ((n + mᵢ) + mₑ) mᵢ)
    IsNonsingular
      (Matrix.reindex e e
        (fun i j =>
          match i, j with
          | Sum.inl (Sum.inl (Sum.inl i1)), Sum.inl (Sum.inl (Sum.inl j1)) => H i1 j1
          | Sum.inl (Sum.inl (Sum.inl i1)), Sum.inl (Sum.inl (Sum.inr _)) => 0
          | Sum.inl (Sum.inl (Sum.inl i1)), Sum.inl (Sum.inr j3) => -AE.transpose i1 j3
          | Sum.inl (Sum.inl (Sum.inl i1)), Sum.inr j4 => -AI.transpose i1 j4
          | Sum.inl (Sum.inl (Sum.inr i2)), Sum.inl (Sum.inl (Sum.inl _)) => 0
          | Sum.inl (Sum.inl (Sum.inr i2)), Sum.inl (Sum.inl (Sum.inr j2)) => Z i2 j2
          | Sum.inl (Sum.inl (Sum.inr _)), Sum.inl (Sum.inr _) => 0
          | Sum.inl (Sum.inl (Sum.inr i2)), Sum.inr j4 => S i2 j4
          | Sum.inl (Sum.inr i3), Sum.inl (Sum.inl (Sum.inl j1)) => AE i3 j1
          | Sum.inl (Sum.inr _), Sum.inl (Sum.inl (Sum.inr _)) => 0
          | Sum.inl (Sum.inr _), Sum.inl (Sum.inr _) => 0
          | Sum.inl (Sum.inr _), Sum.inr _ => 0
          | Sum.inr i4, Sum.inl (Sum.inl (Sum.inl j1)) => AI i4 j1
          | Sum.inr i4, Sum.inl (Sum.inl (Sum.inr j2)) =>
              (-(1 : Matrix (Fin mᵢ) (Fin mᵢ) ℝ)) i4 j2
          | Sum.inr _, Sum.inl (Sum.inr _) => 0
          | Sum.inr _, Sum.inr _ => 0)) := by
  sorry
