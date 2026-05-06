theorem censored_least_squares_equiv
    (K n M : ℕ)
    (hM : M ≤ K)
    (D : ℝ)
    (x : Fin K → EuclideanSpace ℝ (Fin n))
    (yObs : Fin M → ℝ) :
    let J : EuclideanSpace ℝ (Fin n) → (Fin (K - M) → ℝ) → ℝ :=
      fun c yTail =>
        (∑ k : Fin M, (yObs k - ⟪c, x ⟨k, lt_of_lt_of_le k.2 hM⟩⟫) ^ 2) +
          ∑ k : Fin (K - M),
            ((yTail k) - ⟪c, x ⟨M + k.1, by
              have hk : M + k.1 < M + (K - M) := Nat.add_lt_add_left k.2 M
              simpa [Nat.add_sub_of_le hM] using hk
            ⟩⟫) ^ 2
    let feasible : (Fin (K - M) → ℝ) → Prop :=
      fun yTail => ∀ k, D ≤ yTail k
    let F : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun c =>
        (∑ k : Fin M, (yObs k - ⟪c, x ⟨k, lt_of_lt_of_le k.2 hM⟩⟫) ^ 2) +
          ∑ k : Fin (K - M),
            (max (D - ⟪c, x ⟨M + k.1, by
              have hk : M + k.1 < M + (K - M) := Nat.add_lt_add_left k.2 M
              simpa [Nat.add_sub_of_le hM] using hk
            ⟩⟫) 0) ^ 2
    ((∀ cStar : EuclideanSpace ℝ (Fin n),
        IsLeast (Set.range F) (F cStar) ↔
          ∃ yTail : Fin (K - M) → ℝ,
            feasible yTail ∧
            IsLeast
              {r : ℝ | ∃ c yTail', feasible yTail' ∧ J c yTail' = r}
              (J cStar yTail)) ∧
      (∀ cStar : EuclideanSpace ℝ (Fin n),
        IsLeast (Set.range F) (F cStar) →
          ∃ yTail : Fin (K - M) → ℝ,
            feasible yTail ∧
            IsLeast
              {r : ℝ | ∃ c yTail', feasible yTail' ∧ J c yTail' = r}
              (J cStar yTail) ∧
            (∀ k : Fin (K - M),
              let idx : Fin K := ⟨M + k.1, by
                have hk : M + k.1 < M + (K - M) := Nat.add_lt_add_left k.2 M
                simpa [Nat.add_sub_of_le hM] using hk
              ⟩
              yTail k = max D ⟪cStar, x idx⟫))) := by
  sorry
