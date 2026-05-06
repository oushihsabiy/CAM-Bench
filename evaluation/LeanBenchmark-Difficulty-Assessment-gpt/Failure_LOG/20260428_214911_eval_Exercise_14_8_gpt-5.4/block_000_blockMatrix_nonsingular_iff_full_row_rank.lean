theorem blockMatrix_nonsingular_iff_full_row_rank
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (X S : Matrix (Fin n) (Fin n) ℝ)
    (hXdiag : X.IsDiag) (hSdiag : S.IsDiag)
    (hXpos : ∀ i : Fin n, 0 < X i i)
    (hSpos : ∀ i : Fin n, 0 < S i i) :
    IsUnit
        (Matrix.det
          (fun i j : (Fin n ⊕ Fin m) ⊕ Fin n =>
            match i, j with
            | Sum.inl (Sum.inl i1), Sum.inl (Sum.inl j1) => (0 : ℝ)
            | Sum.inl (Sum.inl i1), Sum.inl (Sum.inr j2) => A j2 i1
            | Sum.inl (Sum.inl i1), Sum.inr j3 => if i1 = j3 then 1 else 0
            | Sum.inl (Sum.inr i2), Sum.inl (Sum.inl j1) => A i2 j1
            | Sum.inl (Sum.inr i2), Sum.inl (Sum.inr j2) => 0
            | Sum.inl (Sum.inr i2), Sum.inr j3 => 0
            | Sum.inr i3, Sum.inl (Sum.inl j1) => S i3 j1
            | Sum.inr i3, Sum.inl (Sum.inr j2) => 0
            | Sum.inr i3, Sum.inr j3 => X i3 j3)) ↔
      Function.Surjective (Matrix.mulVecLin A) := by
  sorry
