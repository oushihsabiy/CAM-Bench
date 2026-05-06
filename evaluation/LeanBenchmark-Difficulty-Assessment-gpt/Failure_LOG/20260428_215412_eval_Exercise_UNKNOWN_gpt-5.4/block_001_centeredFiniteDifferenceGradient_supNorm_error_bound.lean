theorem centeredFiniteDifferenceGradient_supNorm_error_bound
    {n : ℕ}
    (f h : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ)
    (ε Lh : ℝ)
    (hε : 0 < ε)
    (hLh : 0 ≤ Lh)
    (h_diff :
      ∃ s : Set ((Fin n → ℝ)),
        IsOpen s ∧
        {z : Fin n → ℝ | ∀ i : Fin n, |z i - x i| ≤ ε} ⊆ s ∧
        ∀ z ∈ s, DifferentiableAt ℝ h z)
    (h_lipschitz :
      ∀ u v : Fin n → ℝ,
        (∀ i : Fin n, |u i - x i| ≤ ε) →
        (∀ i : Fin n, |v i - x i| ≤ ε) →
        sSup (Set.range fun i : Fin n =>
          |((fderiv ℝ h u) (fun j => if j = i then (1 : ℝ) else 0)) -
           ((fderiv ℝ h v) (fun j => if j = i then (1 : ℝ) else 0))|) ≤
        Lh * sSup (Set.range fun i : Fin n => |u i - v i|))
    :
    sSup (Set.range fun i : Fin n =>
      |(centeredFiniteDifferenceGradient f x ε hε) i -
        (fderiv ℝ h x) (fun j => if j = i then (1 : ℝ) else 0)|) ≤
      Lh * ε ^ 2 +
        (sSup (Set.range fun i : Fin n =>
          |f (x + fun j => if j = i then ε else 0) - h (x + fun j => if j = i then ε else 0)|) +
        sSup (Set.range fun i : Fin n =>
          |f (x - fun j => if j = i then ε else 0) - h (x - fun j => if j = i then ε else 0)|)) / ε := by
  sorry
