theorem infimum_affine_singular_value_sum_eq_affine_dual_sdp_optimal_value
    {p m n : ℕ}
    (hmn : n ≤ m) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n)
    (A₀ : Matrix (Fin m) (Fin n) ℝ) (A : Fin p → Matrix (Fin m) (Fin n) ℝ) :
    sInf {r : ℝ |
      ∃ x : Fin p → ℝ,
        r =
          ∑ i : Fin k,
            singularValues (A₀ + ∑ j, x j • A j)
              ⟨i.1, by
                have hi_n : i.1 < n := Nat.lt_of_lt_of_le i.2 hk2
                simpa [Nat.min_eq_right hmn] using hi_n⟩} =
    -- optimal value of the affine dual SDP: maximize tr(A₀ᵀX) over all feasible (X,Z)
    -- feasibility = AffineDualSingularValueSdpProblem constraints (block PSD, tr AⱼᵀX = 0, tr Z = k)
    sSup {v : ℝ |
      ∃ P : AffineDualSingularValueSdpProblem (Fin p) (Fin m) (Fin n),
        P.A₀ = A₀ ∧ P.A = A ∧ P.k = (k : ℝ) ∧ v = P.objective} := by
  sorry
