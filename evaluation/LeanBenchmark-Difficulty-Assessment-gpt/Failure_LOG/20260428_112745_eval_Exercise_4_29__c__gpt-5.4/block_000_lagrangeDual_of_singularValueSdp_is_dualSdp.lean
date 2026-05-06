theorem lagrangeDual_of_singularValueSdp_is_dualSdp
    {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ)
    (hmn : Fintype.card n ≤ Fintype.card m)
    (hk₁ : 1 ≤ k) (hk₂ : k ≤ Fintype.card n)
    (R : SDPRepresentation)
    (hrep : R.representsFunction
      (fun _ =>
        ∑ i : Fin k,
          singularValues A
            ⟨i.1, by
              have hi_n : i.1 < Fintype.card n := Nat.lt_of_lt_of_le i.2 hk₂
              simpa [Nat.min_eq_right hmn] using hi_n⟩))
    :
    -- Strong duality: f(A) = sum of top-k singular values = optimal value of dual SDP
    ∑ i : Fin k,
      singularValues A
        ⟨i.1, by
          have hi_n : i.1 < Fintype.card n := Nat.lt_of_lt_of_le i.2 hk₂
          simpa [Nat.min_eq_right hmn] using hi_n⟩ =
    sSup {v : ℝ | ∃ X : Matrix m n ℝ, ∃ Z : Matrix n n ℝ,
      DualSingularValueSdpProblem.isFeasible { A := A, k := (k : ℝ) } X Z ∧
      v = DualSingularValueSdpProblem.objective { A := A, k := (k : ℝ) } X} := by
  sorry

/- [BLOCK Exercise 4.29-(c) | 67 | thm]
Let A \in \mathbf{R}^{m \times n} with m \ge n, and let k be an integer with 1 \le k \le n. Define f(A)=\sigma_1(A)+\cdots+\sigma_k(A), where \sigma_1(A),\ldots,\sigma_n(A) are the singular values of A, ordered by \sigma_1(A)\ge \sigma_2(A)\ge \cdots \ge \sigma_n(A)\ge 0. Moreover, for given matrices A_0,\ldots,A_p \in \mathbf{R}^{m \times n}, prove that \inf_{x\in \mathbf{R}^p} f(A_0+x_1A_1+\cdots+x_pA_p) is equal to the optimal value of the SDP affine dual SDP.
-/
