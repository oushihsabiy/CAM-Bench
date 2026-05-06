theorem mem_inverseOptimalitySet_iff_exists_dualCertificates
    {n m r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin r → (Fin n → ℝ))
    (b : Fin r → (Fin m → ℝ))
    (c : Fin n → ℝ) :
    c ∈ inverseOptimalitySet A x b ↔
      ∀ j : Fin r, ∃ y : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ y i) ∧
        Matrix.mulVec Aᵀ y = c ∧
        dotProduct (b j) y = dotProduct c (x j) := by
  sorry

/- [BLOCK Exercise 4.13-(a) | 26 | thm]
Let \(A \in \mathbf{R}^{m\times n}\) be given. For each \(j=1,\dots,r\), let \(b^{(j)} \in \mathbf{R}^m\) and \(x^{(j)} \in \mathbf{R}^n\). Define
\[
C=\left\{c\in \mathbf{R}^n \mid x^{(j)} \in \operatorname*{argmin}_{x\in \mathbf{R}^n}\{c^T x \mid Ax\ge b^{(j)}\}\ \text{for every } j=1,\dots,r\right\},
\]
where \(Ax\ge b^{(j)}\) is interpreted componentwise. For a fixed index \(i\in\{1,\dots,n\}\), define
\[
c_i^{\max}=\sup\{c_i\mid c\in C\},\qquad c_i^{\min}=\inf\{c_i\mid c\in C\}.
\]
Prove that \(c_i^{\max}\) and \(c_i^{\min}\) are the optimal values of the linear programs inverse optimality maximization LP and inverse optimality minimization LP, respectively.
-/
