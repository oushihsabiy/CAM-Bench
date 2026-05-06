theorem separableEqualityConstrained_dualFunction_eq_neg_dot_sub_sum_psi
    (n p : ℕ)
    (A : Fin p → Fin n → ℝ)
    (b : Fin p → ℝ)
    (c : ℝ)
    (hc : 0 < c)
    (nu : Fin p → ℝ) :
    -- inf over the domain {x | ∀ i, |x i| < c} (where φ is finite)
    sInf
        ((fun x : Fin n → ℝ =>
            (∑ i : Fin n, |x i| / (c - |x i|)) +
            ∑ j : Fin p, nu j * ((∑ i : Fin n, A j i * x i) - b j)) ''
          {x : Fin n → ℝ | ∀ i : Fin n, |x i| < c})
      =
      -∑ j : Fin p, b j * nu j
        - ∑ i : Fin n, (if |∑ j : Fin p, A j i * nu j| ≤ 1 / c then 0
            else (Real.sqrt (c * |∑ j : Fin p, A j i * nu j|) - 1) ^ 2) := by
  sorry

/- [BLOCK Exercise 4.20 | 44 | thm]
Let \(A \in \mathbf{R}^{m \times n}\), \(b \in \mathbf{R}^m\), and \(c>0\). Define \(\phi:\mathbf{R}\to \mathbf{R}\cup\{+\infty\}\) by
\[
\phi(u)=\begin{cases}
\dfrac{|u|}{c-|u|}, & |u|<c,\\
+\infty, & \text{otherwise}.
\end{cases}
\]
Consider the separable equality-constrained primal problem. For \(\nu\in\mathbf{R}^m\), define the Lagrangian
\[
L(x,\nu)=\sum_{i=1}^n \phi(x_i)+\nu^T(Ax-b)
\]
and the dual function
\[
g(\nu)=\inf_{x\in\mathbf{R}^n} L(x,\nu).
\]
Hence prove that the Lagrange dual problem is
\[
\begin{aligned}
\text{maximize} \quad & -b^T\nu-\sum_{i=1}^n \psi\big((A^T\nu)_i\big) \\
\text{subject to} \quad & \nu\in\mathbf{R}^m.
\end{aligned}
\]
where
\[
\psi(t)=\begin{cases}
0, & |t|\le \dfrac1c,\\
\big(\sqrt{c|t|}-1\big)^2, & |t|>\dfrac1c.
\end{cases}
\]
-/
