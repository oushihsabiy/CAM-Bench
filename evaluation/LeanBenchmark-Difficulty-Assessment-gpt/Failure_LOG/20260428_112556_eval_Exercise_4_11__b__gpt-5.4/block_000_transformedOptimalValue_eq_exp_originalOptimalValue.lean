theorem transformedOptimalValue_eq_exp_originalOptimalValue
    (P : ConvexProgramPair)
    (h_attains : ∃ x ∈ P.feasibleSet, ∀ y ∈ P.feasibleSet, P.originalObjective x ≤ P.originalObjective y) :
    P.transformedOptimalValue = Real.exp P.originalOptimalValue := by
  sorry

/- [BLOCK Exercise 4.11-(b) | 20 | thm]
Let \(f_i:\mathbf{R}^n\to\mathbf{R}\), \(i=0,1,\ldots,m\), be convex differentiable functions. Consider the problems
\[
\begin{aligned}
\text{minimize} \quad & f_0(x)\\
\text{subject to} \quad & f_i(x)\le 0, \quad i=1,\ldots,m.
\end{aligned}
\tag{13}
\]
and
\[
\begin{aligned}
\text{minimize} \quad & \tilde f_0(x)=\exp(f_0(x))\\
\text{subject to} \quad & f_i(x)\le 0, \quad i=1,\ldots,m.
\end{aligned}
\tag{14}
\]
For problem \((13)\), define
\(L(x,\lambda)=f_0(x)+\sum_{i=1}^m \lambda_i f_i(x), \qquad \lambda\in\mathbf{R}^m,\)
and
\(g(\lambda)=\inf_{x\in\mathbf{R}^n} L(x,\lambda).\)
For problem \((14)\), define
\(\tilde L(x,\tilde\lambda)=\exp(f_0(x))+\sum_{i=1}^m \tilde\lambda_i f_i(x), \qquad \tilde\lambda\in\mathbf{R}^m,\)
and
\(\tilde g(\tilde\lambda)=\inf_{x\in\mathbf{R}^n} \tilde L(x,\tilde\lambda).\)
Assume \(\lambda\ge 0\) componentwise, and define \(\tilde\lambda = \exp(g(\lambda))\,\lambda\). Prove that
\[\log \tilde g(\tilde\lambda) \ge g(\lambda).\]
In particular, the lower bound obtained from the dual of problem \((14)\) is at least as strong as the lower bound obtained from the dual of problem \((13)\).
-/
