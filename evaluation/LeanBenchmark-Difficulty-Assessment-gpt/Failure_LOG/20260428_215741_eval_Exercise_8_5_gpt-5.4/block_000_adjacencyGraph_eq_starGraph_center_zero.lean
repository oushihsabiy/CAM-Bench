theorem adjacencyGraph_eq_starGraph_center_zero
    (n : ℕ) (hn : 1 ≤ n) :
    adjacencyGraph n
      (fun x : Fin n → ℝ =>
        x ⟨0, hn⟩ * ∑ i : Fin n, ((i.1 + 1 : ℕ) : ℝ)^2 * (x i)^2) =
      starGraph n ⟨0, hn⟩ := by
  sorry

/- [BLOCK Exercise 8.5 | 22 | thm]
Let n ∈ ℕ with n ≥ 1, and define f : ℝ^n → ℝ by f(x)=x₁sum_{i=1}^n i^2 xᵢ^2, where x=(x₁,ldots,xₙ) ∈
ℝ^n. The adjacency graph of f is the undirected graph with vertex set {1,2,ldots,n}, where distinct
vertices i and j are adjacent if there exists x ∈ ℝ^n such that (∂^2 f)/(∂ xᵢ∂ xⱼ)(x)ne 0. A
coloring of this graph is valid if adjacent vertices have different colors. Prove that the coloring
in which vertex 1 has one color and all vertices 2,3,ldots,n have another color is valid.
-/
