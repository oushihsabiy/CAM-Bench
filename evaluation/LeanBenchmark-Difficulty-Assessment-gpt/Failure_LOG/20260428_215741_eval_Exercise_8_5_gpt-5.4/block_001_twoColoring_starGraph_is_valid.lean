theorem twoColoring_starGraph_is_valid
    (n : ℕ) (hn : 1 ≤ n)
    (c : Fin n → ℕ)
    (hc0 : c ⟨0, hn⟩ = 0)
    (hc1 : ∀ i : Fin n, i ≠ ⟨0, hn⟩ → c i = 1) :
    validColoring
      (adjacencyGraph n
        (fun x : Fin n → ℝ =>
          x ⟨0, hn⟩ * ∑ i : Fin n, ((i.1 + 1 : ℕ) : ℝ)^2 * (x i)^2))
      c := by
  sorry

/- [BLOCK Exercise 8.5 | 23 | thm]
Let n ∈ ℕ with n ≥ 1, and define f : ℝ^n → ℝ by f(x)=x₁sum_{i=1}^n i^2 xᵢ^2, where x=(x₁,ldots,xₙ) ∈
ℝ^n. The intersection graph for ∇ f is the undirected graph with vertex set {1,2,ldots,n}, where
distinct vertices i and j are adjacent if there exist k ∈ {1,2,ldots,n} and x ∈ ℝ^n such that (∂^2
f)/(∂ xₖ∂ xᵢ)(x)ne 0 quadandquad (∂^2 f)/(∂ xₖ∂ xⱼ)(x)ne 0. Prove that in the intersection graph for
∇ f, every two distinct vertices are adjacent; equivalently, the intersection graph is the complete
graph on {1,2,ldots,n}.
-/
