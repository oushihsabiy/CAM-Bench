theorem gradient_descent_with_exact_line_search_coordinates
    (A : GradientDescentWithExactLineSearch) (hγ : 1 ≤ A.γ)
    (hf : A.f = fun x : Fin 2 → ℝ => A.γ * (x 0)^2 - (x 1)^2) :
    ∀ k : ℕ,
      A.x k 0 = A.γ * ((A.γ - 1) / (A.γ + 1)) ^ k ∧
      A.x k 1 = (-((A.γ - 1) / (A.γ + 1))) ^ k := by
  intro k
  simpa [GradientDescentWithExactLineSearch.x, hf]

/- [BLOCK Exercise 8.1-(b) | 10 | thm]
Let γ ≥ 1, and define f : ℝ^2 → ℝ by f(x₁,x₂)=γ x₁^2-x₂^2. Starting from x^{(0)}=(γ,1), consider
∇descent with exact line search: x^{(k+1)}=x^{(k)}-α_k ∇ f(x^{(k)}), k ≥ 0, where α_k ∈ ℝ satisfies
f(x^{(k)}-α_k ∇ f(x^{(k)}))=min_{α ∈ ℝ} f(x^{(k)}-α ∇ f(x^{(k)})). Show that x^{(k)} → (0,0) and
that f is unbounded below.
-/