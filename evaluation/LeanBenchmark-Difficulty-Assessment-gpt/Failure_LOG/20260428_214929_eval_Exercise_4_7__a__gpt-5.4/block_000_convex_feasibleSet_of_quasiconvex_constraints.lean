theorem convex_feasibleSet_of_quasiconvex_constraints
    {n p m : ℕ}
    (A : Matrix (Fin p) (Fin n) ℝ)
    (b : Fin p → ℝ)
    (c : Fin n → ℝ)
    (d : ℝ)
    (f0 : (Fin n → ℝ) → WithTop ℝ)
    (f : Fin m → (Fin n → ℝ) → WithTop ℝ)
    (hf0 : Convex ℝ {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)})
    (hf : ∀ i : Fin m,
      Convex ℝ {xt : (Fin n → ℝ) × ℝ | f i xt.1 ≤ (xt.2 : WithTop ℝ)}) :
    Convex ℝ
      {x : Fin n → ℝ |
        (∀ i : Fin m, f i x ≤ (0 : WithTop ℝ)) ∧
        Matrix.mulVec A x = b ∧
        f0 x < ⊤ ∧
        (∑ j : Fin n, c j * x j) + d > 0} := by
  intro x hx y hy a b' ha hb hab
  rcases hx with ⟨hx_f, hx_eq, hx_f0, hx_pos⟩
  rcases hy with ⟨hy_f, hy_eq, hy_f0, hy_pos⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hmemx :
        ((x, (0 : ℝ)) : (Fin n → ℝ) × ℝ) ∈
          {xt : (Fin n → ℝ) × ℝ | f i xt.1 ≤ (xt.2 : WithTop ℝ)} :=
      hx_f i
    have hmemy :
        ((y, (0 : ℝ)) : (Fin n → ℝ) × ℝ) ∈
          {xt : (Fin n → ℝ) × ℝ | f i xt.1 ≤ (xt.2 : WithTop ℝ)} :=
      hy_f i
    have hconv := hf i hmemx hmemy ha hb hab
    simpa [Prod.smul_mk, Prod.mk.add_mk] using hconv
  · calc
      Matrix.mulVec A (a • x + b' • y)
          = Matrix.mulVec A (a • x) + Matrix.mulVec A (b' • y) := by
              simp
      _ = a • Matrix.mulVec A x + b' • Matrix.mulVec A y := by simp
      _ = a • b + b' • b := by rw [hx_eq, hy_eq]
      _ = (a + b') • b := by ext i; simp [smul_eq_mul, add_mul]
      _ = b := by rw [hab, one_smul]
  · have hmemx :
        ((x, (0 : ℝ)) : (Fin n → ℝ) × ℝ) ∈
          {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)} := by
        exact le_of_lt hx_f0
    have hmemy :
        ((y, (0 : ℝ)) : (Fin n → ℝ) × ℝ) ∈
          {xt : (Fin n → ℝ) × ℝ | f0 xt.1 ≤ (xt.2 : WithTop ℝ)} := by
        exact le_of_lt hy_f0
    have hconv := hf0 hmemx hmemy ha hb hab
    exact lt_of_le_of_lt (by simpa [Prod.smul_mk, Prod.mk.add_mk] using hconv) (by simp)
  · have hsum :
        (∑ j : Fin n, c j * (a • x + b' • y) j)
          = a * (∑ j : Fin n, c j * x j) + b' * (∑ j : Fin n, c j * y j) := by
        simp [Pi.add_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum, left_distrib]
    rw [hsum]
    have hcomb :
        a * (∑ j : Fin n, c j * x j) + b' * (∑ j : Fin n, c j * y j) + d
          = a * ((∑ j : Fin n, c j * x j) + d) + b' * ((∑ j : Fin n, c j * y j) + d) := by
      rw [mul_add, mul_add]
      ring_nf
      rw [hab]
      ring
    rw [hcomb]
    have hxnonneg : 0 ≤ a * ((∑ j : Fin n, c j * x j) + d) := by
      exact mul_nonneg ha (le_of_lt hx_pos)
    have hyterm_nonneg : 0 ≤ b' * ((∑ j : Fin n, c j * y j) + d) := by
      exact mul_nonneg hb (le_of_lt hy_pos)
    have hyterm_pos : 0 < b' * ((∑ j : Fin n, c j * y j) + d) ∨ b' * ((∑ j : Fin n, c j * y j) + d) = 0 := by
      exact lt_or_eq_of_le hyterm_nonneg
    cases hyterm_pos with
    | inl hpos =>
        exact add_pos_of_nonneg_of_pos hxnonneg hpos
    | inr hzero =>
        rw [hzero, add_zero]
        have h' : a = 1 := by linarith
        rw [h', one_mul]
        exact hx_pos

/- [BLOCK Exercise 4.7-(a) | 36 | thm]
Let c ∈ ℝ^n and d ∈ ℝ.
Let f₀, f₁, ..., fₘ : ℝ^n → ℝ U {+infinity} be convex functions, and let
dom f₀ = {x ∈ ℝ^n | f₀(x) < +infinity}.
Show that the function
x -> f₀(x) / (cᵀ x + d)
is quasiconvex on the domain
{x in dom f₀ | cᵀ x + d > 0}.
-/