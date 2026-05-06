theorem feasible_to_standardForm_feasible
    (lp : LinearProgram)
    {x : Fin lp.n → ℝ}
    (hx : x ∈ lp.feasibleSet)
    (sf : StandardFormLinearProgram)
    (hsf : sf.base = lp) :
    let xPlus : Fin sf.base.n → ℝ := fun i => max (x (hsf ▸ i)) 0
    let xMinus : Fin sf.base.n → ℝ := fun i => max (-x (hsf ▸ i)) 0
    let s : Fin sf.base.m → ℝ := fun i => sf.base.h i - ∑ j : Fin sf.base.n, sf.base.G i j * x (hsf ▸ j)
    ((xPlus, xMinus, s) ∈ sf.feasibleSet) ∧
      (x = fun i => xPlus (hsf ▸ i) - xMinus (hsf ▸ i)) ∧
      (lp.objective x = sf.objective xPlus xMinus) := by
  subst hsf
  dsimp
  rcases hx with ⟨hG, hA⟩
  have hxsplit : ∀ j : Fin sf.base.n, max (x j) 0 - max (-x j) 0 = x j := by
    intro j
    by_cases hj : 0 ≤ x j
    · have hneg : max (-x j) 0 = 0 := by
        rw [max_eq_right]
        linarith
      rw [max_eq_left hj, hneg]
      ring
    · have hj' : x j ≤ 0 := le_of_not_ge hj
      have hpos : max (x j) 0 = 0 := by
        rw [max_eq_right]
        linarith
      have hneg : max (-x j) 0 = -x j := by
        rw [max_eq_left]
        linarith
      rw [hpos, hneg]
      ring
  refine ⟨?_, ?_, ?_⟩
  · simpa [StandardFormLinearProgram.feasibleSet] using
      (show
        (∀ i : Fin sf.base.n, 0 ≤ max (x i) 0) ∧
        (∀ i : Fin sf.base.n, 0 ≤ max (-x i) 0) ∧
        (∀ i : Fin sf.base.m, 0 ≤ sf.base.h i - ∑ j : Fin sf.base.n, sf.base.G i j * x j) ∧
        (∀ i : Fin sf.base.m,
          (∑ j : Fin sf.base.n, sf.base.G i j * max (x j) 0) -
              (∑ j : Fin sf.base.n, sf.base.G i j * max (-x j) 0) +
              (sf.base.h i - ∑ j : Fin sf.base.n, sf.base.G i j * x j) =
            sf.base.h i) ∧
        (∀ i : Fin sf.base.p,
          (∑ j : Fin sf.base.n, sf.base.A i j * max (x j) 0) -
              (∑ j : Fin sf.base.n, sf.base.A i j * max (-x j) 0) =
            sf.base.b i) := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro i
            exact le_max_right _ _
          · intro i
            exact le_max_right _ _
          · intro i
            exact sub_nonneg.mpr (hG i)
          · intro i
            calc
              (∑ j : Fin sf.base.n, sf.base.G i j * max (x j) 0) -
                  (∑ j : Fin sf.base.n, sf.base.G i j * max (-x j) 0) +
                  (sf.base.h i - ∑ j : Fin sf.base.n, sf.base.G i j * x j)
                  =
                  (∑ j : Fin sf.base.n,
                    (sf.base.G i j * max (x j) 0 - sf.base.G i j * max (-x j) 0)) +
                    (sf.base.h i - ∑ j : Fin sf.base.n, sf.base.G i j * x j) := by
                    rw [Finset.sum_sub_distrib]
              _ =
                  (∑ j : Fin sf.base.n,
                    sf.base.G i j * (max (x j) 0 - max (-x j) 0)) +
                    (sf.base.h i - ∑ j : Fin sf.base.n, sf.base.G i j * x j) := by
                    congr
                    funext j
                    ring
              _ =
                  (∑ j : Fin sf.base.n, sf.base.G i j * x j) +
                    (sf.base.h i - ∑ j : Fin sf.base.n, sf.base.G i j * x j) := by
                    congr
                    funext j
                    rw [hxsplit j]
              _ = sf.base.h i := by ring
          · intro i
            calc
              (∑ j : Fin sf.base.n, sf.base.A i j * max (x j) 0) -
                  (∑ j : Fin sf.base.n, sf.base.A i j * max (-x j) 0)
                  =
                  ∑ j : Fin sf.base.n,
                    (sf.base.A i j * max (x j) 0 - sf.base.A i j * max (-x j) 0) := by
                    rw [Finset.sum_sub_distrib]
              _ =
                  ∑ j : Fin sf.base.n,
                    sf.base.A i j * (max (x j) 0 - max (-x j) 0) := by
                    congr
                    funext j
                    ring
              _ = ∑ j : Fin sf.base.n, sf.base.A i j * x j := by
                    congr
                    funext j
                    rw [hxsplit j]
              _ = sf.base.b i := hA i)
  · funext i
    symm
    exact hxsplit i
  · dsimp [LinearProgram.objective, StandardFormLinearProgram.objective]
    calc
      (∑ j : Fin sf.base.n, sf.base.c j * x j) + sf.base.d
          = (∑ j : Fin sf.base.n, sf.base.c j * (max (x j) 0 - max (-x j) 0)) + sf.base.d := by
              congr
              funext j
              symm
              exact hxsplit j
      _ =
          (∑ j : Fin sf.base.n,
            (sf.base.c j * max (x j) 0 - sf.base.c j * max (-x j) 0)) + sf.base.d := by
            congr
            funext j
            ring
      _ =
          ((∑ j : Fin sf.base.n, sf.base.c j * max (x j) 0) -
            (∑ j : Fin sf.base.n, sf.base.c j * max (-x j) 0)) + sf.base.d := by
            rw [Finset.sum_sub_distrib]
      _ = sf.objective (fun i => max (x i) 0) (fun i => max (-x i) 0) := by
            rfl

/- [BLOCK Exercise 4.10 | 8 | thm]
Let n,m,p ∈ ℕ, c∈ ℝ^n, d∈ ℝ, G∈ ℝ^{m× n}, h∈ ℝ^m, A∈ ℝ^{p× n}, and b∈ ℝ^p. Consider the linear
program
array{ll}
minimize & cᵀ x+d ;
subject to & Gx ≤ h,;
& Ax=b,
array
with decision variable x∈ ℝ^n, and let
mathcal F={x∈ ℝ^n| Gx≤ h,\ Ax=b}.
Define the associated standard-form problem with variables x^+,x^-∈ ℝ^n and s∈ ℝ^m by
array{ll}
minimize & cᵀ x^+ - cᵀ x^- + d ;
subject to & Gx^+ - Gx^- + s = h,;
& Ax^+-Ax^-=b,;
& x^+≥ 0,quad x^-≥ 0,quad s≥ 0,
array
where all inequalities are componentwise, and let
mathcal F_{sf}={(x^+,x^-,s)∈ ℝ^n× ℝ^n× ℝ^m | x^+≥ 0,\ x^-≥ 0,\ s≥ 0,\ Gx^+-Gx^-+s=h,\ Ax^+-Ax^-=b}.
For x∈ ℝ^n, define x^+,x^-∈ ℝ^n componentwise by
(x^+)_i=xᵢ,0, (x^-)_i=-xᵢ,0quad (i=1,dots,n).
Prove that for every (x^+,x^-,s)∈ mathcal F_{sf}, the point x=x^+-x^- belongs to mathcal F, and its
objective value equals that of (x^+,x^-,s):
cᵀ x + d = cᵀ x^+ - cᵀ x^- + d.
-/