import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-58»
/-
For h: R^m → ℝ U {+ infinity, - infinity}, its convex conjugate h*: R^m → ℝ U {+ infinity, -
infinity}
is defined by h*(y) = sup_{v ∈ ℝ^m} (yᵀ v - h(v)).
-/
open scoped RealInnerProductSpace

def convexConjugate {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → EReal) :
    EuclideanSpace ℝ (Fin m) → EReal :=
  fun y => sSup (Set.range fun v => ((⟪y, v⟫ : ℝ) : EReal) - h v)

/-
Let f₀, f₁, ..., fₘ: D → ℝ be convex functions on a convex set D subseteq ℝ^n. Consider the
optimization problem: minimize f₀(x) subject to fᵢ(x) < = 0 for i = 1, ..., m, and x in D.
-/
structure ConvexInequalityConstrainedProblem (n m : ℕ) where
  domain : Set (EuclideanSpace ℝ (Fin n))
  domain_convex : Convex ℝ domain
  objective : EuclideanSpace ℝ (Fin n) → ℝ
  constraints : Fin m → EuclideanSpace ℝ (Fin n) → ℝ
  objective_convex : ConvexOn ℝ domain objective
  constraints_convex : ∀ i : Fin m, ConvexOn ℝ domain (constraints i)

def ConvexInequalityConstrainedProblem.isFeasible
    {n m : ℕ} (P : ConvexInequalityConstrainedProblem n m)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ P.domain ∧ ∀ i : Fin m, P.constraints i x ≤ 0

/-- Rewrite the perturbation value as an `iInf` over domain points. -/
lemma perturbationValue_eq_iInf
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤) :
    pStar =
      fun u =>
        iInf fun x : {x // x ∈ P.domain} =>
          if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
            ((P.objective x.1 : ℝ) : EReal)
          else
            ⊤ := by
  -- Repackage the `sInf` over a range as the corresponding indexed `iInf`.
  ext u
  simp [hp, sInf_range]

/-- Relaxing the inequality bounds can only decrease the perturbation value. -/
lemma perturbationValue_antitone
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    {u v : EuclideanSpace ℝ (Fin m)}
    (huv : ∀ i : Fin m, u i ≤ v i) :
    pStar v ≤ pStar u := by
  let F : EuclideanSpace ℝ (Fin m) → {x // x ∈ P.domain} → EReal :=
    fun w x =>
      if ∀ i : Fin m, P.constraints i x.1 ≤ w i then
        ((P.objective x.1 : ℝ) : EReal)
      else
        ⊤
  have hmono : ∀ x, F v x ≤ F u x := by
    -- A point feasible for the tighter bound `u` is also feasible for the relaxed bound `v`.
    intro x
    by_cases hu : ∀ i : Fin m, P.constraints i x.1 ≤ u i
    · have hv : ∀ i : Fin m, P.constraints i x.1 ≤ v i := fun i => le_trans (hu i) (huv i)
      simp [F, hu, hv]
    · by_cases hv : ∀ i : Fin m, P.constraints i x.1 ≤ v i
      · simp [F, hu, hv]
      · simp [F, hu, hv]
  calc
    pStar v = iInf (F v) := by
      simp [perturbationValue_eq_iInf (P := P) (pStar := pStar) hp, F]
    _ ≤ iInf (F u) := iInf_mono hmono
    _ = pStar u := by
      simp [perturbationValue_eq_iInf (P := P) (pStar := pStar) hp, F]

/-- Any feasible domain point gives an upper bound on the perturbation value. -/
lemma perturbationValue_le_objective_of_feasible
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    {u : EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ P.domain)
    (hfeas : ∀ i : Fin m, P.constraints i x ≤ u i) :
    pStar u ≤ ((P.objective x : ℝ) : EReal) := by
  let F : {x // x ∈ P.domain} → EReal :=
    fun xsub =>
      if ∀ i : Fin m, P.constraints i xsub.1 ≤ u i then
        ((P.objective xsub.1 : ℝ) : EReal)
      else
        ⊤
  calc
    pStar u = iInf F := by
      simp [perturbationValue_eq_iInf (P := P) (pStar := pStar) hp, F]
    _ ≤ F ⟨x, hx⟩ := iInf_le _ _
    _ = ((P.objective x : ℝ) : EReal) := by
      -- The chosen point contributes its objective value because it is feasible for `u`.
      simp [F, hfeas]

/-- A convex combination of two feasible perturbation witnesses gives the expected upper bound on
the perturbation value at the convex-combined perturbation. -/
lemma perturbationValue_combo_le_of_feasible_pair
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hab : a + b = 1)
    {u1 u2 : EuclideanSpace ℝ (Fin m)}
    {x1 x2 : EuclideanSpace ℝ (Fin n)}
    (hx1 : x1 ∈ P.domain)
    (hfeas1 : ∀ i : Fin m, P.constraints i x1 ≤ u1 i)
    (hx2 : x2 ∈ P.domain)
    (hfeas2 : ∀ i : Fin m, P.constraints i x2 ≤ u2 i) :
    pStar (a • u1 + b • u2) ≤
      (((a * P.objective x1 + b * P.objective x2 : ℝ)) : EReal) := by
  let x := a • x1 + b • x2
  have hx : x ∈ P.domain := P.domain_convex hx1 hx2 ha hb hab
  have hconstraints :
      ∀ i : Fin m, P.constraints i x ≤ (a • u1 + b • u2) i := by
    -- Convexity keeps each constraint feasible under the same convex combination.
    intro i
    have hconstraint_combo :
        P.constraints i x ≤ a * P.constraints i x1 + b * P.constraints i x2 := by
      simpa [x] using (P.constraints_convex i).2 hx1 hx2 ha hb hab
    have hconstraint_bound :
        a * P.constraints i x1 + b * P.constraints i x2 ≤ a * u1 i + b * u2 i := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hfeas1 i) ha)
        (mul_le_mul_of_nonneg_left (hfeas2 i) hb)
    calc
      P.constraints i x ≤ a * P.constraints i x1 + b * P.constraints i x2 := hconstraint_combo
      _ ≤ a * u1 i + b * u2 i := hconstraint_bound
      _ = (a • u1 + b • u2) i := by simp
  have hobjective :
      P.objective x ≤ a * P.objective x1 + b * P.objective x2 := by
    -- The objective satisfies the same convex upper bound on the convex domain.
    simpa [x] using P.objective_convex.2 hx1 hx2 ha hb hab
  calc
    pStar (a • u1 + b • u2) ≤ ((P.objective x : ℝ) : EReal) :=
      perturbationValue_le_objective_of_feasible (P := P) (pStar := pStar) hp hx hconstraints
    _ ≤ (((a * P.objective x1 + b * P.objective x2 : ℝ)) : EReal) := by
      exact_mod_cast hobjective

/-- Interior points of the finite-above effective domain admit a metric ball on which the
perturbation value stays finite-above. -/
lemma perturbationValue_lt_top_on_ball_of_mem_interior
    {n m : ℕ}
    (pStar : EuclideanSpace ℝ (Fin m) → EReal)
    {u : EuclideanSpace ℝ (Fin m)}
    (hu : u ∈ interior {v | pStar v < ⊤}) :
    ∃ r > 0, Metric.ball u r ⊆ {v | pStar v < ⊤} := by
  -- Convert interior membership into a neighborhood basis ball around `u`.
  rw [mem_interior_iff_mem_nhds] at hu
  rcases Metric.mem_nhds_iff.mp hu with ⟨r, hr, hball⟩
  exact ⟨r, hr, hball⟩

/-- If the perturbation value at `v` lies below a real bound, some feasible point attains an
objective value below that bound. -/
lemma exists_feasible_of_perturbationValue_lt_real
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    {v : EuclideanSpace ℝ (Fin m)}
    {r : ℝ}
    (hv : pStar v < (r : EReal)) :
    ∃ x : EuclideanSpace ℝ (Fin n),
      x ∈ P.domain ∧ (∀ i : Fin m, P.constraints i x ≤ v i) ∧ P.objective x < r := by
  let F : {x // x ∈ P.domain} → EReal :=
    fun x =>
      if ∀ i : Fin m, P.constraints i x.1 ≤ v i then
        ((P.objective x.1 : ℝ) : EReal)
      else
        ⊤
  have hlt : iInf F < (r : EReal) := by
    -- Rewrite the perturbation value as an indexed infimum and extract a strict witness.
    simpa [perturbationValue_eq_iInf (P := P) (pStar := pStar) hp, F] using hv
  obtain ⟨x, hxlt⟩ := iInf_lt_iff.mp hlt
  by_cases hfeas : ∀ i : Fin m, P.constraints i x.1 ≤ v i
  · -- In the feasible branch the witness carries the desired strict objective estimate.
    refine ⟨x.1, x.2, hfeas, ?_⟩
    simpa [F, hfeas] using hxlt
  · -- The infeasible branch evaluates to `⊤`, contradicting the strict upper bound.
    simp [F, hfeas] at hxlt

/-- Any finite-above perturbation value has at least one feasible witness in the primal domain. -/
lemma exists_feasible_of_perturbationValue_lt_top
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    {v : EuclideanSpace ℝ (Fin m)}
    (hv : pStar v < ⊤) :
    ∃ x : EuclideanSpace ℝ (Fin n), x ∈ P.domain ∧ ∀ i : Fin m, P.constraints i x ≤ v i := by
  let F : {x // x ∈ P.domain} → EReal :=
    fun x =>
      if ∀ i : Fin m, P.constraints i x.1 ≤ v i then
        ((P.objective x.1 : ℝ) : EReal)
      else
        ⊤
  have hlt : iInf F < ⊤ := by
    -- The indexed-infimum form lets us read off a witness whose contribution is finite.
    simpa [perturbationValue_eq_iInf (P := P) (pStar := pStar) hp, F] using hv
  obtain ⟨x, hxlt⟩ := iInf_lt_iff.mp hlt
  by_cases hfeas : ∀ i : Fin m, P.constraints i x.1 ≤ v i
  · -- Any finite witness in the infimum must come from a feasible primal point.
    exact ⟨x.1, x.2, hfeas⟩
  · -- The infeasible branch contributes `⊤`, so it cannot be strictly below `⊤`.
    simp [F, hfeas] at hxlt

/-- Rewrite the dual function as an indexed infimum of Lagrangian values. -/
lemma dualFunction_eq_iInf_lagrangian
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (g : EuclideanSpace ℝ (Fin m) → EReal)
    (hg : g =
      fun lam =>
        if ∀ i : Fin m, 0 ≤ lam i then
          sInf <|
            Set.range fun x : {x // x ∈ P.domain} =>
              (((P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1) : ℝ) : EReal)
        else
          ⊥)
    {lam : EuclideanSpace ℝ (Fin m)}
    (hlam : ∀ i : Fin m, 0 ≤ lam i) :
    g lam =
      iInf fun x : {x // x ∈ P.domain} =>
        (((P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1) : ℝ) : EReal) := by
  -- Repackage the defining `sInf` of the dual function as an indexed `iInf`.
  simp [hg, hlam, sInf_range]

/-- Weak duality: every dual-feasible multiplier yields an affine minorant of the perturbation
value. -/
lemma dualAffineMinorant_le_perturbationValue
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar g : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    (hg : g =
      fun lam =>
        if ∀ i : Fin m, 0 ≤ lam i then
          sInf <|
            Set.range fun x : {x // x ∈ P.domain} =>
              (((P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1) : ℝ) : EReal)
        else
          ⊥)
    {lam v : EuclideanSpace ℝ (Fin m)}
    (hlam : ∀ i : Fin m, 0 ≤ lam i) :
    g lam - ((⟪v, lam⟫ : ℝ) : EReal) ≤ pStar v := by
  let G : {x // x ∈ P.domain} → EReal :=
    fun x =>
      (((P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1) : ℝ) : EReal)
  let F : {x // x ∈ P.domain} → EReal :=
    fun x =>
      if ∀ i : Fin m, P.constraints i x.1 ≤ v i then
        ((P.objective x.1 : ℝ) : EReal)
      else
        ⊤
  have hpoint :
      ∀ x : {x // x ∈ P.domain},
        g lam - ((⟪v, lam⟫ : ℝ) : EReal) ≤ F x := by
    -- Compare the dual value against each feasible perturbation witness separately.
    intro x
    by_cases hxv : ∀ i : Fin m, P.constraints i x.1 ≤ v i
    · have hsum :
          ∑ i : Fin m, lam i * P.constraints i x.1 ≤
            ∑ i : Fin m, lam i * v i := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left (hxv i) (hlam i)
      have hgx :
          g lam ≤
            (((P.objective x.1 + ∑ i : Fin m, lam i * v i) : ℝ) : EReal) := by
        -- Evaluate the dual infimum at the chosen domain point and relax its constraint values to `v`.
        calc
          g lam = iInf G := by
            simp [dualFunction_eq_iInf_lagrangian (P := P) (g := g) hg hlam, G]
          _ ≤ G x := iInf_le _ x
          _ ≤ (((P.objective x.1 + ∑ i : Fin m, lam i * v i) : ℝ) : EReal) := by
            -- This is the real-valued comparison transported into `EReal`.
            change
              (((P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1) : ℝ) : EReal) ≤
                (((P.objective x.1 + ∑ i : Fin m, lam i * v i) : ℝ) : EReal)
            have hreal :
                P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1 ≤
                  P.objective x.1 + ∑ i : Fin m, lam i * v i :=
              add_le_add_right hsum (P.objective x.1)
            exact_mod_cast hreal
      have hsub :
          g lam - ((⟪v, lam⟫ : ℝ) : EReal) ≤ ((P.objective x.1 : ℝ) : EReal) := by
        -- Subtract the finite pairing term from the weak-duality bound.
        refine EReal.sub_le_of_le_add ?_
        simpa [EuclideanSpace.inner_eq_star_dotProduct, G, dotProduct] using hgx
      simpa [F, hxv] using hsub
    · -- If `x` is not feasible for `v`, the perturbation witness contributes `⊤`.
      simp [F, hxv]
  -- Taking the infimum over all perturbation witnesses yields the desired minorant.
  calc
    g lam - ((⟪v, lam⟫ : ℝ) : EReal) ≤ iInf F := le_iInf hpoint
    _ = pStar v := by
      simp [perturbationValue_eq_iInf (P := P) (pStar := pStar) hp, F]

/-- The dual function is the infimum of all perturbation shifts by a fixed dual-feasible
multiplier. -/
lemma dualFunction_eq_iInf_perturbationShift
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar g : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    (hg : g =
      fun lam =>
        if ∀ i : Fin m, 0 ≤ lam i then
          sInf <|
            Set.range fun x : {x // x ∈ P.domain} =>
              (((P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1) : ℝ) : EReal)
        else
          ⊥)
    {lam : EuclideanSpace ℝ (Fin m)}
    (hlam : ∀ i : Fin m, 0 ≤ lam i) :
    g lam =
      iInf fun v : EuclideanSpace ℝ (Fin m) =>
        pStar v + ((⟪v, lam⟫ : ℝ) : EReal) := by
  apply le_antisymm
  · -- Weak duality shows that `g lam` is a lower bound for every shifted perturbation value.
    refine le_iInf fun v => ?_
    exact
      (EReal.sub_le_iff_le_add
        (.inl (by simp))
        (.inl (by simp))).1
        (dualAffineMinorant_le_perturbationValue (P := P) (pStar := pStar) (g := g) hp hg hlam)
  · -- Evaluate the perturbation infimum at the constraint vector of each domain point.
    have hpoint :
        ∀ x : {x // x ∈ P.domain},
          iInf (fun v : EuclideanSpace ℝ (Fin m) => pStar v + ((⟪v, lam⟫ : ℝ) : EReal)) ≤
            (((P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1) : ℝ) : EReal) := by
      intro x
      let v : EuclideanSpace ℝ (Fin m) :=
        (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m)).symm
          (fun i => P.constraints i x.1)
      have hv :
          pStar v ≤ ((P.objective x.1 : ℝ) : EReal) := by
        -- The constraint vector of `x` makes `x` tautologically feasible for that perturbation.
        refine perturbationValue_le_objective_of_feasible (P := P) (pStar := pStar) hp x.2 ?_
        intro i
        change P.constraints i x.1 ≤ ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m)) v) i
        simp [v]
      have hi :
          iInf (fun v : EuclideanSpace ℝ (Fin m) => pStar v + ((⟪v, lam⟫ : ℝ) : EReal)) ≤
            pStar v + ((⟪v, lam⟫ : ℝ) : EReal) :=
        iInf_le _ v
      calc
        iInf (fun v : EuclideanSpace ℝ (Fin m) => pStar v + ((⟪v, lam⟫ : ℝ) : EReal))
            ≤ pStar v + ((⟪v, lam⟫ : ℝ) : EReal) := hi
        _ ≤ (((P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1) : ℝ) : EReal) := by
          -- Replace `pStar v` by the objective upper bound at `x`.
          simpa [v, EuclideanSpace.equiv, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
            add_comm, add_left_comm, add_assoc]
            using add_le_add_right hv (((⟪v, lam⟫ : ℝ) : EReal))
    calc
      iInf (fun v : EuclideanSpace ℝ (Fin m) => pStar v + ((⟪v, lam⟫ : ℝ) : EReal))
          ≤ iInf (fun x : {x // x ∈ P.domain} =>
            (((P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1) : ℝ) : EReal)) :=
        le_iInf hpoint
      _ = g lam := by
        simp [dualFunction_eq_iInf_lagrangian (P := P) (g := g) hg hlam]

/-- Interior points of the finite-above effective domain admit a smaller ball on which the
perturbation value stays both finite-above and away from `⊥`. -/
lemma perturbationValue_ne_bot_on_interior_ball
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    {u : EuclideanSpace ℝ (Fin m)}
    (hu : u ∈ interior {v | pStar v < ⊤})
    (hu_bot : pStar u ≠ ⊥) :
    ∃ r > 0, ∀ v ∈ Metric.ball u r, pStar v ≠ ⊥ ∧ pStar v < ⊤ := by
  obtain ⟨r, hr, hball⟩ :=
    perturbationValue_lt_top_on_ball_of_mem_interior (n := n) (pStar := pStar) hu
  refine ⟨r, hr, ?_⟩
  intro v hv
  have hv_top : pStar v < ⊤ := hball hv
  refine ⟨?_, hv_top⟩
  by_contra hv_bot
  let w : EuclideanSpace ℝ (Fin m) := 2 • u - v
  have hwball : w ∈ Metric.ball u r := by
    -- Reflecting a point across the center preserves the distance to `u`.
    rw [Metric.mem_ball, dist_eq_norm]
    have hwsub : w - u = -(v - u) := by
      simp [w, sub_eq_add_neg, two_smul, add_comm, add_left_comm, add_assoc]
    rw [hwsub, norm_neg]
    exact hv
  have hw_top : pStar w < ⊤ := hball hwball
  obtain ⟨xw, hxw_dom, hxw_feas⟩ :=
    exists_feasible_of_perturbationValue_lt_top (P := P) (pStar := pStar) hp hw_top
  have hu_forall_real_lt : ∀ R : ℝ, pStar u < (R : EReal) := by
    intro R
    have hv_lt :
        pStar v < (((2 : ℝ) * R - P.objective xw : ℝ) : EReal) := by
      simpa [hv_bot] using
        (show (⊥ : EReal) < (((2 : ℝ) * R - P.objective xw : ℝ) : EReal) from
          EReal.bot_lt_coe _)
    obtain ⟨xv, hxv_dom, hxv_feas, hxv_obj⟩ :=
      exists_feasible_of_perturbationValue_lt_real (P := P) (pStar := pStar) hp hv_lt
    have hcombo :=
      perturbationValue_combo_le_of_feasible_pair
        (P := P) (pStar := pStar) hp
        (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
        (by positivity) (by positivity) (by norm_num)
        (u1 := v) (u2 := w) (x1 := xv) (x2 := xw)
        hxv_dom hxv_feas hxw_dom hxw_feas
    have hu_eq : (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w = u := by
      ext i
      simp [w, sub_eq_add_neg, two_smul]
      ring
    have hobj_lt :
        ((1 / 2 : ℝ) * P.objective xv + (1 / 2 : ℝ) * P.objective xw : ℝ) < R := by
      linarith
    calc
      pStar u = pStar ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) := by rw [hu_eq]
      _ ≤ ((((1 / 2 : ℝ) * P.objective xv + (1 / 2 : ℝ) * P.objective xw : ℝ)) : EReal) := hcombo
      _ < (R : EReal) := by exact_mod_cast hobj_lt
  exact hu_bot ((EReal.eq_bot_iff_forall_lt (pStar u)).2 hu_forall_real_lt)

/-- If one interior perturbation value is not `⊥`, then no perturbation value can be `⊥`. -/
lemma perturbationValue_ne_bot_everywhere_of_mem_interior
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    {u : EuclideanSpace ℝ (Fin m)}
    (hu : u ∈ interior {v | pStar v < ⊤})
    (hu_bot : pStar u ≠ ⊥) :
    ∀ v : EuclideanSpace ℝ (Fin m), pStar v ≠ ⊥ := by
  obtain ⟨r, hr, hlocal⟩ :=
    perturbationValue_ne_bot_on_interior_ball (P := P) (pStar := pStar) hp hu hu_bot
  have hu_top : pStar u < ⊤ := by
    have hu_mem : u ∈ {v | pStar v < ⊤} := interior_subset hu
    exact hu_mem
  obtain ⟨xu, hxu_dom, hxu_feas⟩ :=
    exists_feasible_of_perturbationValue_lt_top (P := P) (pStar := pStar) hp hu_top
  intro v
  by_cases hvu : v = u
  · simpa [hvu] using hu_bot
  · by_contra hv_bot
    let t : ℝ := min (r / (dist v u + 1)) (1 / 2)
    have ht_pos : 0 < t := by
      apply lt_min
      · have hden : 0 < dist v u + 1 := by positivity
        exact div_pos hr hden
      · norm_num
    have ht_lt_one : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    let z : EuclideanSpace ℝ (Fin m) := (1 - t) • u + t • v
    have hzball : z ∈ Metric.ball u r := by
      -- The chosen convex-combination parameter keeps `z` inside the interior ball around `u`.
      rw [Metric.mem_ball, dist_eq_norm]
      have hzsub : z - u = t • (v - u) := by
        ext i
        simp [z, sub_eq_add_neg]
        ring
      rw [hzsub, norm_smul, Real.norm_of_nonneg ht_pos.le]
      have hmul_lt : t * dist v u < r := by
        have hlt1 : dist v u < dist v u + 1 := by linarith
        have hdiv :
            (r / (dist v u + 1)) * dist v u < r := by
          have hden : 0 < dist v u + 1 := by positivity
          have := (mul_lt_mul_of_pos_left hlt1 (div_pos hr hden))
          have hcancel : (r / (dist v u + 1)) * (dist v u + 1) = r := by
            field_simp [hden.ne']
          simpa [left_distrib, hcancel, mul_comm, mul_left_comm, mul_assoc] using this
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (min_le_left _ _) dist_nonneg) hdiv
      simpa [dist_eq_norm] using hmul_lt
    have hz_ne_bot : pStar z ≠ ⊥ := (hlocal z hzball).1
    have hz_forall_real_lt : ∀ R : ℝ, pStar z < (R : EReal) := by
      intro R
      have hv_lt :
          pStar v <
            (((R - (1 - t) * P.objective xu) / t : ℝ) : EReal) := by
        simp [hv_bot]
      obtain ⟨xv, hxv_dom, hxv_feas, hxv_obj⟩ :=
        exists_feasible_of_perturbationValue_lt_real (P := P) (pStar := pStar) hp hv_lt
      have hcombo :=
        perturbationValue_combo_le_of_feasible_pair
          (P := P) (pStar := pStar) hp
          (a := 1 - t) (b := t)
          (by linarith) ht_pos.le (by ring)
          (u1 := u) (u2 := v) (x1 := xu) (x2 := xv)
          hxu_dom hxu_feas hxv_dom hxv_feas
      have hz_eq : (1 - t) • u + t • v = z := rfl
      have hobj_lt :
          (((1 - t) * P.objective xu + t * P.objective xv : ℝ)) < R := by
        have hxv_bound :
            t * P.objective xv < t * ((R - (1 - t) * P.objective xu) / t) := by
          exact mul_lt_mul_of_pos_left hxv_obj ht_pos
        have ht_ne : t ≠ 0 := ne_of_gt ht_pos
        have hxv_bound' : t * P.objective xv < R - (1 - t) * P.objective xu := by
          rwa [mul_div_cancel₀ _ ht_ne] at hxv_bound
        linarith
      calc
        pStar z = pStar ((1 - t) • u + t • v) := by rw [hz_eq]
        _ ≤ ((((1 - t) * P.objective xu + t * P.objective xv : ℝ)) : EReal) := hcombo
        _ < (R : EReal) := by exact_mod_cast hobj_lt
    exact hz_ne_bot ((EReal.eq_bot_iff_forall_lt (pStar z)).2 hz_forall_real_lt)

/-- Away from `⊥`, the perturbation value induces a convex real-valued function on its finite-above
effective domain. -/
lemma perturbationValue_toReal_convexOn_domain
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    (hno_bot : ∀ v : EuclideanSpace ℝ (Fin m), pStar v ≠ ⊥) :
    let D : Set (EuclideanSpace ℝ (Fin m)) := {v | pStar v < ⊤}
    let φ : EuclideanSpace ℝ (Fin m) → ℝ := fun v => (pStar v).toReal
    ConvexOn ℝ D φ := by
  classical
  let D : Set (EuclideanSpace ℝ (Fin m)) := {v | pStar v < ⊤}
  let φ : EuclideanSpace ℝ (Fin m) → ℝ := fun v => (pStar v).toReal
  refine convexOn_iff_convex_epigraph.2 ?_
  intro p hp_epi q hq_epi a b ha hb hab
  rcases hp_epi with ⟨hpD, hpφ⟩
  rcases hq_epi with ⟨hqD, hqφ⟩
  let z : EuclideanSpace ℝ (Fin m) := a • p.1 + b • q.1
  have happrox :
      ∀ ε > 0, pStar z ≤ (((a * p.2 + b * q.2 + ε : ℝ)) : EReal) := by
    intro ε hε
    have hp_lt : pStar p.1 < ((p.2 + ε : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hpD.ne (hno_bot p.1)]
      exact_mod_cast lt_of_le_of_lt hpφ (lt_add_of_pos_right _ hε)
    have hq_lt : pStar q.1 < ((q.2 + ε : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hqD.ne (hno_bot q.1)]
      exact_mod_cast lt_of_le_of_lt hqφ (lt_add_of_pos_right _ hε)
    obtain ⟨xp, hxp_dom, hxp_feas, hxp_obj⟩ :=
      exists_feasible_of_perturbationValue_lt_real (P := P) (pStar := pStar) hp hp_lt
    obtain ⟨xq, hxq_dom, hxq_feas, hxq_obj⟩ :=
      exists_feasible_of_perturbationValue_lt_real (P := P) (pStar := pStar) hp hq_lt
    calc
      pStar z ≤ ((((a * P.objective xp + b * P.objective xq : ℝ))) : EReal) :=
        perturbationValue_combo_le_of_feasible_pair
          (P := P) (pStar := pStar) hp (a := a) (b := b) ha hb hab
          hxp_dom hxp_feas hxq_dom hxq_feas
      _ ≤ (((a * p.2 + b * q.2 + ε : ℝ)) : EReal) := by
        have hreal :
            a * P.objective xp + b * P.objective xq ≤ a * p.2 + b * q.2 + ε := by
          have hxp_le : a * P.objective xp ≤ a * (p.2 + ε) := by
            exact mul_le_mul_of_nonneg_left hxp_obj.le ha
          have hxq_le : b * P.objective xq ≤ b * (q.2 + ε) := by
            exact mul_le_mul_of_nonneg_left hxq_obj.le hb
          nlinarith [hxp_le, hxq_le, hab]
        exact_mod_cast hreal
  have hz_finite : pStar z < ⊤ := by
    exact lt_of_le_of_lt (happrox 1 zero_lt_one) (EReal.coe_lt_top _)
  refine ⟨hz_finite, ?_⟩
  have hreal_eps :
      ∀ ε > 0, (pStar z).toReal ≤ a * p.2 + b * q.2 + ε := by
    intro ε hε
    have hrhs_ne_top : ((((a * p.2 + b * q.2 + ε : ℝ)) : EReal)) ≠ ⊤ := by
      simpa using (EReal.coe_ne_top (a * p.2 + b * q.2 + ε))
    exact EReal.toReal_le_toReal (happrox ε hε) (hno_bot z) hrhs_ne_top
  exact le_of_forall_pos_le_add hreal_eps

/-- Separating a point from the strict epigraph over a ball yields a local affine support there. -/
lemma local_affine_support_on_ball
    {m : ℕ} {φ : EuclideanSpace ℝ (Fin m) → ℝ} {u : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hr : 0 < r)
    (hφconv : ConvexOn ℝ (Metric.ball u r) φ)
    (hφcont : ContinuousOn φ (Metric.ball u r)) :
    ∃ v : StrongDual ℝ (EuclideanSpace ℝ (Fin m)), ∃ c : ℝ,
      v u + c = φ u ∧ ∀ z ∈ Metric.ball u r, v z + c ≤ φ z := by
  let T : Set (EuclideanSpace ℝ (Fin m) × ℝ) := {p | p.1 ∈ Metric.ball u r ∧ φ p.1 < p.2}
  have hTconv : Convex ℝ T := by
    -- The strict epigraph of a convex function is convex.
    simpa [T] using hφconv.convex_strict_epigraph
  have hcont_prod :
      ContinuousOn (fun p : EuclideanSpace ℝ (Fin m) × ℝ => φ p.1 - p.2)
        (Prod.fst ⁻¹' Metric.ball u r) := by
    -- Compose the continuity of `φ` on the ball with the first projection, then subtract the
    -- height.
    have hφfst :
        ContinuousOn (fun p : EuclideanSpace ℝ (Fin m) × ℝ => φ p.1)
          (Prod.fst ⁻¹' Metric.ball u r) :=
      hφcont.comp continuous_fst.continuousOn (by intro p hp; exact hp)
    exact hφfst.sub continuous_snd.continuousOn
  have hTopen : IsOpen T := by
    -- Openness comes from continuity of `(z,t) ↦ φ z - t` on the open base `ball u r`.
    have hopen_base : IsOpen (Prod.fst ⁻¹' Metric.ball u r) :=
      (Metric.isOpen_ball : IsOpen (Metric.ball u r)).preimage
        (continuous_fst : Continuous (Prod.fst :
          (EuclideanSpace ℝ (Fin m) × ℝ) → EuclideanSpace ℝ (Fin m)))
    have hopen_pre : IsOpen ((Prod.fst ⁻¹' Metric.ball u r) ∩
        (fun p : EuclideanSpace ℝ (Fin m) × ℝ => φ p.1 - p.2) ⁻¹' Set.Iio 0) :=
      hcont_prod.isOpen_inter_preimage hopen_base isOpen_Iio
    have hT :
        T = ((Prod.fst ⁻¹' Metric.ball u r) ∩
          (fun p : EuclideanSpace ℝ (Fin m) × ℝ => φ p.1 - p.2) ⁻¹' Set.Iio 0) := by
      ext p
      simp [T, Metric.ball, sub_lt_iff_lt_add, add_comm]
    rw [hT]
    exact hopen_pre
  have hu_not_mem : (u, φ u) ∉ T := by
    -- The boundary point itself is not in the strict epigraph.
    simp [T]
  obtain ⟨L, hsep⟩ :=
    geometric_hahn_banach_point_open (x := (u, φ u)) hTconv hTopen hu_not_mem
  let w : StrongDual ℝ (EuclideanSpace ℝ (Fin m)) := L.comp (.inl ℝ _ _)
  let α : ℝ := L (0, 1)
  have hzero (t : ℝ) : L (0, t) = t * α := by
    -- Evaluate the separator on the vertical line through the origin.
    have hsmul : ((0 : EuclideanSpace ℝ (Fin m)), t) =
        t • ((0 : EuclideanSpace ℝ (Fin m)), (1 : ℝ)) := by
      ext <;> simp
    rw [hsmul, map_smul]
    simp [α, smul_eq_mul]
  have happly (z : EuclideanSpace ℝ (Fin m)) (t : ℝ) : L (z, t) = w z + α * t := by
    -- Split every point into its horizontal and vertical components.
    have hpair : (z, t) = (z, 0) + ((0 : EuclideanSpace ℝ (Fin m)), t) := by ext <;> simp
    rw [hpair, map_add, hzero]
    simp [w, α, mul_comm]
  have hαpos : 0 < α := by
    -- Route correction: using the vertical test point avoids the normalization dead-end.
    have hsep_u : L (u, φ u) < L (u, φ u + 1) :=
      hsep _ ⟨Metric.mem_ball_self hr, by linarith⟩
    rw [happly, happly] at hsep_u
    linarith
  let v : StrongDual ℝ (EuclideanSpace ℝ (Fin m)) := (-α⁻¹ : ℝ) • w
  let c : ℝ := φ u + α⁻¹ * w u
  refine ⟨v, c, ?_, ?_⟩
  · -- The affine function is exact at the supporting point.
    simp [v, c]
  · intro z hz
    -- Separating `(u, φ u)` from `(z, φ z + ε)` gives the local inequality after dividing by `α`.
    refine le_of_forall_pos_lt_add ?_
    intro ε hε
    have hzsep : L (u, φ u) < L (z, φ z + ε) := hsep _ ⟨hz, by linarith⟩
    rw [happly, happly] at hzsep
    have hleft : α * (φ u + α⁻¹ * w u) = w u + α * φ u := by
      field_simp [hαpos.ne']
      ring_nf
    have hright : α * (φ z + ε + α⁻¹ * w z) = w z + α * (φ z + ε) := by
      field_simp [hαpos.ne']
      ring_nf
    have hdiv : φ u + α⁻¹ * w u < φ z + ε + α⁻¹ * w z := by
      apply lt_of_mul_lt_mul_left
      · rw [hleft, hright]
        exact hzsep
      · exact hαpos.le
    have hvz : v z + c = φ u + α⁻¹ * w u - α⁻¹ * w z := by
      simp [v, c, sub_eq_add_neg, smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_comm]
    rw [hvz]
    linarith

theorem perturbationValue_eq_convexConjugate_negDual_on_interiorDom
    {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m)
    (pStar g : EuclideanSpace ℝ (Fin m) → EReal)
    (hp : pStar =
      fun u =>
        sInf <|
          Set.range fun x : {x // x ∈ P.domain} =>
            if ∀ i : Fin m, P.constraints i x.1 ≤ u i then
              ((P.objective x.1 : ℝ) : EReal)
            else
              ⊤)
    (hg : g =
      fun lam =>
        if ∀ i : Fin m, 0 ≤ lam i then
          sInf <|
            Set.range fun x : {x // x ∈ P.domain} =>
              (((P.objective x.1 + ∑ i : Fin m, lam i * P.constraints i x.1) : ℝ) : EReal)
        else
          ⊥)
    {u : EuclideanSpace ℝ (Fin m)}
    (hu : u ∈ interior {v | pStar v < ⊤}) :
    pStar u = convexConjugate (fun y => -g y) (-u) := by
  refine le_antisymm ?_ ?_
  · by_cases hu_bot : pStar u = ⊥
    · -- The reverse inequality is trivial on the bottom branch.
      simp [hu_bot]
    · -- Route correction: the easy weak-duality direction is closed first, so the remaining blocker
      -- is now handled by a global affine minorant touching `pStar` at `u`, rather than the older
      -- segment-by-segment globalization route.
      have hu_top : pStar u < ⊤ := by
        -- Interior membership immediately implies that the center point stays in the effective
        -- domain.
        have hu_mem : u ∈ {v | pStar v < ⊤} := interior_subset hu
        exact hu_mem
      have hno_bot :
          ∀ v : EuclideanSpace ℝ (Fin m), pStar v ≠ ⊥ :=
        perturbationValue_ne_bot_everywhere_of_mem_interior
          (P := P) (pStar := pStar) hp hu hu_bot
      let D : Set (EuclideanSpace ℝ (Fin m)) := {v | pStar v < ⊤}
      let φ : EuclideanSpace ℝ (Fin m) → ℝ := fun v => (pStar v).toReal
      have hφconv : ConvexOn ℝ D φ :=
        perturbationValue_toReal_convexOn_domain
          (P := P) (pStar := pStar) hp hno_bot
      have hDconv : Convex ℝ D := hφconv.1
      have hφcont : ContinuousOn φ (interior D) := hφconv.continuousOn_interior
      have hu_nhds : interior D ∈ 𝓝 u := IsOpen.mem_nhds isOpen_interior hu
      obtain ⟨r, hr, hrsub⟩ :
          ∃ r : ℝ, 0 < r ∧ Metric.closedBall u r ⊆ interior D :=
        Metric.nhds_basis_closedBall.mem_iff.1 hu_nhds
      have hball_int : Metric.ball u r ⊆ interior D := fun z hz =>
        hrsub (Metric.ball_subset_closedBall hz)
      have hball_D : Metric.ball u r ⊆ D := fun z hz => interior_subset (hball_int hz)
      have hφconv_ball : ConvexOn ℝ (Metric.ball u r) φ :=
        hφconv.subset hball_D (convex_ball u r)
      have hφcont_ball : ContinuousOn φ (Metric.ball u r) := hφcont.mono hball_int
      obtain ⟨v, c, hvu, hvball⟩ :=
        local_affine_support_on_ball hr hφconv_ball hφcont_ball
      let ψ : EuclideanSpace ℝ (Fin m) → ℝ := fun z => v z + c
      have hψconc : ConcaveOn ℝ D ψ := (v.toLinearMap.concaveOn hDconv).add_const c
      have hgap_conv : ConvexOn ℝ D (fun z => φ z - ψ z) := hφconv.sub hψconc
      have hlocal_min : IsLocalMinOn (fun z => φ z - ψ z) D u := by
        -- The local support on the ball gives a local minimum for the convex gap `φ - ψ`.
        have hball_nhds : Metric.ball u r ∈ 𝓝[D] u :=
          mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds u hr)
        have hmin_inter : IsMinOn (fun z => φ z - ψ z) (D ∩ Metric.ball u r) u := by
          intro z hz
          rcases hz with ⟨_, hzball⟩
          have hsub : 0 ≤ φ z - ψ z := sub_nonneg.mpr (hvball z hzball)
          simpa [ψ, hvu] using hsub
        have hlocal_inter : IsLocalMinOn (fun z => φ z - ψ z) (D ∩ Metric.ball u r) u :=
          hmin_inter.localize
        have hnhds_eq : 𝓝[D ∩ Metric.ball u r] u = 𝓝[D] u :=
          nhdsWithin_inter_of_mem' hball_nhds
        simpa [IsLocalMinOn, hnhds_eq] using hlocal_inter
      have huD : u ∈ D := hu_top
      have hglobal_min : IsMinOn (fun z => φ z - ψ z) D u :=
        IsMinOn.of_isLocalMinOn_of_convexOn huD hlocal_min hgap_conv
      have hminor_real : ∀ z ∈ D, ψ z ≤ φ z := by
        -- Convexity globalizes the local support inequality to the whole effective domain.
        intro z hzD
        have hsub : 0 ≤ φ z - ψ z := by
          simpa [ψ, hvu] using hglobal_min hzD
        exact sub_nonneg.mp hsub
      have hminor_ereal : ∀ z : EuclideanSpace ℝ (Fin m), ((ψ z : ℝ) : EReal) ≤ pStar z := by
        intro z
        by_cases hz_top : pStar z = ⊤
        · simp [hz_top]
        · have hzD : z ∈ D := lt_of_le_of_ne le_top hz_top
          rw [← EReal.coe_toReal hzD.ne (hno_bot z)]
          exact_mod_cast hminor_real z hzD
      let a : EuclideanSpace ℝ (Fin m) :=
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm v
      have ha_eval : ∀ z : EuclideanSpace ℝ (Fin m), v z = ⟪a, z⟫ := by
        intro z
        simpa [a] using (InnerProductSpace.toDual_symm_apply (x := z) (y := v)).symm
      have hψ_eq : ∀ z : EuclideanSpace ℝ (Fin m), ψ z = ⟪a, z⟫ + c := by
        intro z
        simp [ψ, ha_eval z]
      have hu_value : ((ψ u : ℝ) : EReal) = pStar u := by
        simpa [ψ, φ, hvu] using (EReal.coe_toReal hu_top.ne hu_bot)
      have ha_nonpos : ∀ i : Fin m, a i ≤ 0 := by
        -- Antitonicity of `pStar` along positive coordinate directions forces the affine slope to
        -- be coordinatewise nonpositive.
        intro i
        by_contra hai_pos
        let z : EuclideanSpace ℝ (Fin m) := u + EuclideanSpace.single i 1
        have huz : ∀ j : Fin m, u j ≤ z j := by
          intro j
          by_cases hji : j = i
          · subst hji
            simp [z, EuclideanSpace.single_apply]
          · simp [z, EuclideanSpace.single_apply, hji]
        have hz_le : pStar z ≤ pStar u :=
          perturbationValue_antitone (P := P) (pStar := pStar) hp huz
        have hψ_pos : ψ u < ψ z := by
          rw [hψ_eq, hψ_eq]
          have hz_inner : ⟪a, z⟫ = ⟪a, u⟫ + a i := by
            simp [z, inner_add_right, EuclideanSpace.inner_single_right]
          linarith
        have hψ_pos_ereal : ((ψ u : ℝ) : EReal) < ((ψ z : ℝ) : EReal) := by
          exact_mod_cast hψ_pos
        have : pStar u < pStar z := by
          rw [← hu_value]
          exact lt_of_lt_of_le hψ_pos_ereal (hminor_ereal z)
        exact (not_lt_of_ge hz_le) this
      let lam : EuclideanSpace ℝ (Fin m) := -a
      have hlam : ∀ i : Fin m, 0 ≤ lam i := by
        intro i
        simpa [lam] using neg_nonneg.mpr (ha_nonpos i)
      have hc_le_g : (c : EReal) ≤ g lam := by
        -- The global affine minorant gives a lower bound for every perturbation shift, hence for
        -- their infimum `g lam`.
        rw [dualFunction_eq_iInf_perturbationShift (P := P) (pStar := pStar) (g := g) hp hg hlam]
        refine le_iInf ?_
        intro z
        have hsum : (c : EReal) + (((⟪a, z⟫ : ℝ) : EReal)) ≤ pStar z := by
          simpa [hψ_eq z, add_comm, add_left_comm, add_assoc] using hminor_ereal z
        have hsub :
            (c : EReal) ≤ pStar z - (((⟪a, z⟫ : ℝ) : EReal)) := by
          exact
            (EReal.le_sub_iff_add_le
              (a := (c : EReal))
              (b := (((⟪a, z⟫ : ℝ) : EReal)))
              (c := pStar z)
              (.inl (EReal.coe_ne_bot _))
              (.inl (EReal.coe_ne_top _))).2 hsum
        simpa [lam, sub_eq_add_neg, real_inner_comm, add_comm, add_left_comm, add_assoc] using hsub
      have hu_dual :
          pStar u ≤ g lam - ((⟪u, lam⟫ : ℝ) : EReal) := by
        have hadd :
            (((⟪a, u⟫ : ℝ)) : EReal) + (c : EReal) ≤
              (((⟪a, u⟫ : ℝ)) : EReal) + g lam := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hc_le_g ((((⟪a, u⟫ : ℝ)) : EReal))
        calc
          pStar u = (((⟪a, u⟫ + c : ℝ)) : EReal) := by
            rw [← hu_value, hψ_eq u]
          _ = (((⟪a, u⟫ : ℝ)) : EReal) + (c : EReal) := by simp
          _ ≤ (((⟪a, u⟫ : ℝ)) : EReal) + g lam := hadd
          _ = g lam - ((⟪u, lam⟫ : ℝ) : EReal) := by
            simp [lam, sub_eq_add_neg, real_inner_comm, add_comm, add_left_comm, add_assoc]
      -- Use the multiplier `lam` as an explicit witness in the conjugate supremum.
      rw [convexConjugate]
      have hwitness :
          g lam - ((⟪u, lam⟫ : ℝ) : EReal) ∈
            Set.range (fun y => ((⟪-u, y⟫ : ℝ) : EReal) - -g y) := by
        refine ⟨lam, ?_⟩
        simp [sub_eq_add_neg, inner_neg_left, add_comm, add_left_comm, add_assoc]
      exact le_trans hu_dual (le_sSup hwitness)
  · -- Unfold the conjugate and estimate each affine minorant by weak duality.
    rw [convexConjugate]
    refine sSup_le ?_
    rintro z ⟨lam, rfl⟩
    by_cases hlam : ∀ i : Fin m, 0 ≤ lam i
    · -- Dual-feasible multipliers give affine minorants of the perturbation value.
      simpa [sub_eq_add_neg, inner_neg_left, add_comm, add_left_comm, add_assoc] using
        dualAffineMinorant_le_perturbationValue
          (P := P) (pStar := pStar) (g := g) hp hg (lam := lam) (v := u) hlam
    · -- Non-feasible multipliers contribute `⊥`, so they are irrelevant to the supremum.
      have hg_bot : g lam = ⊥ := by simp [hg, hlam]
      simp [hg_bot, sub_eq_add_neg, inner_neg_left]

end «problem-58»
