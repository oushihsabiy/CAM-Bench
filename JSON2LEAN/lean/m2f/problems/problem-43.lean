import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-43»
/-
A cone K ⊆ ℝ^m is a proper convex cone if it is convex, closed, has nonempty interior, and is
pointed, i. e. K cap (- K) = {0}.
-/
def IsProperConvexCone (K : Set (Fin m → ℝ)) : Prop :=
  (∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin m → ℝ⦄, x ∈ K → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  Set.Nonempty (interior K) ∧
  K ∩ {x | -x ∈ K} = {0}

/-
Given a cone K ⊆ ℝ^m, the generalized inequality induced by K is the relation y preceq_K z defined
by z - y ∈ K.
-/
def GeneralizedInequality (K : Set (Fin m → ℝ)) (y z : Fin m → ℝ) : Prop :=
  z - y ∈ K

/-
For a map f: ℝ^n → ℝ^m, its K - epigraph is epi_K f = {(x, t) ∈ ℝ^n × ℝ^m | f(x) preceq_K t}.
-/
def KEpigraph (K : Set (Fin m → ℝ)) (f : (Fin n → ℝ) → Fin m → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {p | GeneralizedInequality K (f p.1) p.2}

/-
A function f: ℝ^n → ℝ^m is K - convex if for all x, y ∈ ℝ^n and all θ ∈ [0, 1], f(θ x + (1 - θ)y)
preceq_K θ f(x) + (1 - θ)f(y).
-/
def IsKConvex (K : Set (Fin m → ℝ)) (f : (Fin n → ℝ) → Fin m → ℝ) : Prop :=
  ∀ ⦃x y : Fin n → ℝ⦄, ∀ ⦃θ : ℝ⦄,
    0 ≤ θ → θ ≤ 1 →
      GeneralizedInequality K
        (f (θ • x + (1 - θ) • y))
        (θ • f x + (1 - θ) • f y)

/-- A proper convex cone contains the origin. -/
lemma zero_mem_of_isProperConvexCone {K : Set (Fin m → ℝ)} (hK : IsProperConvexCone K) :
    (0 : Fin m → ℝ) ∈ K := by
  -- Pick a point from the nonempty interior and scale it down to the origin.
  rcases hK.2.2.2.1 with ⟨u, hu_int⟩
  have huK : u ∈ K := interior_subset hu_int
  simpa using hK.1 (show 0 ≤ (0 : ℝ) by norm_num) huK

/-- A proper convex cone is closed under addition. -/
lemma add_mem_of_isProperConvexCone {K : Set (Fin m → ℝ)} (hK : IsProperConvexCone K)
    {u v : Fin m → ℝ} (hu : u ∈ K) (hv : v ∈ K) : u + v ∈ K := by
  -- First place the midpoint combination in the cone using convexity.
  have hconv := convex_iff_add_mem.mp hK.2.1
  have hmid : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v ∈ K := by
    exact hconv hu hv (by positivity) (by positivity) (by norm_num)
  -- Then scale by `2` to recover the sum `u + v`.
  have hscaled : (2 : ℝ) • ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v) ∈ K :=
    hK.1 (by positivity) hmid
  have hsum : (2 : ℝ) • ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v) = u + v := by
    -- Check the vector identity coordinatewise and use scalar arithmetic in `ℝ`.
    ext i
    simp [Pi.smul_apply, Pi.add_apply]
    ring
  rw [hsum] at hscaled
  exact hscaled

/-- The epigraph defect splits into the cone contribution from the heights and the Jensen defect. -/
lemma epigraph_defect_decomposition {f : (Fin n → ℝ) → Fin m → ℝ}
    (x y : Fin n → ℝ) (t s : Fin m → ℝ) (a b : ℝ) :
    (a • t + b • s) - f (a • x + b • y) =
      (a • (t - f x) + b • (s - f y)) + ((a • f x + b • f y) - f (a • x + b • y)) := by
  -- Compare both sides pointwise and expand the scalar algebra.
  ext i
  simp [Pi.smul_apply, Pi.add_apply, Pi.sub_apply]
  ring

/-
Let K ⊆ ℝ^m be a proper convex cone, and define the generalized inequality preceq_K on ℝ^m by y
preceq_K z if z - y ∈ K. Let f: ℝ^n → ℝ^m, and define its K - epigraph by epi_K f = {(x, t)∈ ℝ^n×
ℝ^m |
f(x)preceq_K t}. A function f is called K - convex if for all x, y∈ ℝ^n and all θ∈[0, 1], f(θ
x + (1 - θ)y)preceq_K θ f(x) + (1 - θ)f(y). Show that f is K - convex if and only if epi_K f is a
convex set.
-/
theorem isKConvex_iff_convex_KEpigraph
    {K : Set (Fin m → ℝ)} {f : (Fin n → ℝ) → Fin m → ℝ}
    (hK : IsProperConvexCone K) :
    IsKConvex K f ↔ Convex ℝ (KEpigraph K f) := by
  constructor
  · intro hf
    -- Rewrite epigraph convexity into explicit coefficient form.
    rw [convex_iff_add_mem]
    intro p hp q hq a b ha hb hab
    rcases p with ⟨x, t⟩
    rcases q with ⟨y, s⟩
    simp only [KEpigraph, GeneralizedInequality] at hp hq
    change (a • t + b • s - f (a • x + b • y) ∈ K)
    -- Use convexity of the cone on the two epigraph defects.
    have hconv := convex_iff_add_mem.mp hK.2.1
    have hcone : a • (t - f x) + b • (s - f y) ∈ K := hconv hp hq ha hb hab
    -- Re-express the second coefficient as `1 - a` and invoke `K`-convexity of `f`.
    have ha1 : a ≤ 1 := by linarith
    have hb' : b = 1 - a := by linarith
    have hjensen : (a • f x + b • f y) - f (a • x + b • y) ∈ K := by
      simpa [GeneralizedInequality, hb'] using hf (x := x) (y := y) (θ := a) ha ha1
    -- Split the target defect into the two cone elements and add them inside `K`.
    rw [epigraph_defect_decomposition]
    exact add_mem_of_isProperConvexCone hK hcone hjensen
  · intro hEpigraph
    -- Put the diagonal points `(x, f x)` and `(y, f y)` into the epigraph using `0 ∈ K`.
    intro x y θ hθ0 hθ1
    have hzero : (0 : Fin m → ℝ) ∈ K := zero_mem_of_isProperConvexCone hK
    have hx : (x, f x) ∈ KEpigraph K f := by
      simpa [KEpigraph, GeneralizedInequality] using hzero
    have hy : (y, f y) ∈ KEpigraph K f := by
      simpa [KEpigraph, GeneralizedInequality] using hzero
    -- Apply convexity of the epigraph to the diagonal points with weights `θ` and `1 - θ`.
    have hconv := convex_iff_add_mem.mp hEpigraph
    have hθ' : 0 ≤ 1 - θ := by linarith
    have hmem : θ • (x, f x) + (1 - θ) • (y, f y) ∈ KEpigraph K f :=
      hconv hx hy hθ0 hθ' (by ring)
    simpa [KEpigraph, GeneralizedInequality] using hmem
end «problem-43»
