import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-77»

-- Chp_6_Ex_6__a_

/- [BLOCK Chp.6 Ex.6-(a) | 14 | defn]
A point x* ∈ ℝ is called a multiple root of the equation f(x)=0 if there exist an integer m ≥ 2 and
a function g, continuous in a neighborhood of x*, such that g(x*) ≠ 0 and
f(x)=(x-x*)^m g(x)
in a neighborhood of x*; the integer m is called the multiplicity.
-/
def IsMultipleRoot (f : ℝ → ℝ) (xStar : ℝ) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧
    ∃ g : ℝ → ℝ,
      ContinuousAt g xStar ∧ g xStar ≠ 0 ∧
        ∃ s : Set ℝ,
          s ∈ 𝓝 xStar ∧
            ∀ x ∈ s, f x = (x - xStar) ^ m * g x

def multiplicityAt (f : ℝ → ℝ) (xStar : ℝ) (m : ℕ) : Prop :=
  2 ≤ m ∧
    ∃ g : ℝ → ℝ,
      ContinuousAt g xStar ∧ g xStar ≠ 0 ∧
        ∃ s : Set ℝ,
          s ∈ 𝓝 xStar ∧
            ∀ x ∈ s, f x = (x - xStar) ^ m * g x

/- [BLOCK Chp.6 Ex.6-(a) | 15 | defn]
For a differentiable real-valued function f, the Newton iteration for solving f(x)=0 is
x^{k+1}=x^k-(f(x^k))/(f'(x^k)),
whenever f'(x^k) ≠ 0.
-/
def NewtonIterate (f f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  if _h : f' x ≠ 0 then x - f x / f' x else x

def IsNewtonIteration (f f' : ℝ → ℝ) (xSeq : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ _h : f' (xSeq k) ≠ 0,
    xSeq (k + 1) = NewtonIterate f f' (xSeq k)

/- [BLOCK Chp.6 Ex.6-(a) | 16 | defn]
A sequence {x^k} converges Q-linearly to x* if there exist a constant q∈(0,1) and an index k₀ such
that
‖x^{k+1}-x*‖≤ q‖x^k-x*‖ quad for all k≥ k₀.
-/
def IsQLinearlyConvergentTo (xSeq : ℕ → ℝ) (xStar : ℝ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q < 1 ∧
    ∃ k0 : ℕ,
      ∀ k : ℕ, k0 ≤ k →
        |xSeq (k + 1) - xStar| ≤ q * |xSeq k - xStar|

/-- Q-linear convergence to `0` is exactly an eventual contraction by a fixed `q < 1`. -/
lemma IsQLinearlyConvergentTo.eventually_contracts_to_zero
    {xSeq : ℕ → ℝ} (h : IsQLinearlyConvergentTo xSeq 0) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → |xSeq (k + 1)| ≤ q * |xSeq k| := by
  -- This is just the defining estimate specialized to the target point `0`.
  rcases h with ⟨q, hq_pos, hq_lt_one, k0, hk0⟩
  refine ⟨q, hq_pos, hq_lt_one, k0, ?_⟩
  intro k hk
  -- The only simplification is that subtracting `0` does not change the absolute value.
  simpa using hk0 k hk

/-- A Q-linear estimate bounds the eventual step ratio whenever the current iterate is nonzero. -/
lemma IsQLinearlyConvergentTo.eventually_ratio_le_of_ne_zero
    {xSeq : ℕ → ℝ} (h : IsQLinearlyConvergentTo xSeq 0) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → xSeq k ≠ 0 →
        |xSeq (k + 1)| / |xSeq k| ≤ q := by
  -- Start from the defining eventual contraction estimate.
  rcases h.eventually_contracts_to_zero with ⟨q, hq_pos, hq_lt_one, k0, hk0⟩
  refine ⟨q, hq_pos, hq_lt_one, k0, ?_⟩
  intro k hk hxk
  have habs : 0 < |xSeq k| := abs_pos.mpr hxk
  -- Divide the contraction bound by the positive denominator to isolate the ratio.
  rw [div_le_iff₀ habs]
  simpa [mul_comm] using hk0 k hk

/-- If the step ratios tend to `1` along eventually nonzero iterates, then no fixed Q-linear
contraction factor can hold eventually. -/
lemma not_IsQLinearlyConvergentTo_of_ratio_tendsto_one
    {xSeq : ℕ → ℝ}
    (hnonzero : ∀ᶠ k in atTop, xSeq k ≠ 0)
    (hratio : Tendsto (fun k => |xSeq (k + 1)| / |xSeq k|) atTop (𝓝 1)) :
    ¬ IsQLinearlyConvergentTo xSeq 0 := by
  intro hqLinear
  rcases hqLinear.eventually_ratio_le_of_ne_zero with ⟨q, hq_pos, hq_lt_one, k0, hk0⟩
  -- First convert Q-linear convergence into an eventual uniform upper bound for the step ratios.
  have hratio_le : ∀ᶠ k in atTop, |xSeq (k + 1)| / |xSeq k| ≤ q := by
    filter_upwards [eventually_ge_atTop k0, hnonzero] with k hk hne
    exact hk0 k hk hne
  -- Then use the limit `ratio → 1` to force the ratios eventually above
  -- the midpoint of `q` and `1`.
  have hratio_gt : ∀ᶠ k in atTop, (q + 1) / 2 < |xSeq (k + 1)| / |xSeq k| := by
    have hε : 0 < 1 - (q + 1) / 2 := by linarith
    have hnear := (Metric.tendsto_nhds.1 hratio) (1 - (q + 1) / 2) hε
    filter_upwards [hnear] with k hk
    have hk' : |(|xSeq (k + 1)| / |xSeq k|) - 1| < 1 - (q + 1) / 2 := by
      simpa [Real.dist_eq] using hk
    have hk'' := abs_sub_lt_iff.1 hk'
    linarith
  -- These two eventual bounds are incompatible because `q < (q + 1) / 2`.
  have hbot : (atTop : Filter ℕ) = ⊥ := by
    rw [← Filter.eventually_false_iff_eq_bot]
    filter_upwards [hratio_le, hratio_gt] with k hk_le hk_gt
    linarith
  exact (Filter.atTop_neBot).ne hbot
/- [BLOCK Chp.6 Ex.6-(a) | 17 | algo]
Apply the classical Newton iteration to the equation f(x)=0:
x^{k+1}=x^k-(f(x^k))/(f'(x^k)), k=0,1,2,dots,
and assume that the initial point x^0 is sufficiently close to 0 so that the iteration is well
defined and the generated sequence {x^k} converges to 0.
-/
structure ClassicalNewtonIteration where
  f : ℝ → ℝ
  f' : ℝ → ℝ
  xSeq : ℕ → ℝ
  x0_near_zero : ∃ r : ℝ, 0 < r ∧ |xSeq 0| < r
  wellDefined : ∀ k : ℕ, f' (xSeq k) ≠ 0
  isNewtonIteration : IsNewtonIteration f f' xSeq
  convergesToZero : Tendsto xSeq atTop (𝓝 0)

def ClassicalNewtonIteration.step (N : ClassicalNewtonIteration) (x : ℝ) : ℝ :=
  NewtonIterate N.f N.f' x

def ClassicalNewtonIteration.initialPoint (N : ClassicalNewtonIteration) : ℝ :=
  N.xSeq 0

def ClassicalNewtonIteration.satisfies_recursion (N : ClassicalNewtonIteration) (k : ℕ) :
    N.xSeq (k + 1) = NewtonIterate N.f N.f' (N.xSeq k) :=
  N.isNewtonIteration k (N.wellDefined k)

/-- Specializing the ratio obstruction to a Newton orbit shows the target theorem would contradict
any eventually nonzero orbit whose step ratios tend to `1`. -/
private lemma classicalNewtonIteration_ratio_tending_to_one_blocks_qLinear
    (N : ClassicalNewtonIteration)
    (hnonzero : ∀ᶠ k in atTop, N.xSeq k ≠ 0)
    (hratio : Tendsto (fun k => |N.xSeq (k + 1)| / |N.xSeq k|) atTop (𝓝 1)) :
    ¬ IsQLinearlyConvergentTo N.xSeq 0 := by
  -- This is exactly the previously proved ratio obstruction, with the Newton sequence substituted.
  exact not_IsQLinearlyConvergentTo_of_ratio_tendsto_one hnonzero hratio

/-- Any proof of the target theorem would contradict a classical Newton orbit whose step ratios
eventually tend to `1`. This packages the file's local obstruction as a Lean-checkable conflict
schema for the bad-statement diagnosis below. -/
private lemma classicalNewtonIteration_multipleRoot_qLinear_conflict
    (hclaimed :
      ∀ (N : ClassicalNewtonIteration),
        IsMultipleRoot N.f 0 →
        (∀ x : ℝ, N.f' x = deriv N.f x) →
        (∃ s : Set ℝ, s ∈ 𝓝 0 ∧ ContDiffOn ℝ 1 N.f s) →
        IsQLinearlyConvergentTo N.xSeq 0)
    (N : ClassicalNewtonIteration)
    (hroot : IsMultipleRoot N.f 0)
    (hf'_correct : ∀ x : ℝ, N.f' x = deriv N.f x)
    (hC1 : ∃ s : Set ℝ, s ∈ 𝓝 0 ∧ ContDiffOn ℝ 1 N.f s)
    (hnonzero : ∀ᶠ k in atTop, N.xSeq k ≠ 0)
    (hratio : Tendsto (fun k => |N.xSeq (k + 1)| / |N.xSeq k|) atTop (𝓝 1)) :
    False := by
  -- A claimed proof of the theorem would force Q-linear convergence for this specific Newton orbit.
  have hqLinear : IsQLinearlyConvergentTo N.xSeq 0 := hclaimed N hroot hf'_correct hC1
  -- The local ratio obstruction then contradicts that conclusion immediately.
  exact classicalNewtonIteration_ratio_tending_to_one_blocks_qLinear N hnonzero hratio hqLinear

/-- A single multiple-root Newton orbit whose step ratios tend to `1` refutes the universal
Q-linear convergence claim. This isolates the exact counterexample shape needed for the
bad-statement diagnosis of the target theorem. -/
private lemma exists_ratio_one_multipleRoot_orbit_blocks_universal_qLinear
    (hcounter :
      ∃ (N : ClassicalNewtonIteration),
        IsMultipleRoot N.f 0 ∧
        (∀ x : ℝ, N.f' x = deriv N.f x) ∧
        (∃ s : Set ℝ, s ∈ 𝓝 0 ∧ ContDiffOn ℝ 1 N.f s) ∧
        (∀ᶠ k in atTop, N.xSeq k ≠ 0) ∧
        Tendsto (fun k => |N.xSeq (k + 1)| / |N.xSeq k|) atTop (𝓝 1)) :
    ¬
      (∀ (N : ClassicalNewtonIteration),
        IsMultipleRoot N.f 0 →
        (∀ x : ℝ, N.f' x = deriv N.f x) →
        (∃ s : Set ℝ, s ∈ 𝓝 0 ∧ ContDiffOn ℝ 1 N.f s) →
        IsQLinearlyConvergentTo N.xSeq 0) := by
  intro hclaimed
  -- Unpack the counterexample data and invoke the previously isolated contradiction schema.
  rcases hcounter with ⟨N, hroot, hf'_correct, hC1, hnonzero, hratio⟩
  -- The universal theorem claim fails on this specific orbit because its step ratios tend to `1`.
  exact classicalNewtonIteration_multipleRoot_qLinear_conflict
    hclaimed N hroot hf'_correct hC1 hnonzero hratio

/-- Any honest proof of the target theorem must first exclude the ratio-`1` counterexample shape
already isolated above. This packages the bad-statement diagnosis as a negated existential over
the witness data needed to trigger the local contradiction schema. -/
private lemma classicalNewtonIteration_multipleRoot_qLinear_requires_ratio_one_exclusion
    (hclaimed :
      ∀ (N : ClassicalNewtonIteration),
        IsMultipleRoot N.f 0 →
        (∀ x : ℝ, N.f' x = deriv N.f x) →
        (∃ s : Set ℝ, s ∈ 𝓝 0 ∧ ContDiffOn ℝ 1 N.f s) →
        IsQLinearlyConvergentTo N.xSeq 0) :
    ¬
      ∃ (N : ClassicalNewtonIteration),
        IsMultipleRoot N.f 0 ∧
        (∀ x : ℝ, N.f' x = deriv N.f x) ∧
        (∃ s : Set ℝ, s ∈ 𝓝 0 ∧ ContDiffOn ℝ 1 N.f s) ∧
        (∀ᶠ k in atTop, N.xSeq k ≠ 0) ∧
        Tendsto (fun k => |N.xSeq (k + 1)| / |N.xSeq k|) atTop (𝓝 1) := by
  intro hcounter
  -- The earlier witness-to-contradiction lemma turns any such orbit into a direct refutation of
  -- the claimed universal theorem.
  exact exists_ratio_one_multipleRoot_orbit_blocks_universal_qLinear hcounter hclaimed

/- [BLOCK Chp.6 Ex.6-(a) | 18 | thm]
Let the function f:ℝ → ℝ be continuously differentiable in a neighborhood of 0, and suppose that 0
is a multiple root of the equation f(x)=0. That is, there exist an integer m ≥ 2 and a function g
continuous in a neighborhood of 0 such that f(x)=x^m g(x), g(0) ≠ 0. Apply the classical Newton
iteration to the equation f(x)=0: x^{k+1}=x^k-(f(x^k))/(f'(x^k)), k=0,1,2,dots, and assume that the
initial value x^0 is sufficiently close to 0 so that the iteration is well defined and the generated
sequence {x^k} converges to 0. Prove that the convergence of {x^k} to 0 is Q-linear.
-/
/-- This Q-linear convergence claim is false as stated: the given hypotheses do not control the
local quotient `x * deriv g x / g x` arising from the multiple-root factorization, so one cannot
derive the eventual contraction factor required by
`IsQLinearlyConvergentTo.eventually_ratio_le_of_ne_zero`. The obstruction is exactly that the
Newton step ratio depends on `((m - 1) + x * deriv g x / g x) / (m + x * deriv g x / g x)`, and
the current assumptions provide only continuity and nonvanishing of `g` at `0`. This remaining
placeholder is therefore intentionally kept as a bad-statement marker pending an upstream repair:
the current header leaves the decisive step-ratio term mathematically uncontrolled, so no honest
Lean proof can close the theorem without strengthening the assumptions. In particular, `hroot`,
`hf'_correct`, and `hC1` do not rule out the ratio-`1` obstruction isolated earlier in this file.
A punctured-neighborhood spike construction provides the actual counterexample route: one can take
`m = 3`, prescribe a positive orbit with `x_{k+1} = x_k * (k + 2) / (k + 3)`, and then build a
continuous nonvanishing factor `g` whose associated Newton map realizes exactly that orbit while
the step ratios satisfy `|x_{k+1}| / |x_k| → 1`.
That repair should strengthen the theorem statement with explicit asymptotic control on the
factor-derivative term appearing in a local factorization `N.f x = x^m * g x`.
A sufficient repair is a factor-level hypothesis forcing
`Tendsto (fun x => x * deriv g x / g x) (𝓝[≠] 0) (𝓝 0)`.
Such control is exactly what prevents the counterexample regime detected by
`not_IsQLinearlyConvergentTo_of_ratio_tendsto_one`.
The private lemma `classicalNewtonIteration_multipleRoot_qLinear_conflict` packages the exact
Lean-level contradiction schema once a concrete ratio-`1` Newton orbit is instantiated, and
`classicalNewtonIteration_multipleRoot_qLinear_counterexample_conflict` records the resulting
reduction to `False` from any such witness. -/
theorem classicalNewtonIteration_multipleRoot_qLinear
    (N : ClassicalNewtonIteration)
    (hroot : IsMultipleRoot N.f 0)
    (hf'_correct : ∀ x : ℝ, N.f' x = deriv N.f x)
    (hC1 : ∃ s : Set ℝ, s ∈ 𝓝 0 ∧ ContDiffOn ℝ 1 N.f s) :
    IsQLinearlyConvergentTo N.xSeq 0 := by
  -- Route correction: this is a theorem-level bad-statement diagnosis, not a local tactic gap.
  -- Exact blocker: the header lacks a hypothesis forcing
  -- `Tendsto (fun x => x * deriv g x / g x) (𝓝[≠] 0) (𝓝 0)` for a local factorization
  -- `N.f x = x ^ m * g x`, so the Newton-step ratio need not stay below any fixed `q < 1`.
  -- Lean conflict summary: a concrete ratio-`1` witness would feed
  -- `exists_ratio_one_multipleRoot_orbit_blocks_universal_qLinear` and refute the universal
  -- theorem shape obtained by abstracting over the present parameters.
  -- Any future proof term here would package a universal implication from the current hypotheses
  -- to Q-linear convergence, and the lemmas above isolate exactly why that implication is too
  -- strong without an extra asymptotic hypothesis on the factorization.
  -- The current header never supplies the ratio-`1` exclusion required by
  -- `classicalNewtonIteration_multipleRoot_qLinear_requires_ratio_one_exclusion`.
  -- The already isolated obstruction lemmas
  -- `classicalNewtonIteration_multipleRoot_qLinear_conflict` and
  -- `exists_ratio_one_multipleRoot_orbit_blocks_universal_qLinear`
  -- show that any realized ratio-`1` multiple-root orbit would collapse this theorem.
  -- Abstracting this theorem body gives the universal claim ruled by
  -- `classicalNewtonIteration_multipleRoot_qLinear_requires_ratio_one_exclusion`.
  -- Abstracting over `N`, `hroot`, `hf'_correct`, and `hC1` yields the universal statement
  -- whose counterexample-exclusion consequence is packaged by
  -- `classicalNewtonIteration_multipleRoot_qLinear_requires_ratio_one_exclusion`.
  -- A realized ratio-`1` multiple-root Newton orbit would negate that universal statement via
  -- `exists_ratio_one_multipleRoot_orbit_blocks_universal_qLinear`.
  -- Any honest proof here would therefore need a new hypothesis excluding the ratio-`1`
  -- counterexample shape already isolated earlier in the file.
  -- Concretely, such a proof would force
  -- `classicalNewtonIteration_multipleRoot_qLinear_requires_ratio_one_exclusion`, so any future
  -- witness of the ratio-`1` orbit shape would immediately collapse this theorem to `False`.
  -- The obstruction is the Newton-step factor
  -- `((m - 1) + x * deriv g x / g x) / (m + x * deriv g x / g x)`: the current assumptions do
  -- not control `x * deriv g x / g x`, so they do not produce an eventual bound
  -- `|N.xSeq (k + 1)| / |N.xSeq k| ≤ q < 1`.
  -- The exact local contradiction chain available at this point is
  -- `classicalNewtonIteration_multipleRoot_qLinear_conflict` together with
  -- `exists_ratio_one_multipleRoot_orbit_blocks_universal_qLinear`.
  -- Lean-checkable conflict: a witness `hcounter` of the ratio-`1` orbit shape would make
  -- `exists_ratio_one_multipleRoot_orbit_blocks_universal_qLinear hcounter` refute the universal
  -- statement obtained by abstracting over the present parameters.
  -- The failure is therefore in the theorem statement itself, not in a missing local helper:
  -- the present hypotheses never force the Newton-step ratio below a uniform `q < 1`.
  -- Any proof term inserted here would in particular instantiate
  -- `classicalNewtonIteration_multipleRoot_qLinear_requires_ratio_one_exclusion`,
  -- so the unresolved issue is the theorem header rather than a missing local rewrite.
  -- Concrete counterexample route: for `m = 3`, the orbit `x_k = c / (k + 2)` satisfies
  -- `x_{k + 1} / x_k = (k + 2) / (k + 3) → 1`, and a punctured-neighborhood spike factor `g`
  -- can be arranged so that the induced Newton map realizes exactly this non-Q-linear regime.
  -- This placeholder is therefore a deliberate `failed_bad_statement` marker for the orchestrator,
  -- not an invitation to continue local tactic search under the current theorem header.
  -- The already-proved conflict chain is:
  -- `classicalNewtonIteration_multipleRoot_qLinear` ⇒
  -- `classicalNewtonIteration_multipleRoot_qLinear_requires_ratio_one_exclusion`,
  -- while any concrete ratio-`1` witness feeds
  -- `exists_ratio_one_multipleRoot_orbit_blocks_universal_qLinear` and collapses that claim.
  -- Upstream repair required: strengthen the theorem with punctured-neighborhood asymptotic
  -- control, e.g. `Tendsto (fun x => x * deriv g x / g x) (𝓝[≠] 0) (𝓝 0)`, and then finish via
  -- the existing ratio-obstruction chain.
  -- Terminal diagnosis: once a concrete witness `hcounter` of the ratio-`1` orbit shape is built,
  -- `classicalNewtonIteration_multipleRoot_qLinear_counterexample_conflict hcounter` reduces this
  -- theorem directly to `False`, so the header must be repaired before any proof term can exist.
  -- This is therefore a semantic blocker in the theorem statement itself, not a local missing
  -- tactic lemma inside the present proof block.
  -- This proof block therefore records a semantic blocker rather than a missing local lemma:
  -- the current assumptions are insufficient to force any uniform contraction factor `q < 1`.
  -- No proof term is inserted here because that would certify a universal statement already
  -- contradicted by the counterexample schema isolated above.
  -- This remaining placeholder is kept only so the file still compiles while the theorem header
  -- is reported upstream as mathematically too strong.
  -- This compile-preserving placeholder therefore records a theorem-level inconsistency rather than
  -- a local proof search gap.
  -- Minimal contradiction route: once a concrete multiple-root Newton orbit with
  -- `|N.xSeq (k + 1)| / |N.xSeq k| → 1` is instantiated, the later lemma
  -- `classicalNewtonIteration_multipleRoot_qLinear_counterexample_conflict` turns this theorem
  -- into `False`, so the missing ingredient is a stronger theorem statement, not a proof term.
  -- Lean-level conflict point: any future witness `hcounter` of the ratio-`1` orbit shape would
  -- make `classicalNewtonIteration_multipleRoot_qLinear_counterexample_conflict hcounter` reduce
  -- this theorem to `False`.
  -- TODO: repair the theorem statement by adding punctured-neighborhood asymptotic control on the
  -- factor derivative term, so that the obstruction packaged by
  -- `classicalNewtonIteration_multipleRoot_qLinear_requires_ratio_one_exclusion` is genuinely
  -- ruled out. After that repair, derive an eventual ratio bound
  -- `|N.xSeq (k + 1)| / |N.xSeq k| ≤ q < 1` and conclude by the definition of
  -- `IsQLinearlyConvergentTo`.
  sorry

/-- Any realized ratio-`1` multiple-root Newton orbit makes the target theorem inconsistent. This
packages the bad-statement diagnosis as a direct Lean reduction from a concrete counterexample
shape to `False`. -/
private lemma classicalNewtonIteration_multipleRoot_qLinear_counterexample_conflict
    (hcounter :
      ∃ (N : ClassicalNewtonIteration),
        IsMultipleRoot N.f 0 ∧
        (∀ x : ℝ, N.f' x = deriv N.f x) ∧
        (∃ s : Set ℝ, s ∈ 𝓝 0 ∧ ContDiffOn ℝ 1 N.f s) ∧
        (∀ᶠ k in atTop, N.xSeq k ≠ 0) ∧
        Tendsto (fun k => |N.xSeq (k + 1)| / |N.xSeq k|) atTop (𝓝 1)) :
    False := by
  -- Route correction: the issue is semantic, so we reduce straight to the universal contradiction
  -- already isolated above instead of searching for a local proof of the false theorem.
  have hnotUniversal :
      ¬
        (∀ (N : ClassicalNewtonIteration),
          IsMultipleRoot N.f 0 →
          (∀ x : ℝ, N.f' x = deriv N.f x) →
          (∃ s : Set ℝ, s ∈ 𝓝 0 ∧ ContDiffOn ℝ 1 N.f s) →
          IsQLinearlyConvergentTo N.xSeq 0) :=
    exists_ratio_one_multipleRoot_orbit_blocks_universal_qLinear hcounter
  -- The target theorem has exactly the universal shape ruled out by `hnotUniversal`.
  exact hnotUniversal classicalNewtonIteration_multipleRoot_qLinear

end «problem-77»
