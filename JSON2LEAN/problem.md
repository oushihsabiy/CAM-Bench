# JSON2LEAN Lean Problems Audit

Scope: `/root/workspace/benchmark/JSON2LEAN/lean/problems`

Audit criterion: local definitions are acceptable when they preserve the intended semantics. The flagged files below either make the benchmark misleading, put the target result into the input data, use an axiom/opaque external primitive for core content, or weaken algorithmic/complexity claims into unrelated or nearly trivial propositions.

## Recommended Exclusions

These files should not be used directly in a high-quality theorem-proving benchmark without repair.

| File | Reason |
| --- | --- |
| `lean/problems/problem-1.lean` | The feasible set only requires `y ≠ 0`, so `y < 0` is allowed. The later claimed primal value and duality gap match a different intended problem, likely with a positive-domain restriction. |
| `lean/problems/problem-25.lean` | Assumes Hessian positive definite only at one point but concludes the conjugate is globally represented by a real-valued function `g : E → ℝ`. This needs much stronger global finiteness/Legendre-style hypotheses. |
| `lean/problems/problem-36.lean` | The supremum reformulation is forced into `ℝ` via an assumption that every supremum has a real value. This removes the `+∞` behavior that should penalize infeasible points. |
| `lean/problems/problem-47.lean` | The KKT definition checks `gradL = fderiv L`, not stationarity `fderiv L = 0`. The listed KKT point set is therefore not a trustworthy formalization. |
| `lean/problems/problem-69.lean` | The linear-time complexity theorem only proves `∃ ops C, ops ≤ C * n + C`, with `ops` unrelated to the computation. This is a complexity shell. |
| `lean/problems/problem-70.lean` | `P.g` is constrained only where `f t > 0`, but the theorem claims convexity of the full objective. The support/domain behavior is under-specified. |
| `lean/problems/problem-75.lean` | The structure contains `feasible_constraint` and `optimality`; the theorem largely restates fields already stored in the input. |
| `lean/problems/problem-76.lean` | Uses an actual `axiom IsUnivariateNormal`; the structure also stores `optimization_equiv`, putting an equivalence into the data. |
| `lean/problems/problem-100.lean` | `thrustProfiles` is an arbitrary set, but the theorem asserts convexity of the solution set. Missing constraints make the proposition false in general. |
| `lean/problems/problem-130.lean` | The convexity theorem uses `x_i / t_i` on a domain allowing `t_i = 0`, instead of the perspective closure. The real-valued expression does not match the stated extended-real perspective. |
| `lean/problems/problem-136.lean` | Uses `EReal.toReal` on potentially infinite objective values, losing the extended-real domain semantics needed for the convexity/log-likelihood claim. |
| `lean/problems/problem-138.lean` | Same domain issue as `problem-1`: the constraint allows `x_1 < 0` in the denominator coordinate, so the claimed optimum/KKT statement is not the intended problem. |
| `lean/problems/problem-167.lean` | `IsThomasTypeMethod` encodes existence of a solver/op-count but does not bind to a concrete algorithm or real cost model. The O(n) conclusion is too weak. |
| `lean/problems/problem-168.lean` | O(n) computation is reduced to `∃ C, n ≤ C * n + C`, which is a near-trivial arithmetic bound and not an algorithmic complexity statement. |
| `lean/problems/problem-180.lean` | The `θ(n^3)` claim is formalized as `(N+1)^3 = Θ(N^3)` and is not connected to dense KKT solving. |
| `lean/problems/problem-199.lean` | The theorem proves `P.is_feasible` and the definitional objective equation, both already contained in the structure/definitions; it does not formalize a real maximization equivalence. |

## Needs Manual Review / Possible Repair

These are not necessarily invalid, but they contain modeling choices that can hide the intended theorem.

| File | Concern |
| --- | --- |
| `lean/problems/problem-20.lean` | The structure includes `equivalence`, `transformed_feasible_set_convex`, and `transformed_objective_convex` as fields. Some of the target content is already assumed. |
| `lean/problems/problem-33.lean` | The structure includes `optimal_at_xstar`. This may be acceptable as a hypothesis, but it mixes a major mathematical property into the problem data. |
| `lean/problems/problem-148.lean` | `RobustQuadraticProgram` includes `exact_equivalence` as a field. Later theorems do not rely only on it, but the data model is risky for benchmark use. |

## Notes

- The directory contains 200 Lean files, and all checked files elaborate with `sorry`.
- The problem is not primarily the use of local definitions. Many local definitions are reasonable.
- The main benchmark risks are:
  - target results embedded as structure fields,
  - extended-real or domain behavior erased by coercions or `toReal`,
  - algorithmic complexity claims replaced by unrelated arithmetic bounds,
  - core mathematical notions introduced as axioms,
  - formal statements mismatching the natural-language problem domain.

