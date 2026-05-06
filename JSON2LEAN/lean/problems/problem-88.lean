import Mathlib

noncomputable section
open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «problem-88»

-- Exercise_17_7__a_

/- [BLOCK Exercise 17.7-(a) | 14 | defn]
For a directed graph with n nodes and m edges, the node-edge incidence matrix is the matrix A ∈
ℝ^n × m with entries A_ij=-1 if edge j leaves node i, A_ij=1 if edge j enters node
i, and A_ij=0 otherwise.
-/
def nodeEdgeIncidenceMatrix (n m : ℕ) (tail head : Fin m → Fin n) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j =>
    if i = head j then
      1
    else if i = tail j then
      -1
    else
      0

/- [BLOCK Exercise 17.7-(a) | 15 | thm]
Consider a directed water-supply network with n nodes and m edges. Nodes 1,ldots,k are supply nodes
and nodes k+1,ldots,n are consumer nodes, where 1 ≤ k ≤ n. Let fⱼ ≥ 0 be the flow on edge j, let hᵢ
be the altitude of node i, let sᵢ ≥ 0 be the supply inflow at node i for i=1,ldots,k, and let cᵢ ≥ 0
be the consumption at node k+i for i=1,ldots,n-k. Thus s ∈ ℝ_+^k, c ∈ ℝ_+^{n-k}, and f ∈ ℝ_+^m. The
flow-conservation equations are Af=[-s; c], where A ∈ ℝ^{n × m} is the node-edge incidence matrix
given by A_{ij}=cases -1 & if edge j leaves node i,; +1 & if edge j enters node i,; 0 & otherwise.
cases Each edge is directed from a higher-altitude node to a lower-altitude node: if edge j goes
from node i to node l, then hᵢ>h_l. For each edge j from node i to node l, the flow satisfies
fⱼ=(α_0 θ_j Rⱼ^2 (hᵢ-h_l))/(Lⱼ), where α_0>0 is given, Lⱼ>0 is the pipe length, Rⱼ>0 is the fixed
known pipe radius, and θ_j ∈ [0,1] is the valve opening. The supply constraints are sᵢ ≤ sᵢ^{max},
i=1,ldots,k. A vector c ∈ ℝ_+^{n-k} is supportable if there exist f ∈ ℝ_+^m, s ∈ ℝ_+^k, and θ ∈ ℝ^m
with 0 ≤ θ_j ≤ 1 for all j, such that all the conditions above hold. Show that the set of
supportable consumption vectors is a polyhedron, and determine how to decide whether a given
consumption vector is supportable.
-/
theorem supportableConsumptionSet_isPolyhedron_and_characterization
    (n m k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : k ≤ n)
    (tail head : Fin m → Fin n)
    (h : Fin n → ℝ)
    (alpha0 : ℝ)
    (halpha0 : 0 < alpha0)
    (L R : Fin m → ℝ)
    (hL : ∀ j, 0 < L j)
    (hR : ∀ j, 0 < R j)
    (edge_descends : ∀ j, h (tail j) > h (head j))
    (smax : Fin k → ℝ)
    (hsmax : ∀ i, 0 ≤ smax i)
    (c : Fin (n - k) → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    let A := nodeEdgeIncidenceMatrix n m tail head
    let edgeCapacity : Fin m → ℝ := fun j => alpha0 * (R j)^2 * (h (tail j) - h (head j)) / (L j)
    let supportable : Set (Fin (n - k) → ℝ) := fun c' =>
      (∀ i, 0 ≤ c' i) ∧
      ∃ f : Fin m → ℝ, ∃ s : Fin k → ℝ, ∃ theta : Fin m → ℝ,
        (∀ j, 0 ≤ f j) ∧
        (∀ i, 0 ≤ s i ∧ s i ≤ smax i) ∧
        (∀ j, 0 ≤ theta j ∧ theta j ≤ 1) ∧
        (∀ i : Fin k,
          ∑ j : Fin m, A ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ j * f j = - s i) ∧
        (∀ i : Fin (n - k),
          ∑ j : Fin m, A ⟨k + i.1, by
            have hi : i.1 < n - k := i.2
            omega⟩ j * f j = c' i) ∧
        (∀ j, f j = edgeCapacity j * theta j)
    (∃ p q : ℕ,
      ∃ M : Matrix (Fin p) (Fin (n - k)) ℝ,
        ∃ N : Matrix (Fin q) (Fin (n - k)) ℝ,
          ∃ b : Fin p → ℝ,
            ∃ d : Fin q → ℝ,
              (∀ c' : Fin (n - k) → ℝ,
                c' ∈ supportable ↔
                  (∀ i : Fin p, ∑ j : Fin (n - k), M i j * c' j ≤ b i) ∧
                  (∀ i : Fin q, ∑ j : Fin (n - k), N i j * c' j = d i)) ∧
              (c ∈ supportable ↔
                (∀ i : Fin p, ∑ j : Fin (n - k), M i j * c j ≤ b i) ∧
                (∀ i : Fin q, ∑ j : Fin (n - k), N i j * c j = d i))) := by
  sorry

end «problem-88»
