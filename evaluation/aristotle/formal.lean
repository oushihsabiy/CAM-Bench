/-
Source: book/convex_optimization_Chp2
-/
import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

-- Exercise_2_37__c_

/- [BLOCK Exercise 2.37-(c) | 86 | defn]
For a cone K ⊆ ℝ^n, its dual cone is K* = { z ∈ ℝ^n | zᵀ x ≥ 0 for all x ∈ K }.
-/
open scoped RealInnerProductSpace

def dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  { z | ∀ ⦃x⦄, x ∈ K → 0 ≤ ⟪z, x⟫ }

/- [BLOCK Exercise 2.37-(c) | 87 | defn]
A matrix H ∈ ℝ^m × m is a Hankel matrix if its entries are constant on anti-diagonals, i.e.,
there exists a sequence (h₁,dots,h_2m-1) such that H_ij = h_i+j-1 for all 1 ≤ i,j ≤ m.
-/
def IsHankelMatrix {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∃ h : Fin (2 * m - 1) → ℝ,
    ∀ i j : Fin m,
      H i j =
        h
          ⟨i.1 + j.1, by
            -- Note: the textbook uses 1-based `h_{i+j-1}`; with `Fin` (0-based),
            -- indexing by `i+j` corresponds to that convention after reindexing `h`.
            cases m with
            | zero =>
                -- no indices exist
                exact False.elim (Fin.elim0 i)
            | succ m =>
                have hi : i.1 ≤ m := Nat.le_of_lt_succ i.2
                have hj : j.1 ≤ m := Nat.le_of_lt_succ j.2
                have hsum : i.1 + j.1 ≤ m + m := Nat.add_le_add hi hj
                -- `i+j ≤ 2m < 2m+1 = 2*(m+1)-1`
                have hm : m + m < 2 * (m + 1) - 1 := by
                  -- `2*(m+1)-1 = m+m+1`
                  simpa [two_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_one] using
                    (Nat.lt_succ_self (m + m))
                exact lt_of_le_of_lt hsum hm⟩

/- [BLOCK Exercise 2.37-(c) | 88 | thm]
Let k ∈ ℕ. Define K_{pol}=≤ft{x ∈ ℝ^{2k+1}\ |dle|\ x₁+x₂ t+x₃ t^2+·s+x_{2k+1} t^{2k}≥ 0 ext{ for all
} t∈ ℝ
ight}. For a cone K ⊆ ℝ^{2k+1}, define its dual cone by K*={z∈ ℝ^{2k+1}| zᵀ x ≥ 0 ext{ for all } x∈
K}. Define K_{han}={z∈ ℝ^{2k+1}| H(z)succeq 0}, where H(z) is the (k+1) imes (k+1) Hankel matrix
with entries H(z)_{ij}=z_{i+j-1}, 1≤ i,j≤ k+1. Show that K_{pol}^*=K_{han}.
-/
def Kpol (k : ℕ) : Set (EuclideanSpace ℝ (Fin (2 * k + 1))) :=
  { x |
    ∀ t : ℝ,
      0 ≤
        (∑ i : Fin (2 * k + 1), (x i) * (t ^ (i.1 : ℕ))) }

def hankelMatrix (k : ℕ) (z : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  fun i j => z ⟨i.1 + j.1, by
    have hi : i.1 < k + 1 := i.2
    have hj : j.1 < k + 1 := j.2
    have hsum : i.1 + j.1 ≤ 2 * k := by
      have hi' : i.1 ≤ k := Nat.le_of_lt_succ hi
      have hj' : j.1 ≤ k := Nat.le_of_lt_succ hj
      calc
        i.1 + j.1 ≤ k + k := Nat.add_le_add hi' hj'
        _ = 2 * k := by omega
    exact Nat.lt_of_le_of_lt hsum (Nat.lt_succ_self (2 * k))⟩

def Khan (k : ℕ) : Set (EuclideanSpace ℝ (Fin (2 * k + 1))) :=
  { z | Matrix.PosSemidef (hankelMatrix k z) }

theorem dualCone_Kpol_eq_Khan (k : ℕ) : dualCone (Kpol k) = Khan k := by
  sorry
