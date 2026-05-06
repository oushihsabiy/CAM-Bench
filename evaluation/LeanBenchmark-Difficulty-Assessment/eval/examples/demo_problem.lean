-- Demo problem: 两道小题，每道含 sorry
import Mathlib.Tactic

-- Q1: 简单的自然数等式
theorem add_comm_demo (a b : Nat) : a + b = b + a := by
  sorry

-- Q2: 列表长度
theorem list_length_append (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  sorry
