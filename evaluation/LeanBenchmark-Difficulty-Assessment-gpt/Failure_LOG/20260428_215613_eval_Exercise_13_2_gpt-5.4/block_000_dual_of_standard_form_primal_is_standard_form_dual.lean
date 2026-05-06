theorem dual_of_standard_form_primal_is_standard_form_dual
    (P : StandardFormPrimalLP) :
    dualProblem (Fin P.m) (Fin P.n) P.c P.b P.A
      = (P.b, P.c, fun j i => P.A i j) := by
  sorry
