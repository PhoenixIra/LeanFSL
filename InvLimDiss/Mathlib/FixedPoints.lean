import Mathlib.SetTheory.Ordinal.FixedPointApproximants

variable [CompleteLattice α]

theorem OrdinalApprox.gfpApprox_le_gfpApprox_of_le (f g : α →o α) (x : α) (h : f ≤ g) :
    gfpApprox f x ≤ gfpApprox g x := by
  intro i
  induction i using Ordinal.induction with
  | h i ih =>
    unfold gfpApprox
    apply le_sInf
    simp only [exists_prop, Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq, sInf_insert,
      forall_eq_or_imp, inf_le_left, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      true_and]
    intro i' h_lt
    apply inf_le_of_right_le
    apply sInf_le_of_le
    · use i'
    · apply le_trans (h _)
      simp only [OrderHom.toFun_eq_coe]
      apply g.monotone
      exact ih i' h_lt
