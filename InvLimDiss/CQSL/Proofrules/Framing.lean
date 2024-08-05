import InvLimDiss.CQSL.Step.Framing
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

namespace CQSL

variable {Var : Type}

open Syntax Semantics QSL unitInterval Action State HeapValue Classical OrdinalApprox

theorem wrle_frame {c : Program Var} {P : StateRV Var}
    (h : (wrtProg c) ∩ (varRV F) = ∅) :
    `[qsl| wrle [c] ([[P]] | [[RI]]) ⋆ [[F]] ⊢ wrle [c] ([[P]] ⋆ [[F]] | [[RI]])] := by
  unfold wrle'
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  rw [← OrdinalApprox.gfpApprox_ord_eq_gfp]
  induction (Order.succ <| Cardinal.mk <| Program Var → StateRV Var).ord
    using Ordinal.induction generalizing c with
  | h i ih =>
    unfold gfpApprox
    simp only [OrderHom.coe_mk, exists_prop, Set.union_singleton, sInf_insert, Pi.inf_apply,
      Pi.top_apply, ge_iff_le, le_top, inf_of_le_right]
    apply le_sInf
    intro Q h_Q
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop,
      exists_exists_and_eq_and] at h_Q
    obtain ⟨j, h_j, rfl⟩ := h_Q
    cases eq_or_ne c [Prog| ↓] with
    | inl h_eq =>
      unfold wrle_step
      simp only [h_eq]
      refine qslSepMul_mono ?_ (le_rfl)
      apply sInf_le
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop,
        exists_exists_and_eq_and, and_true]
      use j
    | inr h_ne_term =>
      cases eq_or_ne c [Prog| ↯] with
      | inl h_eq =>
        unfold wrle_step
        simp only [h_eq]
        rw [← le_qslSepDiv_iff_qslSepMul_le]
        apply sInf_le_of_le
        simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop,
          exists_exists_and_eq_and, exists_and_right]
        · apply And.intro
          · use j
          · rfl
        · exact bot_le
      | inr h_ne_abort =>
        conv => right; rw [wrle_step]
        simp only
        rw [le_qslSepDiv_iff_qslSepMul_le]
        apply le_trans
        pick_goal 2
        · apply step_mono_of_semantics_support
          intro s a _ c' s' h_semantics
          apply qslSepMul_mono
          · have : wrtProg c' ∩ varRV F = ∅ := by {
              apply Set.Subset.antisymm
              · apply Set.Subset.trans
                · exact Set.inter_subset_inter (written_of_transition h_semantics) (Set.Subset.rfl)
                · exact subset_of_eq h
              · exact Set.empty_subset _
            }
            exact ih j h_j this
          · exact le_rfl
        · conv => right; intro s; left; intro c' s'; rw [← qslSepMul_assoc, qslSepMul_comm F RI, qslSepMul_assoc]
          refine le_trans ?_ (step_framing _ (wrtStmt_inter_varRV_eq_emptyset_of_wrtProg h))
          rw [← qslSepMul_assoc ,qslSepMul_comm F RI, qslSepMul_assoc]
          refine qslSepMul_mono ?_ le_rfl
          unfold Entailment.entail instEntailmentStateRV
          simp only [ge_iff_le]
          rw [← le_qslSepDiv_iff_qslSepMul_le]
          apply sInf_le
          simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop,
            exists_exists_and_eq_and]
          use j, h_j
          rw [wrle_step]
          split
          case h_1 => simp only [ne_eq, not_true_eq_false] at h_ne_term
          case h_2 => simp only [ne_eq, not_true_eq_false] at h_ne_abort
          case h_3 => rfl

end CQSL
