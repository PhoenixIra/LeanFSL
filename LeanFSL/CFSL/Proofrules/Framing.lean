import LeanFSL.CFSL.Step.Framing
import LeanFSL.CFSL.WeakExpectation
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

namespace CFSL

variable {Var : Type}

open Syntax Semantics FSL unitInterval Action State HeapValue Classical OrdinalApprox

theorem wrle_frame {c : Program Var} {P : StateRV Var}
    (h : (wrtProg c) ∩ (varRV F) = ∅) :
    `[fsl| wrle [c] ([[P]] | [[RI]]) ⋆ [[F]] ⊢ wrle [c] ([[P]] ⋆ [[F]] | [[RI]])] := by
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
      simp only [wrleStepHom, OrderHom.coe_mk, wrleStep, h_eq]
      refine fslSepMul_mono ?_ (le_rfl)
      apply sInf_le
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop,
        exists_exists_and_eq_and, and_true]
      use j, h_j
      simp only [wrleStep]
    | inr h_ne_term =>
      cases eq_or_ne c [Prog| ↯] with
      | inl h_eq =>
        simp only [wrleStepHom, OrderHom.coe_mk, h_eq, wrleStep]
        rw [← le_fslSepDiv_iff_fslSepMul_le]
        apply sInf_le_of_le
        · simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop,
            exists_exists_and_eq_and, exists_and_right]
          use j, h_j
        · exact bot_le
      | inr h_ne_abort =>
        conv => right; rw [wrleStepHom, OrderHom.coe_mk]; unfold wrleStep
        simp only
        rw [le_fslSepDiv_iff_fslSepMul_le]
        apply le_trans
        pick_goal 2
        · apply step_mono_of_semantics_support
          intro s a _ c' s' h_semantics
          apply fslSepMul_mono
          · have : wrtProg c' ∩ varRV F = ∅ := by {
              apply Set.Subset.antisymm
              · apply Set.Subset.trans
                · exact Set.inter_subset_inter (written_of_transition h_semantics) (Set.Subset.rfl)
                · exact subset_of_eq h
              · exact Set.empty_subset _
            }
            exact ih j h_j this
          · exact le_rfl
        · conv => right; intro s; left; intro c' s'; rw [← fslSepMul_assoc, fslSepMul_comm F RI, fslSepMul_assoc]
          refine le_trans ?_ (step_framing _ (wrtStmt_inter_varRV_eq_emptyset_of_wrtProg h))
          rw [← fslSepMul_assoc ,fslSepMul_comm F RI, fslSepMul_assoc]
          refine fslSepMul_mono ?_ le_rfl
          unfold Entailment.entail instEntailmentStateRV
          simp only [ge_iff_le]
          rw [← le_fslSepDiv_iff_fslSepMul_le]
          apply sInf_le
          simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop,
            exists_exists_and_eq_and]
          use j, h_j
          rw [wrleStepHom, OrderHom.coe_mk, wrleStep]
          · exact h_ne_term
          · exact h_ne_abort

end CFSL
