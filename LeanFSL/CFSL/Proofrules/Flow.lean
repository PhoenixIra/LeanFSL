import LeanFSL.CFSL.WeakExpectation
import LeanFSL.SL.FuzzySubstSimp
import LeanFSL.SL.Classical
import LeanFSL.CFSL.Step.Framing
import LeanFSL.CFSL.Proofrules.Inductive
import LeanFSL.Mathlib.FixedPoints

/-!
  Proofrules for wrle with flow programs that are not inductive (i.e. looping, choices) as one should use it for reasoning about concurrent probabilistic programs.
-/

namespace CFSL

open FSL Syntax OrderHom unitInterval Atom Semantics

theorem wrle_probabilisticBranching :
    `[fsl| <e> ⬝ wrle [c₁] ([[P]] | [[resource]])
        + ~<e> ⬝ wrle [c₂] ([[P]] | [[resource]])
        ⊢ wrle [pif e then [[c₁]] else [[c₂]] fi] ([[P]] | [[resource]])] := by
  nth_rw 3 [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_fslSepDiv_iff_fslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [wrtStmt, Set.empty_inter]
  · refine fslSepMul_mono ?_ le_rfl
    intro s
    rw [step_probChoice]
    split_ifs
    case pos h_abort₁ h_abort₂ =>
      rw [h_abort₁, h_abort₂, wrle_eq_of_abort]
      simp only [fslAdd, fslMul, fslReal, fslFalse, mul_zero, fslNot, truncatedAdd_zero, add_zero,
        le_refl]
    case neg h_abort₁ _ =>
      rw [h_abort₁, wrle_eq_of_abort]
      simp only [fslAdd, fslMul, fslReal, fslFalse, mul_zero, fslNot, zero_truncatedAdd, zero_add,
        le_refl]
    case pos h_abort₂ =>
      rw [h_abort₂, wrle_eq_of_abort]
      simp only [fslAdd, fslMul, fslReal, fslFalse, mul_zero, truncatedAdd_zero, add_zero, le_refl]
    case neg =>
      simp only [fslAdd, fslMul, fslReal, fslNot]
      rfl

open SL in
theorem wrle_conditionalBranching {e : BoolExp Var} :
    `[fsl| ⁅<e>⁆ ⬝ wrle [c₁] ([[P]] | [[resource]])
        ⊔ ~⁅<e>⁆ ⬝ wrle [c₂] ([[P]] | [[resource]])
        ⊢ wrle [if e then [[c₁]] else [[c₂]] fi] ([[P]] | [[resource]])] := by
  nth_rw 3 [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_fslSepDiv_iff_fslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [wrtStmt, Set.empty_inter]
  · refine fslSepMul_mono ?_ le_rfl
    intro s
    show `[fsl| ⁅<e>⁆ ⬝ [[_]]] s ⊔ `[fsl| ~⁅<e>⁆ ⬝ [[_]]] s ≤ _
    by_cases e s.stack
    case pos h_e =>
      rw [step_condChoice_left _ _ h_e]
      split
      case isTrue h_abort₁ =>
        rw [h_abort₁, wrle_eq_of_abort]
        simp only [fslMax, Sup.sup, fslMul, fslIverson, slExp, iteOneZero_pos h_e, fslFalse,
          mul_zero, fslNot, symm_one, zero_mul, ge_iff_le, le_refl, sup_of_le_left]
      case isFalse =>
        simp only [fslMax, Sup.sup, fslMul, fslIverson, slExp, iteOneZero_pos h_e, one_mul, fslNot,
          symm_one, zero_mul, ge_iff_le, zero_le, sup_of_le_left, le_refl]
    case neg h_e =>
      rw [step_condChoice_right _ _ (by simp only [h_e])]
      split
      case isTrue h_abort₂ =>
        rw [h_abort₂, wrle_eq_of_abort]
        simp only [fslMax, Sup.sup, fslMul, fslIverson, slExp, iteOneZero_neg h_e, fslFalse,
          mul_zero, fslNot, symm_one, zero_mul, ge_iff_le, le_refl, sup_of_le_left]
      case isFalse =>
        simp only [fslMax, Sup.sup, fslMul, fslIverson, slExp, iteOneZero_neg h_e, zero_mul, fslNot,
          symm_zero, one_mul, ge_iff_le, zero_le, sup_of_le_right, le_refl]


open SL OrdinalApprox in
theorem wrle_while {e : BoolExp Var}
    (h_Q : Q ⊢ `[fsl| wrle [c] ([[inv]] | [[resource]])])
    (h_inv : inv ⊢ `[fsl| ⁅<e>⁆ ⬝ [[Q]] ⊔ ~⁅<e>⁆ ⬝ [[P]]]) :
     inv ⊢ `[fsl| wrle [while e begin [[c]] fi] ([[P]] | [[resource]])] := by
  unfold wrle'
  rw [← gfpApprox_ord_eq_gfp]
  induction (Order.succ (Cardinal.mk _)).ord using Ordinal.induction with
  | h i ih =>
    intro s
    unfold gfpApprox
    apply le_sInf
    simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
      Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
      exists_exists_and_eq_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rintro _ (rfl | ⟨i', h_i', rfl⟩)
    · exact le_one'
    · simp only [wrleStepHom, wrleStep]
      apply le_sInf
      rintro _ ⟨heap', h_disjoint, rfl⟩
      cases eq_or_ne (resource ⟨s.stack, heap'⟩) 0 with
      | inl h_zero =>
        simp only [h_zero, unit_div_zero]
        exact le_one'
      | inr h_nonzero =>
        rw [unit_le_div_iff_mul_le]
        apply le_trans
        swap
        · apply step_framing
          simp only [wrtStmt, Set.empty_inter]
        · apply le_sSup_of_le
          · use s.heap, heap'
          · rw [← unit_le_div_iff_mul_le]
            rw [unitInterval.mul_div_cancel_of_pos h_nonzero]
            by_cases e s.stack
            case neg h =>
              rw [Bool.not_eq_true] at h
              rw [step_loop_term _ _ h]
              unfold gfpApprox
              apply le_sInf
              simp only [coe_mk, Set.mem_range, Subtype.exists, exists_prop, Set.union_singleton,
                Set.mem_insert_iff, Set.mem_setOf_eq, exists_eq_or_imp, Pi.top_apply,
                exists_exists_and_eq_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
              rintro _ (rfl | ⟨_, _, rfl⟩)
              · exact le_one'
              · apply le_trans (h_inv s)
                show `[fsl| ⁅<e>⁆ ⬝ [[Q]]] s ⊔ `[fsl|~⁅<e>⁆ ⬝ [[P]]] s ≤ _
                simp only [fslMul, fslIverson, slExp, h, Bool.false_eq_true, iteOneZero_false,
                  zero_mul, fslNot, symm_zero, one_mul, zero_le, sup_of_le_right, wrleStep, le_refl]
            case pos h =>
              rw [step_loop_cont _ _ h]
              apply le_trans ?_ (gfpApprox_wrleStep_seq s)
              apply le_trans
              swap
              · apply gfpApprox_le_gfpApprox_of_le (wrleStepHom inv resource)
                apply mk_le_mk.mpr
                apply wrleStep_mono_of_le_RV
                exact ih i' h_i'
              · apply le_trans (h_inv s)
                show `[fsl| ⁅<e>⁆ ⬝ [[Q]] ] s ⊔ `[fsl| ~⁅<e>⁆ ⬝ [[P]] ] s ≤ _
                simp only [fslMax, Sup.sup, fslMul, fslIverson, slExp, h, iteOneZero_true, one_mul,
                  fslNot, symm_one, zero_mul, zero_le, sup_of_le_left]
                apply le_trans (h_Q s)
                unfold wrle'
                apply le_gfpApprox_of_mem_fixedPoints (wrleStepHom _ _)
                · simp only [coe_mk, Function.mem_fixedPoints]
                  exact isFixedPt_gfp (wrleStepHom _ _)
                · exact le_top

end CFSL
