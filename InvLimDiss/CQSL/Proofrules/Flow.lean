import InvLimDiss.CQSL.WeakExpectation
import InvLimDiss.SL.Framing.Simps
import InvLimDiss.SL.Classical
import InvLimDiss.CQSL.Step.Framing

/-!
  Proofrules for wrle with flow programs that are not inductive (i.e. looping, choices) as one should use it for reasoning about concurrent probabilistic programs.
-/

namespace CQSL

open QSL Syntax OrderHom unitInterval Atom Semantics

theorem wrle_probabilisticBranching :
    `[qsl| <e> ⬝ wrle [c₁] ([[P]] | [[resource]])
        + ~<e> ⬝ wrle [c₂] ([[P]] | [[resource]])
        ⊢ wrle [pif e then [[c₁]] else [[c₂]] fi] ([[P]] | [[resource]])] := by
  nth_rw 3 [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_qslSepDiv_iff_qslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [wrtStmt, Set.empty_inter]
  · refine qslSepMul_mono ?_ le_rfl
    intro s
    rw [step_probChoice]
    split_ifs
    case pos h_abort₁ h_abort₂ =>
      rw [h_abort₁, h_abort₂, wrle_eq_of_abort]
      simp only [qslAdd, qslMul, qslReal, qslFalse, mul_zero, qslNot, truncatedAdd_zero, add_zero,
        le_refl]
    case neg h_abort₁ _ =>
      rw [h_abort₁, wrle_eq_of_abort]
      simp only [qslAdd, qslMul, qslReal, qslFalse, mul_zero, qslNot, zero_truncatedAdd, zero_add,
        le_refl]
    case pos h_abort₂ =>
      rw [h_abort₂, wrle_eq_of_abort]
      simp only [qslAdd, qslMul, qslReal, qslFalse, mul_zero, truncatedAdd_zero, add_zero, le_refl]
    case neg =>
      simp only [qslAdd, qslMul, qslReal, qslNot]
      rfl

open SL in
theorem wrle_conditionalBranching {e : BoolExp Var} :
    `[qsl| ⁅<e>⁆ ⬝ wrle [c₁] ([[P]] | [[resource]])
        ⊔ ~⁅<e>⁆ ⬝ wrle [c₂] ([[P]] | [[resource]])
        ⊢ wrle [if e then [[c₁]] else [[c₂]] fi] ([[P]] | [[resource]])] := by
  nth_rw 3 [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [le_qslSepDiv_iff_qslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [wrtStmt, Set.empty_inter]
  · refine qslSepMul_mono ?_ le_rfl
    intro s
    by_cases e s.stack
    case pos h_e =>
      rw [step_condChoice_left _ _ h_e]
      split
      case isTrue h_abort₁ =>
        rw [h_abort₁, wrle_eq_of_abort]
        simp only [qslMax, Sup.sup, qslMul, qslIverson, slExp, iteOneZero_pos h_e, qslFalse,
          mul_zero, qslNot, symm_one, zero_mul, ge_iff_le, le_refl, sup_of_le_left]
      case isFalse =>
        simp only [qslMax, Sup.sup, qslMul, qslIverson, slExp, iteOneZero_pos h_e, one_mul, qslNot,
          symm_one, zero_mul, ge_iff_le, zero_le, sup_of_le_left, le_refl]
    case neg h_e =>
      rw [step_condChoice_right _ _ (by simp only [h_e])]
      split
      case isTrue h_abort₂ =>
        rw [h_abort₂, wrle_eq_of_abort]
        simp only [qslMax, Sup.sup, qslMul, qslIverson, slExp, iteOneZero_neg h_e, qslFalse,
          mul_zero, qslNot, symm_one, zero_mul, ge_iff_le, le_refl, sup_of_le_left]
      case isFalse =>
        simp only [qslMax, Sup.sup, qslMul, qslIverson, slExp, iteOneZero_neg h_e, zero_mul, qslNot,
          symm_zero, one_mul, ge_iff_le, zero_le, sup_of_le_right, le_refl]


open SL in
theorem wrle_while {e : BoolExp Var}
    (h_Q : Q ⊢ `[qsl| wrle [c] ([[inv]] | [[resource]])])
    (h_inv : inv ⊢ `[qsl| ⁅<e>⁆ ⬝ [[Q]] ⊔ ~⁅<e>⁆ ⬝ [[P]]]) :
     inv ⊢ `[qsl| wrle [while e begin [[c]] fi] ([[P]] | [[resource]])] := by
  rw [wrle_eq_of_not_final (by simp [finalProgram])]
  rw [entailment_iff_pi_le, le_qslSepDiv_iff_qslSepMul_le]
  apply le_trans
  pick_goal 2
  · apply step_framing
    simp only [wrtStmt, Set.empty_inter]
  · refine qslSepMul_mono ?_ le_rfl
    sorry
    -- here are ordinal induction and preferably also sequential required

end CQSL
