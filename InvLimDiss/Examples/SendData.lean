import InvLimDiss.CFSL
import InvLimDiss.Examples.SyntaxHelp
import InvLimDiss.SL.Framing.VarApprox

open Syntax

noncomputable def sendDataProg : Program String :=
    [Prog| var "r" *≔ const (-1:ℚ) ;
       (pif half then var "r" *≔ const 0 else var "r" *≔ const 1 fi)
    || ("y" ≔* var "r" ; while eq (var "y") (const (-1:ℚ)) begin "y" ≔* var "r" fi)]

open CFSL FSL

theorem sendData_prequel_proof :
     ⊢ emp ⦃ S q. var "r" ↦ fun _ ↦ q ⦄ var "r" *≔ const (-1) ⦃ var "r" ↦ const (-1) ⦄ := by
  apply safeTuple_monotonicty
    `[fsl| (S (q : ℚ). var "r" ↦ q)
        ⋆ (var "r" ↦ const (-1) -⋆ var "r" ↦ const (-1)) ]
    _
  · nth_rw 1 [← fslSepMul_fslEmp_eq `[fsl| S q. var "r" ↦ (fun _ => q) ] ]
    apply fslSepMul_mono le_rfl
    rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
    rw [fslSepMul_comm, fslSepMul_fslEmp_eq]
  · exact le_rfl
  · exact safeTuple_mutate `[fsl| var "r" ↦ const (-1) ]

theorem no_shared_stack_vars :
    wrtProg ([Prog| "y" ≔* var "r" ; while eq (var "r") (const (-1)) begin "y" ≔* var "r" fi ]) ∩
      (varProg ([Prog| pif half then var "r" *≔ const 0 else var "r" *≔ const 1 fi ]) ∪ varRV `[fsl| <one> ] ∪
        varRV `[fsl| (var "r" ↦ const 0) ⊔ (var "r" ↦ const (-1)) ]) = ∅ := by
  simp only [wrtProg, Set.union_self, Set.singleton_inter_eq_empty, Set.mem_union, not_or]
  simp only [varProg, Set.mem_union, not_or]
  apply And.intro; swap
  · apply Set.not_mem_subset varRV_of_fslMax
    simp only [Set.mem_union, not_or]
    apply And.intro
    · apply Set.not_mem_subset varRV_of_fslPointsTo
      rw [varValue_of_var, varValue_of_const]
      simp only [Set.union_empty, Set.mem_singleton_iff, String.reduceEq, not_false_eq_true]
    · apply Set.not_mem_subset varRV_of_fslPointsTo
      rw [varValue_of_var, varValue_of_const]
      simp only [Set.union_empty, Set.mem_singleton_iff, String.reduceEq, not_false_eq_true]
  apply And.intro; swap
  · rw [varRV_of_fslReal]
    rw [varProb_of_one]
    simp only [Set.mem_empty_iff_false, not_false_eq_true]
  apply And.intro; swap
  apply And.intro
  · simp only [varValue_of_var, Set.mem_singleton_iff, String.reduceEq, not_false_eq_true]
  · simp only [varValue_of_const, Set.mem_empty_iff_false, not_false_eq_true]
  apply And.intro
  · simp only [varProb_of_half, Set.mem_empty_iff_false, not_false_eq_true]
  apply And.intro
  · simp only [varValue_of_var, Set.mem_singleton_iff, String.reduceEq, not_false_eq_true]
  · simp only [varValue_of_const, Set.mem_empty_iff_false, not_false_eq_true]

theorem sendData_left_proof :
    ⊢ (var "r" ↦ const 0) ⊔ (var "r" ↦ const (-1))
    ⦃ <half> ⦄
    pif half then var "r" *≔ const 0 else var "r" *≔ const 1 fi
    ⦃ fTrue ⦄ := by
  apply safeTuple_monotonicty
    `[fsl| <half> ⬝ fTrue + ~<half> ⬝ fFalse]
    _
  · intro s
    simp only [fslReal, half, one_div, fslAdd, fslMul, one, mul_one, fslFalse, mul_zero, add_zero,
      le_refl, fslTrue]
  · exact le_rfl
  apply safeTuple_probabilisticBranching
  · apply safeTuple_atom
    · apply safeTuple_monotonicty
       `[fsl| (S (q : ℚ). var "r" ↦ q)
        ⋆ (var "r" ↦ const 0 -⋆ fTrue ⋆ ((var "r" ↦ const 0) ⊔ (var "r" ↦ const (-1))))]
        _
      · rw [fslSepMul_comm]
        apply fslSepMul_mono
        · rw [entailment_iff_pi_le, fslMax_le_iff]
          apply And.intro
          · apply le_fslSup _ _ 0
            unfold const
            exact le_rfl
          · apply le_fslSup _ _ (-1)
            unfold const
            exact le_rfl
        · rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
          rw [fslSepMul_comm]
          apply fslSepMul_mono
          · apply le_fslMax
            left
            exact le_rfl
          · exact le_rfl
      · exact le_rfl
      apply safeTuple_mutate
    · simp only [Atom.atomicProgram]
  · apply safeTuple_monotonicty
      `[fsl| (S (q : ℚ). var "r" ↦ q) ⋆ (var "r" ↦ const 1 -⋆ fTrue)]
      `[fsl| fTrue]
    · exact fslFalse_le _
    · exact le_rfl
    apply safeTuple_mutate

theorem sendData_right_first_proof :
  ⊢ (var "r" ↦ const 0) ⊔ (var "r" ↦ const (-1))
    ⦃ fTrue ⦄
    "y" ≔* var "r"
    ⦃((var "y") === (const 0)) ⊔ ((var "y") === (const (-1)))⦄ := by
  apply safeTuple_atom
  · apply safeTuple_monotonicty
      `[fsl|S (q : ℚ). var "r" ↦ q ⋆ (var "r" ↦ q -⋆
          (((var "y" === const 0) ⊔ var "y" === const (-1))
          ⋆ ((var "r" ↦ const 0) ⊔ var "r" ↦ const (-1)))("y" ↦ q))]
        _
    · rw [fslSepMul_fslMax_distr, entailment_iff_pi_le, fslMax_le_iff]
      apply And.intro
      · apply le_fslSup _ _ 0
        rw [fslSepMul_comm]
        apply fslSepMul_mono le_rfl
        rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
        simp only [fslSubst_of_fslMax, fslSubst_of_fslEquals, fslSubst_of_fslSepMul,
          fslSubst_of_fslPointsTo]
        rw [substVal_of_var, substVal_of_const, substVal_of_const, substVal_of_var_neq (ne_of_beq_false rfl)]
        apply fslSepMul_mono
        · unfold const
          rw [fslEquals_rfl, fslMax_fslTrue]
          exact le_rfl
        · apply le_fslMax
          left
          exact le_rfl
      · apply le_fslSup _ _ (-1)
        rw [fslSepMul_comm]
        apply fslSepMul_mono le_rfl
        rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
        simp only [fslSubst_of_fslMax, fslSubst_of_fslEquals, fslSubst_of_fslSepMul,
          fslSubst_of_fslPointsTo]
        rw [substVal_of_var, substVal_of_const, substVal_of_const, substVal_of_var_neq (ne_of_beq_false rfl)]
        apply fslSepMul_mono
        · apply le_fslMax
          right
          unfold const
          rw [fslEquals_rfl]
          exact le_rfl
        · apply le_fslMax
          right
          unfold const
          exact le_rfl
    · exact le_rfl
    · apply safeTuple_lookup
      rw [varRV_of_fslEmp]
      trivial
  · simp only [Atom.atomicProgram]

theorem sendData_right_loop_body_proof :
    ⊢ (var "r" ↦ const 0) ⊔ (var "r" ↦ const (-1))
    ⦃ (var "y" === const 0) ⊔ var "y" === const (-1) ⦄
    "y" ≔* var "r"
    ⦃(var "y" === const 0) ⊔ var "y" === const (-1) ⦄ := by
  apply safeTuple_atom
  · apply safeTuple_monotonicty
      `[fsl|S (q : ℚ). var "r" ↦ q ⋆ (var "r" ↦ q -⋆
          (((var "y" === const 0) ⊔ var "y" === const (-1))
          ⋆ ((var "r" ↦ const 0) ⊔ var "r" ↦ const (-1)))("y" ↦ q))]
        _
    · rw [fslSepMul_fslMax_distr, entailment_iff_pi_le, fslMax_le_iff]
      apply And.intro
      · apply le_fslSup _ _ (0:ℚ)
        rw [fslSepMul_comm]
        apply fslSepMul_mono le_rfl
        rw [entailment_iff_pi_le, fslMax_le_iff]
        apply And.intro
        repeat {
          rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
          rw [fslSepMul_comm]
          simp only [fslSubst_of_fslMax, fslSubst_of_fslSepMul, fslSubst_of_fslPointsTo,
            fslSubst_of_fslEquals]
          rw [substVal_of_var, substVal_of_const, substVal_of_const, substVal_of_var_neq (ne_of_beq_false rfl)]
          unfold const
          apply le_fslMax
          left
          apply fslSepMul_mono le_rfl
          apply le_fslMax
          left
          rw [fslEquals_rfl]
          exact le_fslTrue _
        }
      · apply le_fslSup _ _ (-1:ℚ)
        rw [fslSepMul_comm]
        apply fslSepMul_mono le_rfl
        rw [entailment_iff_pi_le, fslMax_le_iff]
        apply And.intro
        repeat {
          rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
          rw [fslSepMul_comm]
          simp only [fslSubst_of_fslMax, fslSubst_of_fslSepMul, fslSubst_of_fslPointsTo,
            fslSubst_of_fslEquals]
          rw [substVal_of_var, substVal_of_const, substVal_of_const, substVal_of_var_neq (ne_of_beq_false rfl)]
          unfold const
          apply le_fslMax
          right
          apply fslSepMul_mono le_rfl
          apply le_fslMax
          right
          rw [fslEquals_rfl]
          exact le_fslTrue _
        }
    · exact le_rfl
    · apply safeTuple_lookup
      rw [varRV_of_fslEmp]
      trivial
  · simp only [Atom.atomicProgram]

theorem sendData_right_proof :
    ⊢ (var "r" ↦ const 0) ⊔ (var "r" ↦ const (-1))
    ⦃ fTrue ⦄
    "y" ≔* var "r" ; while eq (var "y") (const (-1)) begin "y" ≔* var "r" fi
    ⦃ (var "y") === (const 0) ⦄ := by
  apply safeTuple_seq `[fsl| ((var "y") === (const 0)) ⊔ ((var "y") === (const (-1)))]
  · exact sendData_right_first_proof
  · apply safeTuple_while `[fsl| ((var "y") === (const 0)) ⊔ ((var "y") === (const (-1)))]
    · apply sendData_right_loop_body_proof
    · rw [entailment_iff_pi_le, fslMax_le_iff]
      apply And.intro
      · apply le_fslMax
        right
        intro s
        unfold fslEquals fslNot fslIverson eq var const fslMul SL.slExp
        open unitInterval in {
          simp only [decide_eq_true_eq, sym_iteOneZero_eq, iteOneZero_le]
          intro h
          rw [iteOneZero_pos h, iteOneZero_pos, mul_one]
          intro h'
          simp only [h, zero_eq_neg, one_ne_zero] at h'
        }
      · apply le_fslMax
        left
        intro s
        unfold fslEquals fslMul fslIverson fslMax SL.slExp var const eq
        simp only [decide_eq_true_eq]
        open unitInterval in {
          rw [iteOneZero_le]
          intro h
          rw [iteOneZero_pos h, one_mul]
          apply le_sup_of_le_right
          simp only
          rw [iteOneZero_pos h]
        }

theorem sendData_proof :
    ⊢ emp
    ⦃ <half> ⋆ S q. (var "r") ↦ (fun _ => q) ⦄
    sendDataProg
    ⦃ fTrue ⋆ (var "y") === (const 0) ⋆ ((var "r" ↦ const 0) ⊔ (var "r") ↦ (const (-1:ℚ))) ⦄ := by
  unfold sendDataProg
  apply safeTuple_seq `[fsl| <half> ⋆ (var "r") ↦ (const (-1:ℚ))]
  · rw [fslSepMul_comm]; nth_rw 2 [fslSepMul_comm]
    apply safeTuple_frame
    · simp only [wrtProg, Set.empty_inter]
    · exact sendData_prequel_proof
  apply safeTuple_monotonicty
    `[fsl| <half> ⋆ ((var "r" ↦ const 0) ⊔ (var "r") ↦ (const (-1:ℚ)))]
    _
  · apply fslSepMul_mono le_rfl
    apply le_fslMax
    right
    exact le_rfl
  · exact le_rfl
  rw [fslSepMul_assoc]
  apply safeTuple_share
  rw [fslSepMul_comm, fslSepMul_fslEmp_eq]
  rw [← fslReal_fslSepMul_fslTrue half]
  apply safeTuple_concur
  · simp only [wrtProg, Set.union_self, Set.empty_inter]
  · exact no_shared_stack_vars
  · exact sendData_left_proof
  · exact sendData_right_proof
