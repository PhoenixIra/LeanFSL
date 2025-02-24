import InvLimDiss.CFSL
import InvLimDiss.Examples.SyntaxHelp
import InvLimDiss.SL.Framing.VarApprox

open Syntax

noncomputable def sendDataProg : Program String :=
    [Prog| var "r" *≔ const (-1:ℚ) ;
       (pif half then var "r" *≔ const 0 else var "r" *≔ const 1 fi)
    || ("y" ≔* var "r" ; while eq (var "r") (const (-1:ℚ)) begin "y" ≔* var "r" fi)]

open CFSL FSL

theorem sendData_prequel_proof :
     ⊢ emp ⦃ S q. var "r" ↦ fun _ ↦ q ⦄ var "r" *≔ const (-1) ⦃ var "r" ↦ const (-1) ⦄ := by
  apply safeTuple_monotonicty
    `[fsl| (S (q : ℚ). var "r" ↦ q)
        ⋆ (var "r" ↦ const (-1) -⋆ var "r" ↦ const (-1)) ]
    _
  · nth_rw 1 [← fslSepMul_fslEmp_eq `[fsl| S q. var "r" ↦ (fun _ => q) ] ]
    apply fslSepMul_mono le_rfl
    rw [entail_iff_le, le_fslSepDiv_iff_fslSepMul_le]
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
    ⦃ <one> ⦄ := by
  apply safeTuple_monotonicty
    `[fsl| <half> ⬝ <one> + ~<half> ⬝ fFalse]
    _
  · intro s
    simp only [fslReal, half, one_div, fslAdd, fslMul, one, mul_one, fslFalse, mul_zero, add_zero,
      le_refl]
  · exact le_rfl
  apply safeTuple_probabilisticBranching
  · apply safeTuple_atom
    · apply safeTuple_monotonicty
       `[fsl| (S (q : ℚ). var "r" ↦ q)
        ⋆ (var "r" ↦ const 0 -⋆ <one> ⋆ ((var "r" ↦ const 0) ⊔ (var "r" ↦ const (-1))))]
        _
      · rw [fslSepMul_comm]
        apply fslSepMul_mono
        · rw [entail_iff_le, fslMax_le_iff]
          apply And.intro
          · apply le_fslSup _ _ 0
            unfold const
            exact le_rfl
          · apply le_fslSup _ _ (-1)
            unfold const
            exact le_rfl
        · rw [entail_iff_le, le_fslSepDiv_iff_fslSepMul_le]
          rw [fslSepMul_comm]
          apply fslSepMul_mono
          · apply le_fslMax
            left
            exact le_rfl
          · exact le_rfl
      · exact le_rfl
      apply safeTuple_mutate
    · simp only [Atom.atomicProgram]

theorem sendData_right_proof :
    ⊢ (var "r" ↦ const 0) ⊔ (var "r" ↦ const (-1))
    ⦃ fTrue ⦄
    "y" ≔* var "r" ; while eq (var "r") (const (-1)) begin "y" ≔* var "r" fi
    ⦃ var "y" = const 0 ⦄ := by
  sorry

theorem sendData_proof :
    ⊢ emp
    ⦃ <half> ⋆ S q. (var "r") ↦ (fun _ => q) ⦄
    sendDataProg
    ⦃ <one> ⋆ (var "y") = (const 0) ⋆ ((var "r" ↦ const 0) ⊔ (var "r") ↦ (const (-1:ℚ))) ⦄ := by
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
