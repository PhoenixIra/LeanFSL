import InvLimDiss.Examples.ProducerConsumer.Basic
import InvLimDiss.Examples.ProducerConsumer.Producer
import InvLimDiss.Examples.ProducerConsumer.Channel
import InvLimDiss.Examples.ProducerConsumer.Consumer

open Syntax CFSL FSL SL

noncomputable def post_init (y : ℕ) (p : unitInterval) : StateRV String :=
  `[fsl|⁅is_in_ico "y1" (-1) y⁆
    ⋆ (⁅is_in_ico "y2" 0 y⁆ ⬝ <exp (constP p) (inc $ var "y2")>
      ⊔ ~⁅<leq (const 0) (var "y2")>⁆ ⊓ ⁅is_in_ico "y2" (-1) y⁆)
    ⋆ (⁅is_in_ico "y3" (-1) y⁆ ⊓ var "l" === sub (dec $ const y) (var "y3"))]

theorem init_sound (y : ℕ) (p : unitInterval) :
    ⊢ emp
    ⦃<exp (constP p) (const y)> ⋆ [[rInv y]]⦄
    init y
    ⦃ [[post_init y p]] ⋆ [[rInv y]]⦄ := by
  unfold init
  apply safeTuple_monotonicty
    `[fsl| ((((([[post_init y p]] ⋆ [[rInv y]])
          ("y3" ↦ (dec $ const y)))
          ("y2" ↦ (dec $ const y)))
          ("y1" ↦ (dec $ const y)))
          ("l" ↦ (const 0)))]
    _ ?_ le_rfl
  swap
  · simp only [fslSubst_of_fslSepMul]
    apply fslSepMul_mono
    · unfold post_init
      simp only [Int.reduceNeg, fslSubst_of_fslSepMul, fslSubst_of_fslIverson, ne_eq,
        String.reduceEq, not_false_eq_true, substProp_ico_neq, fslSubst_of_fslMax,
        fslSubst_of_fslMul, fslSubst_of_fslReal, substProp_of_exp, substProp_of_constP,
        substVal_of_inc, substVal_of_var_neq, fslSubst_of_fslMin, fslSubst_of_fslNot,
        substProp_of_slExp, substBool_of_leq, substVal_of_const, fslSubst_of_fslEquals,
        substVal_of_sub, substVal_of_dec, substVal_of_var, inc_dec_ident]
      nth_rw 1 [← fslReal_fslSepMul_fslTrue, fslSepMul_comm]
      apply fslSepMul_mono
      · rw [substProp_ico_eq_dec_upper "y1" (-1 : ℤ) y]
        · intro s
          simp only [fslTrue, fslIverson, substProp, slTrue, unitInterval.iteOneZero_true, le_refl]
        · exact neg_one_le_nat y
      · nth_rw 1 [← fslReal_fslSepMul_fslTrue]
        apply fslSepMul_mono
        · apply le_fslMax
          cases y
          case zero =>
            right
            rw [entailment_iff_pi_le, le_fslMin_iff]
            apply And.intro
            · intro s
              simp only [CharP.cast_eq_zero, fslNot, fslIverson, unitInterval.sym_iteOneZero_eq]
              rw [unitInterval.iteOneZero_pos]
              · exact unitInterval.le_one'
              · simp only [slExp, leq, const, dec, zero_sub, Left.nonneg_neg_iff,
                decide_eq_true_eq, not_le, zero_lt_one]
            · rw [substProp_ico_eq_dec_upper "y2" (-1 : ℤ) 0]
              · intro s
                simp only [CharP.cast_eq_zero, fslIverson, substProp, slTrue,
                  unitInterval.iteOneZero_pos]
                exact unitInterval.le_one'
              · exact neg_one_le_nat 0
          case succ y =>
            left
            rw [← fslReal_fslMul_fslTrue, fslMul_comm]
            apply fslMul_mono
            · rw [substProp_ico_eq_dec_upper "y2" (0 : ℤ) (y+1)]
              · intro s
                simp only [fslTrue, fslIverson, substProp, slTrue, unitInterval.iteOneZero_pos,
                  le_refl]
              · exact Int.ofNat_succ_pos y
            · intro s
              simp only [fslReal, Nat.cast_add, Nat.cast_one, fslMul, fslTrue, one_mul, le_refl]
        · rw [entailment_iff_pi_le, le_fslMin_iff]
          apply And.intro
          · rw [substProp_ico_eq_dec_upper "y3" (-1 : ℤ) y]
            intro s
            simp only [fslIverson, substProp, slTrue, unitInterval.iteOneZero_true]
            · exact unitInterval.le_one'
            · exact neg_one_le_nat y
          · intro s
            simp only [fslEquals, const, sub, dec, sub_self, unitInterval.iteOneZero_true]
            exact unitInterval.le_one'
    · unfold rInv rInv1 rInv2
      simp only [fslSubst_of_fslSepMul, fslSubst_of_fslBigSepMul, fslSubst_of_fslMax,
        fslSubst_of_fslPointsTo, substVal_of_add, ne_eq, String.reduceEq, not_false_eq_true,
        substVal_of_var_neq, substVal_of_const]
      exact le_rfl
  · apply safeTuple_seq
    · apply safeTuple_assign
      simp only [varRV_of_fslEmp, Set.mem_empty_iff_false, not_false_eq_true]
    apply safeTuple_seq
    · apply safeTuple_assign
      simp only [varRV_of_fslEmp, Set.mem_empty_iff_false, not_false_eq_true]
    apply safeTuple_seq
    · apply safeTuple_assign
      simp only [varRV_of_fslEmp, Set.mem_empty_iff_false, not_false_eq_true]
    apply safeTuple_assign
    simp only [varRV_of_fslEmp, Set.mem_empty_iff_false, not_false_eq_true]

theorem var_disjoint₁ (y : ℕ) (p : unitInterval) :
    wrtProg producer ∩
      (varProg (channel p) ∪ varProg consumer ∪ varRV `[fsl| fTrue ]
      ∪ varRV `[fsl| var "l" === const ↑y ] ∪ varRV (rInv y))
    = ∅ := by
  sorry

theorem var_disjoint₂ (y : ℕ) (p : unitInterval) :
    wrtProg (channel p) ∩
      (varProg producer ∪ varProg consumer ∪ varRV `[fsl| fTrue ]
      ∪ varRV `[fsl| var "l" === const ↑y ] ∪ varRV (rInv y))
    = ∅ := sorry

theorem var_disjoint₃ (y : ℕ) (p : unitInterval) :
    wrtProg consumer ∩
      (varProg producer ∪ varProg (channel p) ∪ varRV `[fsl| fTrue ]
      ∪ varRV `[fsl| fTrue ] ∪ varRV (rInv y))
    = ∅ := sorry

theorem producerConsumer_sound (y : ℕ) (p : unitInterval) :
    ⊢ emp
    ⦃<exp (constP p) (const y)> ⋆ [[rInv y]]⦄
    producerConsumer y p
    ⦃var "l" === const y ⋆ [[rInv y]]⦄ := by
  unfold producerConsumer
  apply safeTuple_seq _ (init_sound y p)
  apply safeTuple_share
  rw [fslSepMul_comm, fslSepMul_fslEmp_eq]
  rw [← fslTrue_fslSepMul_fslEquals, ← fslTrue_fslSepMul_fslEquals]
  apply safeTuple_concur₃ (var_disjoint₁ y p) (var_disjoint₂ y p) (var_disjoint₃ y p)
  · exact producer_sound y
  · exact channel_sound y p
  · exact consumer_sound y
