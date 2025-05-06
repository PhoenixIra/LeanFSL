import LeanFSL.Examples.ProducerConsumer.Basic

open Syntax CFSL FSL SL

theorem consumer_sound₁ (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃ ⁅is_in_ico "y3" 0 ↑y⁆ ⊓ var "l" === sub (dec (const ↑y)) (var "y3") ⦄
    "x3" ≔* add (var "z2") (var "y3")
    ⦃ ⁅is_in_ico "y3" 0 ↑y⁆ ⊓ (var "l" === sub (dec (const ↑y)) (var "y3"))
      ⊓ ((var "x3" === const 0) ⊔ (var "x3" === const 1) ⊔ var "x3" === const 2) ⦄ := by
  apply safeTuple_atom
  · simp only [Atom.atomicProgram]
  apply safeTuple_monotonicty
    `[fsl| S (q : ℚ). add (var "z2") (var "y3") ↦ q ⋆ (add (var "z2") (var "y3") ↦ q
        -⋆ (((⁅is_in_ico "y3" 0 ↑y⁆ ⊓ (var "l" === sub (dec (const ↑y)) (var "y3"))
        ⊓ ((var "x3" === const 0) ⊔ (var "x3" === const 1) ⊔ var "x3" === const 2))
        ⋆ [[rInv y]])("x3" ↦ q)))]
    _ ?_ le_rfl
  swap
  · rw [rInv]
    rw [fslIverson_fslMin_eq_fslIverson_fslMul]
    rw [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
    nth_rw 3 [fslSepMul_comm]
    rw [← fslSepMul_assoc]; nth_rw 2 [fslSepMul_assoc]; nth_rw 3 [fslSepMul_comm]
    rw [← fslSepMul_assoc]; nth_rw 1 [fslSepMul_assoc]
    rw [← fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
    rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
    rw [rInv2, ico_fslBigSepMul, ← rInv2_wo]
    rw [fslIverson_fslMin_eq_fslIverson_fslMul]
    rw [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
    rw [fslSup_fslSepMul_distr, fslSepMul_fslSup_distr, fslSup_fslSepMul_distr]
    apply fslSup_le
    intro i
    nth_rw 2 [fslMin_comm]
    rw [fslMin_fslMax_right, fslMin_fslMax_right]
    simp only [fslMax_fslSepMul_distr, fslSepMul_fslMax_distr]
    rw [entailment_iff_pi_le, fslMax_le_iff]
    apply And.intro
    · apply le_fslSup _ _ 0
      nth_rw 2 [fslSepMul_assoc]
      nth_rw 3 [fslSepMul_comm]
      simp only [← fslSepMul_assoc]
      rw [← fslMin_self (`[fsl| var "y3" === const i]), ← fslMin_assoc]
      rw [fslMin_comm, conservative_equals, fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [fslMul_eq_emp_fslSepMul_of_pure pure_fslIverson_slEquals]
      nth_rw 2 [fslSepMul_comm]
      simp only [← fslSepMul_assoc]
      apply fslSepMul_mono
      · rw [conservative_pointsTo, conservative_min, conservative_pointsTo]
        rw [conservative_entail]
        intro s
        rw [slAnd, Pi.inf_apply]
        simp only [slPointsTo, slEquals, add, var, const, le_Prop_eq]
        intro ⟨⟨l, h_l, h_heap⟩, h_eq⟩
        use l
        apply And.intro ?_ h_heap
        rw [h_l, h_eq]
      · rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
        simp only [fslSubst_of_fslSepMul, fslSubst_of_fslMin, fslSubst_of_fslIverson, ne_eq,
          String.reduceEq, not_false_eq_true, substProp_ico_neq, fslSubst_of_fslEquals,
          substVal_of_var_neq, substVal_of_sub, substVal_of_dec, substVal_of_const,
          fslSubst_of_fslMax, substVal_of_var, fslSubst_of_fslBigSepMul, fslSubst_of_fslPointsTo,
          substVal_of_add]
        nth_rw 3 [fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
        simp only [← fslSepMul_assoc]
        nth_rw 8 [fslSepMul_comm]
        nth_rw 6 [fslSepMul_assoc]
        nth_rw 8 [fslSepMul_comm]
        simp only [← fslSepMul_assoc]
        nth_rw 5 [fslSepMul_assoc]
        nth_rw 2 [← fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
        nth_rw 1 [← fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [ico_fslBigSepMul, ← rInv2_wo]
        nth_rw 3 [fslIverson_fslMin_eq_fslIverson_fslMul]
        nth_rw 1 [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
        nth_rw 8 [fslSepMul_comm]
        nth_rw 1 [fslSepMul_comm]
        simp only [← fslSepMul_assoc]
        apply fslSepMul_mono le_rfl (fslSepMul_mono le_rfl ?_)
        rw [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]; rw[← fslSepMul_assoc]
        nth_rw 5 [fslSepMul_comm]
        nth_rw 3 [fslSepMul_assoc]
        nth_rw 5 [fslSepMul_comm]
        simp only [← fslSepMul_assoc]
        apply fslSepMul_mono
        · simp only [rInv1, fslSubst_of_fslBigSepMul, fslSubst_of_fslMax, fslSubst_of_fslPointsTo,
            substVal_of_add, ne_eq, String.reduceEq, not_false_eq_true, substVal_of_var_neq,
            substVal_of_const]
          exact le_rfl
        rw [fslSepMul_comm]
        apply fslSepMul_mono
        · rw [← fslMul_eq_fslSepMul_emp_of_pure pure_fslIverson_slEquals]
          apply le_fslSup _ _ i
          simp only [conservative_pointsTo, conservative_mul, conservative_equals, conservative_max,
            conservative_min]
          rw [conservative_entail]
          intro s ⟨h_pt, h_eq⟩
          apply And.intro
          · exact h_eq
          · left
            simp only [slPointsTo, add, var, const]
            simp only [slPointsTo, add, var, const] at h_pt
            simp only [slEquals, var, const] at h_eq
            obtain ⟨l, h_l, h_heap⟩ := h_pt
            use l
            apply And.intro ?_ h_heap
            rw [h_l, h_eq]
        · simp only [conservative_equals, conservative_max, conservative_min]
          rw [conservative_entail]
          intro s h
          apply And.intro h
          left
          simp only [slEquals, const]
    · rw [entailment_iff_pi_le, fslMax_le_iff]
      apply And.intro
      · apply le_fslSup _ _ 1
        nth_rw 2 [fslSepMul_assoc]
        nth_rw 3 [fslSepMul_comm]
        simp only [← fslSepMul_assoc]
        rw [← fslMin_self (`[fsl| var "y3" === const i]), ← fslMin_assoc]
        rw [fslMin_comm, conservative_equals, fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [fslMul_eq_emp_fslSepMul_of_pure pure_fslIverson_slEquals]
        nth_rw 2 [fslSepMul_comm]
        simp only [← fslSepMul_assoc]
        apply fslSepMul_mono
        · rw [conservative_pointsTo, conservative_min, conservative_pointsTo]
          rw [conservative_entail]
          intro s
          rw [slAnd, Pi.inf_apply]
          simp only [slPointsTo, slEquals, add, var, const, le_Prop_eq]
          intro ⟨⟨l, h_l, h_heap⟩, h_eq⟩
          use l
          apply And.intro ?_ h_heap
          rw [h_l, h_eq]
        · rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
          simp only [fslSubst_of_fslSepMul, fslSubst_of_fslMin, fslSubst_of_fslIverson, ne_eq,
            String.reduceEq, not_false_eq_true, substProp_ico_neq, fslSubst_of_fslEquals,
            substVal_of_var_neq, substVal_of_sub, substVal_of_dec, substVal_of_const,
            fslSubst_of_fslMax, substVal_of_var, fslSubst_of_fslBigSepMul, fslSubst_of_fslPointsTo,
            substVal_of_add]
          nth_rw 3 [fslIverson_fslMin_eq_fslIverson_fslMul]
          rw [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
          simp only [← fslSepMul_assoc]
          nth_rw 8 [fslSepMul_comm]
          nth_rw 6 [fslSepMul_assoc]
          nth_rw 8 [fslSepMul_comm]
          simp only [← fslSepMul_assoc]
          nth_rw 5 [fslSepMul_assoc]
          nth_rw 2 [← fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
          nth_rw 1 [← fslIverson_fslMin_eq_fslIverson_fslMul]
          rw [ico_fslBigSepMul, ← rInv2_wo]
          nth_rw 3 [fslIverson_fslMin_eq_fslIverson_fslMul]
          nth_rw 1 [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
          nth_rw 8 [fslSepMul_comm]
          nth_rw 1 [fslSepMul_comm]
          simp only [← fslSepMul_assoc]
          apply fslSepMul_mono le_rfl (fslSepMul_mono le_rfl ?_)
          rw [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]; rw[← fslSepMul_assoc]
          nth_rw 5 [fslSepMul_comm]
          nth_rw 3 [fslSepMul_assoc]
          nth_rw 5 [fslSepMul_comm]
          simp only [← fslSepMul_assoc]
          apply fslSepMul_mono
          · simp only [rInv1, fslSubst_of_fslBigSepMul, fslSubst_of_fslMax, fslSubst_of_fslPointsTo,
              substVal_of_add, ne_eq, String.reduceEq, not_false_eq_true, substVal_of_var_neq,
              substVal_of_const]
            exact le_rfl
          rw [fslSepMul_comm]
          apply fslSepMul_mono
          · rw [← fslMul_eq_fslSepMul_emp_of_pure pure_fslIverson_slEquals]
            apply le_fslSup _ _ i
            simp only [conservative_pointsTo, conservative_mul, conservative_equals, conservative_max,
              conservative_min]
            rw [conservative_entail]
            intro s ⟨h_pt, h_eq⟩
            apply And.intro
            · exact h_eq
            · right; left
              simp only [slPointsTo, add, var, const]
              simp only [slPointsTo, add, var, const] at h_pt
              simp only [slEquals, var, const] at h_eq
              obtain ⟨l, h_l, h_heap⟩ := h_pt
              use l
              apply And.intro ?_ h_heap
              rw [h_l, h_eq]
          · simp only [conservative_equals, conservative_max, conservative_min]
            rw [conservative_entail]
            intro s h
            apply And.intro h
            right; left
            simp only [slEquals, const]
      · apply le_fslSup _ _ 2
        nth_rw 2 [fslSepMul_assoc]
        nth_rw 3 [fslSepMul_comm]
        simp only [← fslSepMul_assoc]
        rw [← fslMin_self (`[fsl| var "y3" === const i]), ← fslMin_assoc]
        rw [fslMin_comm, conservative_equals, fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [fslMul_eq_emp_fslSepMul_of_pure pure_fslIverson_slEquals]
        nth_rw 2 [fslSepMul_comm]
        simp only [← fslSepMul_assoc]
        apply fslSepMul_mono
        · rw [conservative_pointsTo, conservative_min, conservative_pointsTo]
          rw [conservative_entail]
          intro s
          rw [slAnd, Pi.inf_apply]
          simp only [slPointsTo, slEquals, add, var, const, le_Prop_eq]
          intro ⟨⟨l, h_l, h_heap⟩, h_eq⟩
          use l
          apply And.intro ?_ h_heap
          rw [h_l, h_eq]
        · rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
          simp only [fslSubst_of_fslSepMul, fslSubst_of_fslMin, fslSubst_of_fslIverson, ne_eq,
            String.reduceEq, not_false_eq_true, substProp_ico_neq, fslSubst_of_fslEquals,
            substVal_of_var_neq, substVal_of_sub, substVal_of_dec, substVal_of_const,
            fslSubst_of_fslMax, substVal_of_var, fslSubst_of_fslBigSepMul, fslSubst_of_fslPointsTo,
            substVal_of_add]
          nth_rw 3 [fslIverson_fslMin_eq_fslIverson_fslMul]
          rw [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
          simp only [← fslSepMul_assoc]
          nth_rw 8 [fslSepMul_comm]
          nth_rw 6 [fslSepMul_assoc]
          nth_rw 8 [fslSepMul_comm]
          simp only [← fslSepMul_assoc]
          nth_rw 5 [fslSepMul_assoc]
          nth_rw 2 [← fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
          nth_rw 1 [← fslIverson_fslMin_eq_fslIverson_fslMul]
          rw [ico_fslBigSepMul, ← rInv2_wo]
          nth_rw 3 [fslIverson_fslMin_eq_fslIverson_fslMul]
          nth_rw 1 [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
          nth_rw 8 [fslSepMul_comm]
          nth_rw 1 [fslSepMul_comm]
          simp only [← fslSepMul_assoc]
          apply fslSepMul_mono le_rfl (fslSepMul_mono le_rfl ?_)
          rw [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]; rw[← fslSepMul_assoc]
          nth_rw 5 [fslSepMul_comm]
          nth_rw 3 [fslSepMul_assoc]
          nth_rw 5 [fslSepMul_comm]
          simp only [← fslSepMul_assoc]
          apply fslSepMul_mono
          · simp only [rInv1, fslSubst_of_fslBigSepMul, fslSubst_of_fslMax, fslSubst_of_fslPointsTo,
              substVal_of_add, ne_eq, String.reduceEq, not_false_eq_true, substVal_of_var_neq,
              substVal_of_const]
            exact le_rfl
          rw [fslSepMul_comm]
          apply fslSepMul_mono
          · rw [← fslMul_eq_fslSepMul_emp_of_pure pure_fslIverson_slEquals]
            apply le_fslSup _ _ i
            simp only [conservative_pointsTo, conservative_mul, conservative_equals, conservative_max,
              conservative_min]
            rw [conservative_entail]
            intro s ⟨h_pt, h_eq⟩
            apply And.intro
            · exact h_eq
            · right; right
              simp only [slPointsTo, add, var, const]
              simp only [slPointsTo, add, var, const] at h_pt
              simp only [slEquals, var, const] at h_eq
              obtain ⟨l, h_l, h_heap⟩ := h_pt
              use l
              apply And.intro ?_ h_heap
              rw [h_l, h_eq]
          · simp only [conservative_equals, conservative_max, conservative_min]
            rw [conservative_entail]
            intro s h
            apply And.intro h
            right; right
            simp only [slEquals, const]
  apply safeTuple_lookup
  rw [varRV_of_fslEmp]
  decide

theorem consumer_sound₂ (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃⁅is_in_ico "y3" 0 ↑y⁆ ⊓ (var "l" === sub (dec (const ↑y)) (var "y3")) ⦄
      "l" ≔ inc (var "l")
    ⦃ ⁅is_in_ico "y3" 0 ↑y⁆ ⊓ var "l" === sub (dec (const ↑y)) (dec (var "y3")) ⦄ := by
  apply safeTuple_monotonicty
    `[fsl| (⁅is_in_ico "y3" 0 ↑y⁆
      ⊓ var "l" === sub (dec (const ↑y)) (dec (var "y3")))("l" ↦ inc (var "l"))]
    _ ?_ le_rfl
  swap
  · simp only [fslSubst_of_fslMin, fslSubst_of_fslIverson, ne_eq, String.reduceEq,
      not_false_eq_true, substProp_ico_neq, fslSubst_of_fslEquals, substVal_of_var, substVal_of_sub,
      substVal_of_dec, substVal_of_const, substVal_of_var_neq]
    apply fslMin_le_fslMin le_rfl
    rw [conservative_equals, conservative_equals, conservative_entail]
    intro s
    simp only [slEquals, var, sub, dec, const, inc, sub_sub_sub_cancel_right, le_Prop_eq]
    intro h
    rw [h]
    ring
  apply safeTuple_assign
  apply Set.not_mem_subset rInv_subset
  decide

theorem consumer_sound₃ (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃ ⁅is_in_ico "y3" 0 ↑y⁆ ⊓ var "l" === sub (dec (const ↑y)) (dec $ var "y3") ⦄
    "y3" ≔ dec (var "y3") ⦃
    ⁅is_in_ico "y3" (-1) ↑y⁆ ⊓ var "l" === sub (dec (const ↑y)) (var "y3") ⦄ := by
  apply safeTuple_monotonicty
    `[fsl| (⁅is_in_ico "y3" (-1) ↑y⁆
      ⊓ var "l" === sub (dec (const ↑y)) (var "y3"))("y3" ↦ dec (var "y3"))]
    _ ?_ le_rfl
  swap
  · simp only [Int.reduceNeg, fslSubst_of_fslMin, fslSubst_of_fslIverson, substProp_ico_dec_var,
      Nat.cast_add, Nat.cast_one, fslSubst_of_fslEquals, ne_eq, String.reduceEq, not_false_eq_true,
      substVal_of_var_neq, substVal_of_sub, substVal_of_dec, substVal_of_const, substVal_of_var]
    apply fslMin_le_fslMin ?_ le_rfl
    rw [conservative_entail]
    intro s
    simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
      exists_prop, le_Prop_eq, forall_exists_index, and_imp]
    intro i h_u h_l h_eq
    use i
    apply And.intro (And.intro h_u ?_) h_eq
    apply lt_of_lt_of_le h_l
    exact Int.le.intro 1 rfl
  apply safeTuple_assign
  apply Set.not_mem_subset rInv_subset
  decide

theorem consumer_sound (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃⁅is_in_ico "y3" (-1) y⁆ ⊓ var "l" === sub (dec $ const y) (var "y3")⦄
    consumer
    ⦃ var "l" === const ↑y ⦄ := by
  unfold consumer
  apply safeTuple_monotonicty _
    `[fsl| ⁅is_in_ico "y3" (-1) y⁆
      ⬝ var "y3" === const (-1) ⬝ var "l" === sub (dec $ const y) (var "y3")] le_rfl
  · simp only [conservative_mul, conservative_equals]
    rw [conservative_entail]
    intro s ⟨h_ico, h_y3, h_l⟩
    simp only [slEquals, var, const]
    simp only [slEquals, var, sub, dec, const] at h_l
    simp only [slEquals, var, const] at h_y3
    rw [h_l, h_y3]
    simp only [sub_neg_eq_add, sub_add_cancel]
  apply safeTuple_while `[fsl| ⁅is_in_ico "y3" 0 y⁆ ⊓ var "l" === sub (dec $ const y) (var "y3")]
  · rw [is_in_ico_eq_or_first _ (Int.le.intro_sub (y + Nat.succ 0) rfl)]
    simp only [Int.reduceNeg, neg_add_cancel, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [← conservative_max, fslMin_fslMax_right]
    rw [entailment_iff_pi_le, fslMax_le_iff]
    apply And.intro
    · apply le_fslMax
      left
      simp only [conservative_equals, conservative_min, conservative_mul, conservative_entail]
      intro s ⟨h_ico, h_eq⟩
      simp only [slEquals, var, sub, dec, const] at h_eq
      apply And.intro
      · simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
          exists_prop] at h_ico
        obtain ⟨i, ⟨h_iu, h_il⟩, h_i⟩ := h_ico
        simp only [slExp, leq, const, var, decide_eq_true_eq]
        rw [← h_i]
        norm_cast
      exact And.intro h_ico h_eq
    · apply le_fslMax
      right
      simp only [conservative_equals, conservative_min, conservative_not, conservative_max,
        conservative_mul, conservative_entail]
      intro s ⟨⟨h_y3, h_y⟩, h_l⟩
      apply And.intro
      · simp only [slNot, slExp, leq, const, var, decide_eq_true_eq, not_le]
        simp only [slEquals, var, const] at h_y3
        rw [h_y3]
        rfl
      apply And.intro
      · right
        exact ⟨h_y3, h_y⟩
      exact ⟨h_y3, h_l⟩
  apply safeTuple_seq _ (consumer_sound₁ y)
  apply safeTuple_monotonicty
    `[fsl|
      ⁅<eq (var "x3") (const 0)>⁆ ⬝ ⁅is_in_ico "y3" (-1) ↑y⁆ ⊓ (var "l" === sub (dec (const ↑y)) (var "y3"))
      ⊔ ~⁅<eq (var "x3") (const 0)>⁆ ⬝ ⁅is_in_ico "y3" 0 y⁆ ⊓ (var "l" === sub (dec $ const y) (var "y3"))
        ⊓ ((var "x3" === const 1) ⊔ var "x3" === const 2)]
    _ ?_ le_rfl
  swap
  · nth_rw 2 [fslMin_comm]; rw [fslMin_fslMax_right]
    nth_rw 1 [fslMin_comm]; rw [fslMin_fslMax_right]
    apply (fslMax_le_iff _ _ _).mpr
    apply And.intro
    · apply le_fslMax
      left
      simp only [conservative_equals, conservative_min, Int.reduceNeg, conservative_mul]
      rw [conservative_entail]
      intro s ⟨⟨h_x3, h_l⟩, h_ico⟩
      apply And.intro
      · simp only [slExp, eq, var, const, decide_eq_true_eq]
        simp only [slEquals, var, const] at h_x3
        exact h_x3
      apply And.intro ?_ h_l
      apply is_in_ico_le_down _ _ _ ?_
      · exact h_ico
      · exact Int.toNat_eq_zero.mp rfl
    · apply le_fslMax
      right
      simp only [conservative_equals, conservative_max, conservative_min, conservative_not,
        conservative_mul]
      rw [conservative_entail]
      intro s ⟨⟨h_x3, h_l⟩, h_ico⟩
      apply And.intro
      · simp only [slNot, slExp, eq, var, const, decide_eq_true_eq]
        cases h_x3
        case inl h_x3 =>
          simp only [slEquals, var, const] at h_x3
          simp only [h_x3, one_ne_zero, not_false_eq_true]
        case inr h_x3 =>
          simp only [slEquals, var, const] at h_x3
          simp only [h_x3, OfNat.ofNat_ne_zero, not_false_eq_true]
      apply And.intro h_ico
      apply And.intro h_l
      exact h_x3
  apply safeTuple_conditionalBranching (safeTuple_skip _ _)
  apply safeTuple_seq _ ?_ (consumer_sound₃ y)
  apply safeTuple_monotonicty
    `[fsl|
      ⁅<eq (var "x3") (const (-1))>⁆ ⬝ fFalse
      ⊔ ~⁅<eq (var "x3") (const (-1))>⁆ ⬝ ⁅is_in_ico "y3" 0 y⁆
        ⊓ (var "l" === sub (dec $ const y) (var "y3"))]
    _ ?_ le_rfl
  swap
  · apply le_fslMax
    right
    simp only [conservative_equals, conservative_max, conservative_min, conservative_not,
      conservative_mul]
    rw [conservative_entail]
    intro s ⟨h_ico, h_l, h_x3⟩
    apply And.intro ?_ ⟨h_ico, h_l⟩
    simp only [slNot, slExp, eq, var, const, decide_eq_true_eq]
    cases h_x3
    case inl h_x3 =>
      simp only [slEquals, var, const] at h_x3
      rw [h_x3]
      exact ne_of_beq_false rfl
    case inr h_x3 =>
      simp only [slEquals, var, const] at h_x3
      rw [h_x3]
      exact ne_of_beq_false rfl
  exact safeTuple_conditionalBranching safeTuple_false_left (consumer_sound₂ y)
