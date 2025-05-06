import LeanFSL.Examples.ProducerConsumer.Basic

open Syntax CFSL FSL SL

theorem channel_sound₁ (y : ℕ) (p : unitInterval) :
    ⊢ [[rInv y]]
    ⦃ ⁅is_in_ico "y2" 0 ↑y⁆ ⬝ <exp (constP p) (inc $ var "y2")> ⦄
    "x2" ≔* add (var "z1") (var "y2")
    ⦃ ⁅is_in_ico "y2" 0 ↑y⁆ ⬝ <exp (constP p) (inc $ var "y2")>
      ⬝ ((var "x2" === const 0) ⊔ (var "x2" === const 1) ⊔ (var "x2" === const 2)) ⦄ := by
  nth_rw 3 [fslMul_comm]
  rw [fslMul_assoc]
  rw [fslMul_eq_fslSepMul_emp_of_pure pure_fslReal, fslMul_eq_fslSepMul_emp_of_pure pure_fslReal]
  apply safeTuple_frame
  · simp only [wrtProg, Set.singleton_inter_eq_empty]
    have : varRV `[fsl| <exp (constP p) (inc (var "y2"))> ⊓ emp ] ⊆ {"y2"} := by {
      apply subset_trans varRV_of_fslMin
      rw [varRV_of_fslEmp, Set.union_empty, varRV_of_fslReal]
      apply subset_trans varProb_of_exp
      rw [varProb_of_constP, Set.empty_union, varValue_of_inc, varValue_of_var]
    }
    apply Set.not_mem_subset this
    decide
  apply safeTuple_atom
  · simp only [Atom.atomicProgram]
  apply safeTuple_monotonicty
    `[fsl| S (q : ℚ). add (var "z1") (var "y2") ↦ q ⋆ (add (var "z1") (var "y2") ↦ q
        -⋆ ((⁅is_in_ico "y2" 0 ↑y⁆
          ⬝ ((var "x2" === const 0) ⊔ (var "x2" === const 1) ⊔ (var "x2" === const 2)))
          ⋆ [[rInv y]])("x2" ↦ q))]
    _ ?_ le_rfl
  · apply safeTuple_lookup
    rw [varRV_of_fslEmp]
    decide
  · nth_rw 1 [rInv, rInv1]
    rw [fslSepMul_assoc]
    rw [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
    rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
    rw [ico_fslBigSepMul]
    rw [← rInv1_wo]
    rw [fslIverson_fslMin_eq_fslIverson_fslMul]
    rw [← fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
    nth_rw 3 [fslSepMul_comm]
    rw [fslSepMul_fslSup_distr, fslSepMul_fslSup_distr]
    rw [fslSepMul_comm]
    rw [fslSepMul_fslSup_distr]
    apply fslSup_le
    intro i
    rw [fslMin_comm, fslMin_fslMax_right, fslMin_fslMax_right]
    rw [fslSepMul_fslMax_distr, fslSepMul_fslMax_distr, fslSepMul_fslMax_distr]
    rw [entailment_iff_pi_le, fslMax_le_iff]
    apply And.intro
    · apply le_fslSup _ _ 0
      nth_rw 3 [fslSepMul_comm]; nth_rw 2 [fslSepMul_assoc]
      nth_rw 3 [fslSepMul_comm]; nth_rw 1 [← fslSepMul_assoc]
      nth_rw 1 [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]
      rw [← fslSepMul_assoc]
      apply fslSepMul_mono
      · rw [conservative_pointsTo, conservative_equals, conservative_min, conservative_pointsTo]
        rw [conservative_entail]
        intro s ⟨h_pt, h_eq⟩
        simp only [slPointsTo, add, var]
        simp only [slPointsTo, add, var, const] at h_pt
        simp only [slEquals, var, const] at h_eq
        obtain ⟨l, h_l, h_heap⟩ := h_pt
        rw [h_eq]
        use l
      · rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
        simp only [fslSubst_of_fslSepMul, fslSubst_of_fslMul, fslSubst_of_fslIverson,
          fslSubst_of_fslMax, fslSubst_of_fslEquals, substVal_of_var,substVal_of_const]
        rw [substProp_ico_neq (by decide)]
        simp only [rInv, fslSubst_of_fslSepMul]
        nth_rw 2 [fslSepMul_assoc]; rw [← fslSepMul_assoc, fslSepMul_comm]
        apply fslSepMul_mono
        swap
        · unfold rInv2
          simp only [fslSubst_of_fslBigSepMul, fslSubst_of_fslMax, fslSubst_of_fslPointsTo,
            substVal_of_add, ne_eq, String.reduceEq, not_false_eq_true, substVal_of_var_neq,
            substVal_of_const]
          exact le_rfl
        · have : `[fsl| ⁅is_in_ico "y2" 0 ↑y⁆ ⋆ [[rInv1 y]]( "x2" ↦ fun x ↦ 0 ) ]
            ≤ `[fsl| (⁅is_in_ico "y2" 0 ↑y⁆
              ⬝ ((fun x ↦ 0 === const 0) ⊔ (fun x ↦ 0 === const 1) ⊔ fun x ↦ 0 === const 2))
              ⋆ [[rInv1 y]]( "x2" ↦ fun x ↦ 0 ) ] := by {
            apply fslSepMul_mono ?_ le_rfl
            nth_rw 1 [← fslMul_fslTrue (`[fsl| ⁅is_in_ico "y2" 0 ↑y⁆])]
            apply fslMul_mono le_rfl
            simp only [conservative_true, conservative_equals, conservative_max]
            rw [conservative_entail]
            intro s _
            left
            trivial
          }
          apply le_trans ?_ this ; clear this
          nth_rw 2 [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
          rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
          rw [rInv1]
          simp only [fslSubst_of_fslBigSepMul, fslSubst_of_fslMax, fslSubst_of_fslPointsTo,
            substVal_of_add, ne_eq, String.reduceEq, not_false_eq_true, substVal_of_var_neq,
            substVal_of_const]
          rw [ico_fslBigSepMul]
          rw [← rInv1_wo]
          rw [fslIverson_fslMin_eq_fslIverson_fslMul]
          rw [← fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
          nth_rw 2 [fslSepMul_comm]; rw [← fslSepMul_assoc]
          nth_rw 2 [fslSepMul_assoc]; rw [fslSepMul_comm]
          apply fslSepMul_mono ?_ le_rfl
          rw [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
          rw [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
          apply fslSepMul_mono le_rfl
          simp only [conservative_pointsTo, conservative_mul, conservative_equals, conservative_max,
            conservative_min, conservative_sup]
          rw [conservative_entail]
          intro s ⟨h_ico, h_pt⟩
          apply And.intro h_ico
          rw [slExists_apply]
          simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
            exists_prop] at h_ico
          obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h_ico
          use i.toNat
          apply And.intro
          · simp only [slEquals, var, const]
            rw [← h_eq]
            norm_cast
            rw [Int.ofNat_toNat, left_eq_sup]
            exact h_l
          · left
            simp only [slPointsTo, add, var, const]
            simp only [slPointsTo, add, var] at h_pt
            obtain ⟨l', h_l', h_heap⟩ := h_pt
            use l'
            apply And.intro ?_ h_heap
            rw [h_l', add_right_inj, ← h_eq]
            norm_cast
            rw [Int.ofNat_toNat, left_eq_sup]
            exact h_l
    · rw [fslSepMul_fslMax_distr, fslSepMul_fslMax_distr, fslSepMul_fslMax_distr]
      rw [entailment_iff_pi_le, fslMax_le_iff]
      apply And.intro
      · apply le_fslSup _ _ 1
        nth_rw 3 [fslSepMul_comm]; nth_rw 2 [fslSepMul_assoc]
        nth_rw 3 [fslSepMul_comm]; nth_rw 1 [← fslSepMul_assoc]
        nth_rw 1 [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]
        rw [← fslSepMul_assoc]
        apply fslSepMul_mono
        · rw [conservative_pointsTo, conservative_equals, conservative_min, conservative_pointsTo]
          rw [conservative_entail]
          intro s ⟨h_pt, h_eq⟩
          simp only [slPointsTo, add, var]
          simp only [slPointsTo, add, var, const] at h_pt
          simp only [slEquals, var, const] at h_eq
          obtain ⟨l, h_l, h_heap⟩ := h_pt
          rw [h_eq]
          use l
        · rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
          simp only [fslSubst_of_fslSepMul, fslSubst_of_fslMul, fslSubst_of_fslIverson,
            fslSubst_of_fslMax, fslSubst_of_fslEquals, substVal_of_var,substVal_of_const]
          rw [substProp_ico_neq (by decide)]
          simp only [rInv, fslSubst_of_fslSepMul]
          nth_rw 2 [fslSepMul_assoc]; rw [← fslSepMul_assoc, fslSepMul_comm]
          apply fslSepMul_mono
          swap
          · unfold rInv2
            simp only [fslSubst_of_fslBigSepMul, fslSubst_of_fslMax, fslSubst_of_fslPointsTo,
              substVal_of_add, ne_eq, String.reduceEq, not_false_eq_true, substVal_of_var_neq,
              substVal_of_const]
            exact le_rfl
          · have : `[fsl| ⁅is_in_ico "y2" 0 ↑y⁆ ⋆ [[rInv1 y]]( "x2" ↦ fun x ↦ 1 ) ]
              ≤ `[fsl| (⁅is_in_ico "y2" 0 ↑y⁆
                ⬝ ((fun x ↦ 1 === const 0) ⊔ (fun x ↦ 1 === const 1) ⊔ fun x ↦ 1 === const 2))
                ⋆ [[rInv1 y]]( "x2" ↦ fun x ↦ 1 ) ] := by {
              apply fslSepMul_mono ?_ le_rfl
              nth_rw 1 [← fslMul_fslTrue (`[fsl| ⁅is_in_ico "y2" 0 ↑y⁆])]
              apply fslMul_mono le_rfl
              simp only [conservative_true, conservative_equals, conservative_max]
              rw [conservative_entail]
              intro s _
              right; left
              trivial
            }
            apply le_trans ?_ this ; clear this
            nth_rw 2 [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
            rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
            rw [rInv1]
            simp only [fslSubst_of_fslBigSepMul, fslSubst_of_fslMax, fslSubst_of_fslPointsTo,
              substVal_of_add, ne_eq, String.reduceEq, not_false_eq_true, substVal_of_var_neq,
              substVal_of_const]
            rw [ico_fslBigSepMul]
            rw [← rInv1_wo]
            rw [fslIverson_fslMin_eq_fslIverson_fslMul]
            rw [← fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
            nth_rw 2 [fslSepMul_comm]; rw [← fslSepMul_assoc]
            nth_rw 2 [fslSepMul_assoc]; rw [fslSepMul_comm]
            apply fslSepMul_mono ?_ le_rfl
            rw [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
            rw [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
            apply fslSepMul_mono le_rfl
            simp only [conservative_pointsTo, conservative_mul, conservative_equals, conservative_max,
              conservative_min, conservative_sup]
            rw [conservative_entail]
            intro s ⟨h_ico, h_pt⟩
            apply And.intro h_ico
            rw [slExists_apply]
            simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
              exists_prop] at h_ico
            obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h_ico
            use i.toNat
            apply And.intro
            · simp only [slEquals, var, const]
              rw [← h_eq]
              norm_cast
              rw [Int.ofNat_toNat, left_eq_sup]
              exact h_l
            · right; left
              simp only [slPointsTo, add, var, const]
              simp only [slPointsTo, add, var] at h_pt
              obtain ⟨l', h_l', h_heap⟩ := h_pt
              use l'
              apply And.intro ?_ h_heap
              rw [h_l', add_right_inj, ← h_eq]
              norm_cast
              rw [Int.ofNat_toNat, left_eq_sup]
              exact h_l
      · apply le_fslSup _ _ 2
        nth_rw 3 [fslSepMul_comm]; nth_rw 2 [fslSepMul_assoc]
        nth_rw 3 [fslSepMul_comm]; nth_rw 1 [← fslSepMul_assoc]
        nth_rw 1 [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]
        rw [← fslSepMul_assoc]
        apply fslSepMul_mono
        · rw [conservative_pointsTo, conservative_equals, conservative_min, conservative_pointsTo]
          rw [conservative_entail]
          intro s ⟨h_pt, h_eq⟩
          simp only [slPointsTo, add, var]
          simp only [slPointsTo, add, var, const] at h_pt
          simp only [slEquals, var, const] at h_eq
          obtain ⟨l, h_l, h_heap⟩ := h_pt
          rw [h_eq]
          use l
        · rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
          simp only [fslSubst_of_fslSepMul, fslSubst_of_fslMul, fslSubst_of_fslIverson,
            fslSubst_of_fslMax, fslSubst_of_fslEquals, substVal_of_var,substVal_of_const]
          rw [substProp_ico_neq (by decide)]
          simp only [rInv, fslSubst_of_fslSepMul]
          nth_rw 2 [fslSepMul_assoc]; rw [← fslSepMul_assoc, fslSepMul_comm]
          apply fslSepMul_mono
          swap
          · unfold rInv2
            simp only [fslSubst_of_fslBigSepMul, fslSubst_of_fslMax, fslSubst_of_fslPointsTo,
              substVal_of_add, ne_eq, String.reduceEq, not_false_eq_true, substVal_of_var_neq,
              substVal_of_const]
            exact le_rfl
          · have : `[fsl| ⁅is_in_ico "y2" 0 ↑y⁆ ⋆ [[rInv1 y]]( "x2" ↦ fun x ↦ 2 ) ]
              ≤ `[fsl| (⁅is_in_ico "y2" 0 ↑y⁆
                ⬝ ((fun x ↦ 2 === const 0) ⊔ (fun x ↦ 2 === const 1) ⊔ fun x ↦ 2 === const 2))
                ⋆ [[rInv1 y]]( "x2" ↦ fun x ↦ 2 ) ] := by {
              apply fslSepMul_mono ?_ le_rfl
              nth_rw 1 [← fslMul_fslTrue (`[fsl| ⁅is_in_ico "y2" 0 ↑y⁆])]
              apply fslMul_mono le_rfl
              simp only [conservative_true, conservative_equals, conservative_max]
              rw [conservative_entail]
              intro s _
              right; right
              trivial
            }
            apply le_trans ?_ this ; clear this
            nth_rw 2 [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
            rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
            rw [rInv1]
            simp only [fslSubst_of_fslBigSepMul, fslSubst_of_fslMax, fslSubst_of_fslPointsTo,
              substVal_of_add, ne_eq, String.reduceEq, not_false_eq_true, substVal_of_var_neq,
              substVal_of_const]
            rw [ico_fslBigSepMul]
            rw [← rInv1_wo]
            rw [fslIverson_fslMin_eq_fslIverson_fslMul]
            rw [← fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
            nth_rw 2 [fslSepMul_comm]; rw [← fslSepMul_assoc]
            nth_rw 2 [fslSepMul_assoc]; rw [fslSepMul_comm]
            apply fslSepMul_mono ?_ le_rfl
            rw [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
            rw [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
            apply fslSepMul_mono le_rfl
            simp only [conservative_pointsTo, conservative_mul, conservative_equals, conservative_max,
              conservative_min, conservative_sup]
            rw [conservative_entail]
            intro s ⟨h_ico, h_pt⟩
            apply And.intro h_ico
            rw [slExists_apply]
            simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
              exists_prop] at h_ico
            obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h_ico
            use i.toNat
            apply And.intro
            · simp only [slEquals, var, const]
              rw [← h_eq]
              norm_cast
              rw [Int.ofNat_toNat, left_eq_sup]
              exact h_l
            · right; right
              simp only [slPointsTo, add, var, const]
              simp only [slPointsTo, add, var] at h_pt
              obtain ⟨l', h_l', h_heap⟩ := h_pt
              use l'
              apply And.intro ?_ h_heap
              rw [h_l', add_right_inj, ← h_eq]
              norm_cast
              rw [Int.ofNat_toNat, left_eq_sup]
              exact h_l

theorem channel_sound₂ (y : ℕ) (p : unitInterval) :
    ⊢ [[rInv y]]
    ⦃ (var "y2" === const 0) ⊓ ⁅is_in_ico "y2" 0 y⁆
        ⊓ ((var "x2" === const 1) ⊔ var "x2" === const 2)
      ⊔ ~var "y2" === const 0 ⬝ ⁅is_in_ico "y2" 0 ↑y⁆ ⬝ <exp (constP p) (var "y2")>
        ⬝ ((var "x2" === const 1) ⊔ var "x2" === const 2) ⦄
    add (var "z2") (var "y2") *≔ var "x2"
    ⦃ ⁅is_in_ico "y2" 1 ↑y⁆ ⬝ <exp (constP p) (var "y2")> ⊔ ⁅var "y2" === const 0⁆ ⦄ := by
  apply safeTuple_atom
  · simp only [Atom.atomicProgram]
  · apply safeTuple_monotonicty
      `[fsl| (S (q : ℚ). add (var "z2") (var "y2") ↦ q) ⋆ (add (var "z2") (var "y2") ↦ var "x2"
        -⋆ (⁅is_in_ico "y2" 1 ↑y⁆ ⬝ <exp (constP p) (var "y2")> ⊔ ⁅var "y2" === const 0⁆) ⋆ [[rInv y]])]
      _ ?_ le_rfl (safeTuple_mutate _)
    rw [fslSepMul_comm, fslSepMul_fslMax_distr]
    rw [entailment_iff_pi_le, fslMax_le_iff]
    apply And.intro
    · rw [conservative_equals, fslIverson_fslMin_eq_fslIverson_fslMul,
        fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [fslMul_comm, ← fslMul_assoc, fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
      rw [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]
      rw [rInv]; nth_rw 1 [rInv2]; nth_rw 3 [fslSepMul_comm]; nth_rw 1 [fslSepMul_assoc]
      rw [← fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
      rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [ico_fslBigSepMul, ← rInv2_wo]
      rw [fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
      nth_rw 4 [fslSepMul_comm]; rw [fslSepMul_fslSup_distr]
      rw [fslSepMul_fslSup_distr]
      nth_rw 2 [fslSepMul_comm]; rw [fslSepMul_fslSup_distr]
      nth_rw 1 [fslSepMul_comm]; rw [fslSepMul_fslSup_distr]
      apply fslSup_le
      intro i
      nth_rw 3 [fslSepMul_comm]; nth_rw 2 [fslSepMul_assoc]
      nth_rw 4 [fslSepMul_comm]; nth_rw 1 [fslSepMul_assoc]
      nth_rw 3 [fslSepMul_comm]; nth_rw 1 [fslSepMul_assoc]
      nth_rw 3 [fslSepMul_comm]
      simp only [← fslSepMul_assoc]
      rw [← fslMin_self (`[fsl| var "y2" === const i]), fslMin_assoc]
      rw [conservative_equals, fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [fslMul_eq_emp_fslSepMul_of_pure pure_fslIverson_slEquals]
      nth_rw 2 [fslSepMul_comm]
      rw [← fslSepMul_assoc]
      apply fslSepMul_mono
      · rw [fslMin_comm, fslMin_fslMax_right, fslMin_fslMax_right]
        rw [entailment_iff_pi_le, fslMax_le_iff]
        apply And.intro
        · apply le_fslSup _ _ 0
          rw [conservative_pointsTo, conservative_min, conservative_pointsTo, conservative_entail]
          intro s ⟨h_pt, h_eq⟩
          simp only [slPointsTo, add, var]
          simp only [slPointsTo, add, var, const] at h_pt
          simp only [slEquals, var, const] at h_eq
          obtain ⟨l, h_l, h_heap⟩ := h_pt
          use l
          apply And.intro ?_ h_heap
          rw [h_l, h_eq]
        · rw [entailment_iff_pi_le, fslMax_le_iff]
          apply And.intro
          · apply le_fslSup _ _ 1
            rw [conservative_pointsTo, conservative_min, conservative_pointsTo, conservative_entail]
            intro s ⟨h_pt, h_eq⟩
            simp only [slPointsTo, add, var]
            simp only [slPointsTo, add, var, const] at h_pt
            simp only [slEquals, var, const] at h_eq
            obtain ⟨l, h_l, h_heap⟩ := h_pt
            use l
            apply And.intro ?_ h_heap
            rw [h_l, h_eq]
          · apply le_fslSup _ _ 2
            rw [conservative_pointsTo, conservative_min, conservative_pointsTo, conservative_entail]
            intro s ⟨h_pt, h_eq⟩
            simp only [slPointsTo, add, var]
            simp only [slPointsTo, add, var, const] at h_pt
            simp only [slEquals, var, const] at h_eq
            obtain ⟨l, h_l, h_heap⟩ := h_pt
            use l
            apply And.intro ?_ h_heap
            rw [h_l, h_eq]
      · rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
        nth_rw 6 [fslSepMul_comm]; rw [fslSepMul_fslMax_distr]
        apply le_fslMax
        right
        nth_rw 3 [fslSepMul_assoc]; nth_rw 5 [fslSepMul_comm]
        nth_rw 2 [fslSepMul_assoc]; nth_rw 2 [fslSepMul_assoc]
        nth_rw 5 [fslSepMul_comm]
        simp only [← fslSepMul_assoc]
        nth_rw 1 [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]
        rw [← fslSepMul_assoc]
        apply fslSepMul_mono le_rfl
        rw [fslMul_comm, fslMul_eq_fslSepMul_emp_of_pure
          (pure_fslMax pure_fslEquals pure_fslEquals)]
        simp only [← fslSepMul_assoc]
        nth_rw 2 [fslSepMul_assoc]; nth_rw 3 [fslSepMul_comm]
        nth_rw 1 [← fslSepMul_assoc]; rw [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]
        simp only [← fslSepMul_assoc]
        rw [fslSepMul_comm]
        apply fslSepMul_mono ?_ le_rfl
        have :
            `[fsl| (⁅var "y2" === const ↑i⁆ ⊓ emp) ⋆ [[rInv2_wo y "y2"]]
              ⋆ (((var "x2" === const 1) ⊔ var "x2" === const 2) ⊓ emp)
              ⋆ (⁅is_in_ico "y2" 0 ↑y⁆ ⊓ emp) ⋆ add (var "z2") (var "y2") ↦ var "x2" ]
            ≤ `[fsl| ⁅is_in_ico "y2" 0 y⁆ ⊓ (S (j : ℕ). (var "y2" === const j)
              ⊓ ((add (var "z2") (const j) ↦ const 0)
                ⊔ (add (var "z2") (const j) ↦ const 1)
                ⊔ (add (var "z2") (const j) ↦ const 2)))
            ⋆ [[rInv2_wo y "y2"]]] := by {
          nth_rw 3 [fslSepMul_assoc]; nth_rw 4 [fslSepMul_comm]
          nth_rw 1 [← fslSepMul_assoc]; nth_rw 2 [fslSepMul_assoc]
          nth_rw 3 [fslSepMul_comm]
          simp only [← fslSepMul_assoc]
          rw [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]; rw [← fslSepMul_assoc]
          rw [← fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
          rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
          apply fslMin_le_fslMin le_rfl
          rw [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]; rw [← fslSepMul_assoc, fslSepMul_comm]
          apply fslSepMul_mono ?_ le_rfl
          rw [fslSepMul_comm]
          rw [← fslMul_eq_fslSepMul_emp_of_pure pure_fslIverson_slEquals]
          rw [fslSepMul_comm]
          rw [← fslMul_eq_fslSepMul_emp_of_pure (pure_fslMax pure_fslEquals pure_fslEquals)]
          rw [← fslMul_assoc]
          simp only [conservative_pointsTo, conservative_equals, conservative_max, conservative_mul,
            conservative_min, conservative_sup]
          rw [conservative_entail]
          rintro s ⟨h_pt, h_eq | h_eq, h_i⟩
          · rw [slExists_apply]
            use i
            apply And.intro h_i
            right; left
            simp only [slPointsTo, add, var, const]
            simp only [slPointsTo, add, var] at h_pt
            simp only [slEquals, var, const] at h_i h_eq
            obtain ⟨l, h_l, h_heap⟩ := h_pt
            use l
            rw [h_eq] at h_heap
            rw [h_i] at h_l
            exact ⟨h_l, h_heap⟩
          · rw [slExists_apply]
            use i
            apply And.intro h_i
            right; right
            simp only [slPointsTo, add, var, const]
            simp only [slPointsTo, add, var] at h_pt
            simp only [slEquals, var, const] at h_i h_eq
            obtain ⟨l, h_l, h_heap⟩ := h_pt
            use l
            rw [h_eq] at h_heap
            rw [h_i] at h_l
            exact ⟨h_l, h_heap⟩
        }
        apply le_trans this ; clear this
        rw [rInv2_wo]
        rw [← ico_fslBigSepMul, ← rInv2]
        apply fslMin_le
        right
        exact le_rfl
    · rw [fslMul_assoc]; nth_rw 2 [fslMul_comm]; rw [← fslMul_assoc]
      rw [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]; rw [fslSepMul_assoc]
      nth_rw 2 [fslSepMul_comm]
      rw [rInv]; nth_rw 3 [fslSepMul_comm]; nth_rw 1 [fslSepMul_assoc]
      rw [← fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
      rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [rInv2, ico_fslBigSepMul, ← rInv2_wo]
      rw [fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
      simp only [← fslSepMul_assoc]; rw [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]
      rw [← fslSepMul_assoc]
      apply fslSepMul_mono
      · apply fslSup_le
        intro i
        rw [fslMin_comm, fslMin_fslMax_right, fslMin_fslMax_right]
        rw [entailment_iff_pi_le, fslMax_le_iff]
        apply And.intro
        · apply le_fslSup _ _ 0
          rw [conservative_pointsTo, conservative_equals, conservative_min,
            conservative_pointsTo, conservative_entail]
          intro s ⟨h_pt, h_eq⟩
          simp only [slPointsTo, add, var]
          simp only [slPointsTo, add, var, const] at h_pt
          simp only [slEquals, var, const] at h_eq
          obtain ⟨l, h_l, h_heap⟩ := h_pt
          use l
          apply And.intro ?_ h_heap
          rw [h_l, h_eq]
        · rw [entailment_iff_pi_le, fslMax_le_iff]
          apply And.intro
          · apply le_fslSup _ _ 1
            rw [conservative_pointsTo, conservative_equals, conservative_min,
              conservative_pointsTo, conservative_entail]
            intro s ⟨h_pt, h_eq⟩
            simp only [slPointsTo, add, var]
            simp only [slPointsTo, add, var, const] at h_pt
            simp only [slEquals, var, const] at h_eq
            obtain ⟨l, h_l, h_heap⟩ := h_pt
            use l
            apply And.intro ?_ h_heap
            rw [h_l, h_eq]
          · apply le_fslSup _ _ 2
            rw [conservative_pointsTo, conservative_equals, conservative_min,
              conservative_pointsTo, conservative_entail]
            intro s ⟨h_pt, h_eq⟩
            simp only [slPointsTo, add, var]
            simp only [slPointsTo, add, var, const] at h_pt
            simp only [slEquals, var, const] at h_eq
            obtain ⟨l, h_l, h_heap⟩ := h_pt
            use l
            apply And.intro ?_ h_heap
            rw [h_l, h_eq]
      · rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
        nth_rw 5 [fslSepMul_comm]; nth_rw 3 [fslSepMul_comm]
        simp only [← fslSepMul_assoc]
        rw [fslSepMul_assoc]; nth_rw 2 [fslSepMul_comm]; rw [← fslSepMul_assoc]
        apply fslSepMul_mono le_rfl
        rw [← fslMin_of_le _ _ ((conservative_entail _ _).mpr (is_in_ico_le_down _ 0 1 Int.one_nonneg))]
        nth_rw 2 [fslIverson_fslMin_eq_fslIverson_fslMul]
        have : `[fsl| ⁅is_in_ico "y2" 0 ↑y⁆ ⬝ ⁅is_in_ico "y2" 1 ↑y⁆ ⬝ <exp (constP p) (var "y2")> ]
            ≤ `[fsl| ((⁅is_in_ico "y2" 0 ↑y⁆ ⬝ ⁅is_in_ico "y2" 1 ↑y⁆)
              ⬝ <exp (constP p) (var "y2")> ⊔ ⁅var "y2" === const 0⁆)] := by {
          apply le_fslMax
          left
          rw [fslMul_assoc]
          exact le_rfl
        }
        apply le_trans ?_ (fslSepMul_mono le_rfl this ); clear this
        rw [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
        nth_rw 3 [fslSepMul_assoc]; nth_rw 5 [fslSepMul_comm]
        nth_rw 2 [← fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
        rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [ico_fslBigSepMul, ← rInv2_wo]
        nth_rw 2 [fslIverson_fslMin_eq_fslIverson_fslMul]
        nth_rw 1 [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
        simp only [← fslSepMul_assoc]
        nth_rw 3 [fslSepMul_comm]; nth_rw 6 [fslSepMul_comm]
        simp only [fslSepMul_assoc]
        apply fslSepMul_mono ?_ le_rfl
        nth_rw 3 [fslSepMul_comm]
        nth_rw 1 [fslSepMul_assoc]
        rw [← fslMul_eq_fslSepMul_emp_of_pure (pure_is_in_ico _ _ _)]
        nth_rw 3 [fslMul_comm]; nth_rw 2 [fslMul_assoc]
        rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [fslMin_of_le _ _ ((conservative_entail _ _).mpr (is_in_ico_le_down _ 0 1 Int.one_nonneg))]
        simp only [← fslSepMul_assoc]
        rw [fslSepMul_assoc]
        rw [← fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
        rw [fslSepMul_eq_fslTrue_fslMul_of_pure]
        swap
        · apply pure_fslMul (pure_is_in_ico _ _ _)
          apply pure_fslMul (pure_fslNot pure_fslEquals)
          apply pure_fslMul pure_fslReal
          exact pure_fslMax pure_fslEquals pure_fslEquals
        nth_rw 2 [fslSepMul_eq_fslTrue_fslMul_of_pure]
        swap
        · exact pure_fslMul (pure_is_in_ico _ _ _) pure_fslReal
        apply fslSepMul_mono le_rfl
        nth_rw 6 [fslMul_comm]; nth_rw 2 [← fslMul_assoc]
        nth_rw 2 [fslMul_assoc]; nth_rw 4 [fslMul_comm]; nth_rw 2 [← fslMul_assoc]
        nth_rw 1 [fslMul_assoc]; nth_rw 3 [fslMul_comm]
        simp only [← fslMul_assoc]
        apply fslMul_mono le_rfl
        simp only [conservative_equals, conservative_not, conservative_max, conservative_pointsTo,
          conservative_mul, conservative_min, conservative_sup]
        rw [conservative_entail]
        intro s ⟨h_ico, h_neq, h_12, h_pt⟩
        simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
            exists_prop] at h_ico
        obtain ⟨i, ⟨h_il, h_iu⟩, h_i⟩ := h_ico
        simp only [slNot, slEquals, var, const] at h_neq
        simp only [slPointsTo, add, var] at h_pt
        obtain ⟨l, h_l, h_heap⟩ := h_pt
        apply And.intro
        · simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
            exists_prop]
          use i
          apply And.intro (And.intro ?_ h_iu) h_i
          rw [← Int.zero_add 1, Int.add_one_le_iff]
          apply lt_of_le_of_ne h_il
          qify
          rw [h_i]
          exact (Ne.symm h_neq)
        · rw [slExists_apply]
          have : ∃ n : ℕ, n = i := by {
            use i.toNat
            exact Int.toNat_of_nonneg h_il
          }
          obtain ⟨n, h_n⟩ := this
          use n
          apply And.intro
          · simp only [slEquals, var, const]
            rw [← h_i, ← h_n]
            norm_cast
          · right
            cases h_12
            case inl h_1 =>
              left
              simp only [slPointsTo, add, var, const]
              use l
              apply And.intro
              · rw [h_l, ← h_i, ← h_n]
                norm_cast
              · simp only [slEquals, var, const] at h_1
                rw [h_heap, h_1]
            case inr h_2 =>
              right
              simp only [slPointsTo, add, var, const]
              use l
              apply And.intro
              · rw [h_l, ← h_i, ← h_n]
                norm_cast
              · simp only [slEquals, var, const] at h_2
                rw [h_heap, h_2]

theorem channel_sound₃ (y : ℕ) (p : unitInterval) :
    ⊢ [[rInv y]]
    ⦃ ⁅is_in_ico "y2" 1 y⁆ ⬝ <exp (constP p) (var "y2")> ⊔ ⁅var "y2" === const 0⁆ ⦄
    "y2" ≔ dec (var "y2")
    ⦃⁅is_in_ico "y2" 0 ↑y⁆ ⬝ <exp (constP p) (inc $ var "y2")>
      ⊔ ~⁅<leq (const 0) (var "y2")>⁆ ⊓ ⁅is_in_ico "y2" (-1) ↑y⁆ ⦄ := by
  apply safeTuple_monotonicty
    `[fsl| (⁅is_in_ico "y2" 0 ↑y⁆ ⬝ <exp (constP p) (inc $ var "y2")>
      ⊔ ~⁅<leq (const 0) (var "y2")>⁆ ⊓ ⁅is_in_ico "y2" (-1) ↑y⁆)("y2" ↦ (dec $ var "y2"))]
    _ ?_ le_rfl
  swap
  · simp only [Int.reduceNeg, fslSubst_of_fslMax, fslSubst_of_fslMul, fslSubst_of_fslIverson,
      fslSubst_of_fslReal, substProp_of_exp, substProp_of_constP, substVal_of_inc, substVal_of_var,
      fslSubst_of_fslMin, fslSubst_of_fslNot, substProp_of_slExp, substBool_of_leq, substVal_of_const,
      substProp_ico_dec_var, substProp_ico_dec_var', Nat.cast_add, Nat.cast_one]
    rw [entailment_iff_pi_le, fslMax_le_iff]
    apply And.intro
    · apply le_fslMax
      left
      apply fslMul_mono
      · rw [conservative_entail]
        intro s h
        simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
          exists_prop] at h
        simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
          exists_prop]
        obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h
        use i
        apply And.intro ?_ h_eq
        apply And.intro h_l
        apply lt_trans h_u
        exact Int.lt_succ ↑y
      · intro s
        simp only [fslReal, exp, var, Rat.cast_nonneg, constP, inc, dec, sub_add_cancel, le_refl]
    · apply le_fslMax
      right
      rw [conservative_not, conservative_min, conservative_entail]
      intro s h
      simp only [slEquals, var, const] at h
      apply And.intro
      · intro h_leq
        simp only [slExp, leq, const, dec, var, sub_nonneg, decide_eq_true_eq] at h_leq
        apply h_leq.not_lt
        rw [h]
        exact rfl
      · simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
          exists_prop]
        use 0
        apply And.intro ?_ h.symm
        apply And.intro le_rfl
        exact Int.succ_ofNat_pos y
  · apply safeTuple_assign
    apply Set.not_mem_subset rInv_subset
    decide

theorem channel_sound (y : ℕ) (p : unitInterval) :
    ⊢ [[rInv y]]
    ⦃⁅is_in_ico "y2" 0 y⁆ ⬝ <exp (constP p) (inc $ var "y2")>
      ⊔ ~⁅<leq (const 0) (var "y2")>⁆ ⊓ ⁅is_in_ico "y2" (-1) y⁆ ⦄
    channel p
    ⦃ fTrue ⦄ := by
  apply safeTuple_monotonicty
    _
    `[fsl| ⁅is_in_ico "y2" (-1) y⁆]
    le_rfl
  · intro s
    simp only [Int.reduceNeg, fslTrue]
    exact unitInterval.le_one'
  apply safeTuple_while `[fsl| ⁅is_in_ico "y2" 0 y⁆ ⬝ <exp (constP p) (inc $ var "y2")>]
  · rw [entailment_iff_pi_le, fslMax_le_iff]
    apply And.intro
    · apply le_fslMax
      left
      rw [fslMul_assoc]
      apply fslMul_mono ?_ le_rfl
      rw [conservative_mul, conservative_entail]
      intro s h
      apply And.intro
      · simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
          exists_prop] at h
        obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h
        simp only [slExp, leq, const, var, decide_eq_true_eq]
        rw [← h_eq]
        exact Rat.num_nonneg.mp h_l
      · exact h
    · apply le_fslMax
      right
      rw [conservative_not, fslIverson_fslMin_eq_fslIverson_fslMul]
      exact le_rfl
  · apply safeTuple_seq _ (channel_sound₁ y p)
    apply safeTuple_monotonicty
      `[fsl|  ⁅<eq (var "x2") (const 0)>⁆ ⬝ (⁅is_in_ico "y2" 0 y⁆ ⬝ <exp (constP p) (inc $ var "y2")>
                ⊔ ~⁅<leq (const 0) (var "y2")>⁆ ⊓ ⁅is_in_ico "y2" (-1) y⁆)
              ⊔ ~⁅<eq (var "x2") (const 0)>⁆ ⬝ (⁅is_in_ico "y2" 0 y⁆ ⬝ <exp (constP p) (inc $ var "y2")>
                ⬝ ((var "x2" === const 1) ⊔ (var "x2" === const 2)))]
      _ ?_ le_rfl
    swap
    · rw [fslMul_fslMax_distr, fslMul_fslMax_distr]
      apply fslMax_le_fslMax
      · rw [fslMul_fslMax_distr]
        apply le_fslMax
        left
        nth_rw 2 [fslMul_comm]
        rw [fslMul_assoc, fslMul_assoc]
        apply fslMul_mono ?_ le_rfl
        rw [fslMul_comm]
        apply fslMul_mono ?_ le_rfl
        rw [conservative_equals, conservative_entail]
        intro s h
        simp only [slExp, eq, var, const, decide_eq_true_eq]
        simp only [slEquals, var, const] at h
        exact h
      · nth_rw 2 [fslMul_fslMax_distr]
        rw [conservative_not]
        nth_rw 2 [← fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [fslMul_fslMax_distr, fslMul_fslMax_distr]
        rw [entailment_iff_pi_le, le_fslMin_iff]
        apply And.intro
        · rw [entailment_iff_pi_le, fslMax_le_iff]
          apply And.intro
          · rw [fslMul_assoc, fslMul_comm]
            apply fslMul_le_of_le
            rw [conservative_equals, conservative_entail]
            intro s h
            simp only [slNot, slExp, eq, var, const, decide_eq_true_eq]
            simp only [slEquals, var, const] at h
            simp only [h, one_ne_zero, not_false_eq_true]
          · rw [fslMul_assoc, fslMul_comm]
            apply fslMul_le_of_le
            rw [conservative_equals, conservative_entail]
            intro s h
            simp only [slNot, slExp, eq, var, const, decide_eq_true_eq]
            simp only [slEquals, var, const] at h
            simp only [h, OfNat.ofNat_ne_zero, not_false_eq_true]
        · rw [entailment_iff_pi_le, fslMax_le_iff]
          apply And.intro
          · apply le_fslMax
            left
            exact le_rfl
          · apply le_fslMax
            right
            exact le_rfl
    apply safeTuple_conditionalBranching (safeTuple_skip _ _)
    apply safeTuple_seq _ ?_ (channel_sound₃ y p)
    apply safeTuple_monotonicty
      `[fsl| <constP p> ⬝ (((var "y2" === const 0) ⊓ ⁅is_in_ico "y2" 0 y⁆ ⊓
                  ((var "x2" === const 1) ⊔ (var "x2" === const 2)))
                  ⊔ (~(var "y2" === const 0) ⬝ ⁅is_in_ico "y2" 0 y⁆ ⬝ <exp (constP p) (var "y2")>
                      ⬝ ((var "x2" === const 1) ⊔ (var "x2" === const 2))))
          + ~<constP p> ⬝ fFalse]
      _ ?_ le_rfl
    swap
    · rw [fslMul_fslFalse, fslAdd_fslFalse]
      nth_rw 2 [fslMul_fslMax_distr]
      nth_rw 1 [is_in_ico_eq_or_first _ (Int.ofNat_zero_le y)]
      rw [← conservative_max]
      rw [fslMul_comm, fslMul_fslMax_distr]
      rw [fslMax_comm]
      apply fslMax_le_fslMax
      · rw [conservative_equals, conservative_equals, conservative_max]
        rw [← fslMin_assoc, fslMin_comm, fslIverson_fslMin_eq_fslIverson_fslMul]
        nth_rw 3 [fslMul_comm]
        nth_rw 2 [← fslMul_assoc]
        nth_rw 2 [fslMul_comm]
        rw [← fslMul_assoc]
        apply fslMul_mono le_rfl
        rw [conservative_equals, fslIverson_fslMin_eq_fslIverson_fslMul]
        nth_rw 2 [fslMul_comm]
        rw [fslMul_comm, ← fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [Int.cast_zero, Int.cast_natCast]
        nth_rw 1 [← fslMin_self (`[fsl| ⁅(var "y2" === const 0) ∧ ¬(const 0 === const y)⁆])]
        rw [fslMin_assoc, fslIverson_fslMin_eq_fslIverson_fslMul,
          fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [fslMul_comm]
        apply fslMul_mono
        · intro s
          simp only [fslMul, fslIverson, slEquals, var, const, fslReal, constP]
          rw [unitInterval.iteOneZero_eq_ite]
          split_ifs
          case pos h_zero =>
            obtain ⟨h_zero, h_neq⟩ := h_zero
            simp only [slEquals, var, const] at h_zero
            simp only [exp, inc, var, Rat.cast_add, Rat.cast_one, constP, mul_dite, one_mul,
              mul_one]
            rw [dif_pos]
            · unfold unitInterval.rpow
              simp only [NNReal.coe_mk, NNReal.rpow_eq_pow, NNReal.coe_rpow]
              conv => left; left; rw [h_zero]
              simp only [Rat.cast_zero, zero_add, Real.rpow_one, Subtype.coe_eta, le_refl]
            · simp only [h_zero, Rat.cast_zero, zero_add, zero_le_one]
          case neg h_nzero =>
            simp only [zero_mul, zero_le]
        · rw [← fslIverson_fslMin_eq_fslIverson_fslMul]
          simp only [conservative_min, conservative_max, conservative_entail]
          rintro s ⟨h_eq, h_neq⟩
          apply And.intro h_eq
          simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
            exists_prop]
          simp only [slEquals, var, const] at h_eq
          simp only [slNot, slEquals, const] at h_neq
          use 0
          apply And.intro ?_ h_eq.symm
          apply And.intro le_rfl
          norm_cast
          norm_cast at h_neq
          exact lt_of_le_of_ne (Nat.zero_le y) h_neq
      · simp only [zero_add, Int.cast_zero]
        rw [fslMul_assoc]
        nth_rw 2 [fslMul_comm]
        rw [← fslMul_assoc]
        nth_rw 6 [fslMul_comm]
        nth_rw 3 [fslMul_assoc]
        nth_rw 6 [fslMul_comm]
        nth_rw 2 [← fslMul_assoc]
        nth_rw 3 [fslMul_comm]
        nth_rw 1 [← fslMul_assoc]
        apply fslMul_mono le_rfl
        rw [← fslMul_assoc]
        nth_rw 3 [fslMul_comm]
        nth_rw 4 [fslMul_comm]
        rw [← fslMul_assoc]
        rw [fslMul_assoc, conservative_equals, conservative_not, conservative_mul]
        intro s
        simp only [fslMul, fslReal, fslIverson]
        rw [unitInterval.iteOneZero_eq_ite]
        split_ifs
        case pos h =>
          simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists,
            Set.mem_Ico, exists_prop] at h
          obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h
          rw [unitInterval.iteOneZero_pos]
          swap
          · apply And.intro
            · simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists,
                Set.mem_Ico, exists_prop]
              use i
              apply And.intro ?_ h_eq
              apply And.intro ?_ h_u
              exact le_trans Int.one_nonneg h_l
            · simp only [slNot, slEquals, var, const]
              rw [← h_eq]
              intro h
              apply h_l.not_lt
              qify
              rw [h]
              rfl
          · simp only [exp, inc, var, Rat.cast_add, Rat.cast_one, constP, mul_one, Rat.cast_nonneg,
              mul_dite, one_mul]
            rw [dif_pos, dif_pos]
            swap
            · rw [← h_eq]
              qify at h_l
              apply le_trans ?_ h_l
              rfl
            swap
            · rw [← h_eq]
              rw [Rat.cast_intCast]
              have : 1 ≤ i + 1 := Int.le_add_one h_l
              rify at this
              apply le_trans ?_ this
              exact zero_le_one' ℝ
            rw [unitInterval.mul_rpow_eq_rpow_inc]
            apply le_of_eq
            apply congrArg
            rw [← NNReal.coe_inj]
            simp only [NNReal.coe_mk, NNReal.coe_add, NNReal.coe_one]
        case neg h =>
          simp only [mul_zero, zero_le]
    exact safeTuple_probabilisticBranching (channel_sound₂ y p) safeTuple_false_left
