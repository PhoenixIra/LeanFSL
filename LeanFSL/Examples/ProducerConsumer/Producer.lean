import LeanFSL.Examples.ProducerConsumer.Basic

open Syntax CFSL FSL SL

theorem producer_sound₁ (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃ ⁅is_in_ico "y1" 0 ↑y⁆ ⦄
    pif half then "x1" ≔ const 1 else "x1" ≔ const 2 fi
    ⦃ ((var "x1" === const 1) ⊔ (var "x1" === const 2)) ⊓ ⁅is_in_ico "y1" 0 ↑y⁆⦄ := by
  apply safeTuple_monotonicty
    `[fsl| (<half> ⬝ (((var "x1" === const 1) ⊔ (var "x1" === const 2))
              ⊓ ⁅is_in_ico "y1" 0 ↑y⁆)("x1" ↦ const 1))
         + (~<half> ⬝ (((var "x1" === const 1) ⊔ (var "x1" === const 2))
              ⊓ ⁅is_in_ico "y1" 0 ↑y⁆)("x1" ↦ const 2))]
    _ ?_ le_rfl
  swap
  · simp only [fslSubst_of_fslMin, fslSubst_of_fslMax, fslSubst_of_fslEquals, substVal_of_var,
      substVal_of_const, fslEquals_rfl, fslTrue_fslMax, fslSubst_of_fslIverson, fslTrue_fslMin,
      fslMax_fslTrue]
    rw [substProp_ico_neq (by decide), substProp_ico_neq (by decide), fslAdd_weighted_self]
    exact le_rfl
  · apply safeTuple_probabilisticBranching
    · apply safeTuple_assign
      apply Set.not_mem_subset rInv_subset
      decide
    · apply safeTuple_assign
      apply Set.not_mem_subset rInv_subset
      decide

theorem producer_sound₂ (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃ ((var "x1" === const 1) ⊔ (var "x1" === const 2)) ⊓ ⁅is_in_ico "y1" 0 ↑y⁆ ⦄
    add (var "z1") (var "y1") *≔ var "x1"
    ⦃ ⁅is_in_ico "y1" 0 ↑y⁆ ⦄ := by
  apply safeTuple_atom
  · simp only [Atom.atomicProgram]
  · apply safeTuple_monotonicty
      `[fsl| (S (q : ℚ). add (var "z1") (var "y1") ↦ q)
        ⋆ (add (var "z1") (var "y1") ↦ var "x1" -⋆ ⁅is_in_ico "y1" 0 ↑y⁆ ⋆ [[rInv y]])]
      _ ?_ le_rfl (safeTuple_mutate _)
    rw [fslMin_fslMax_right, fslSepMul_comm, fslSepMul_fslMax_distr]
    rw [entailment_iff_pi_le, fslMax_le_iff]
    apply And.intro
    · nth_rw 1 [rInv]
      nth_rw 1 [← fslMin_self (`[fsl| ⁅is_in_ico "y1" 0 y⁆])]
      rw [fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [conservative_equals, fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [fslSepMul_comm, fslMul_assoc]
      rw [fslMul_comm, fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
      nth_rw 2 [fslSepMul_comm]
      rw [fslSepMul_assoc]
      nth_rw 2 [← fslSepMul_assoc]
      rw [← fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
      nth_rw 2 [← fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [rInv1, ico_fslBigSepMul, ← rInv1_wo]
      rw [fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
      rw [fslSepMul_assoc, fslSepMul_assoc]
      nth_rw 3 [fslSepMul_comm]
      rw [←fslSepMul_assoc, ←fslSepMul_assoc]
      apply fslSepMul_mono
      · simp only [conservative_equals, conservative_pointsTo, conservative_max, conservative_min,
          conservative_sup]
        rw [conservative_entail]
        intro s h
        rw [slExists_apply] at h
        rw [slExists_apply]
        obtain ⟨i, h_eq, h_v⟩ := h
        simp only [slEquals] at h_eq
        obtain h_0 | h_1 | h_2 := h_v
        · use 0
          rw [slPointsTo, add] at h_0
          obtain ⟨l, h_l, h_heap⟩ := h_0
          rw [← h_eq] at h_l
          rw [slPointsTo, add]
          use l, h_l
          rw [const] at h_heap
          exact h_heap
        · use 1
          rw [slPointsTo, add] at h_1
          obtain ⟨l, h_l, h_heap⟩ := h_1
          rw [← h_eq] at h_l
          rw [slPointsTo, add]
          use l, h_l
          rw [const] at h_heap
          exact h_heap
        · use 2
          rw [slPointsTo, add] at h_2
          obtain ⟨l, h_l, h_heap⟩ := h_2
          rw [← h_eq] at h_l
          rw [slPointsTo, add]
          use l, h_l
          rw [const] at h_heap
          exact h_heap
      · rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
        rw [← fslSepMul_assoc]
        nth_rw 2 [← fslSepMul_assoc]
        nth_rw 4 [fslSepMul_comm]
        nth_rw 2 [fslSepMul_assoc]
        nth_rw 1 [fslSepMul_assoc]
        unfold rInv
        nth_rw 2 [fslSepMul_assoc]
        apply fslSepMul_mono ?_ le_rfl
        rw [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
        nth_rw 2 [← fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [rInv1, ico_fslBigSepMul, ← rInv1_wo]
        nth_rw 2 [fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [← fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
        nth_rw 3 [fslSepMul_comm]
        nth_rw 1 [fslSepMul_assoc]
        nth_rw 1 [fslSepMul_assoc]
        apply fslSepMul_mono ?_ le_rfl
        nth_rw 1 [← fslSepMul_assoc]
        simp only [conservative_mul, conservative_emp, conservative_min, conservative_pointsTo,
          conservative_sepMul, conservative_equals, conservative_max, conservative_sup]
        rw [conservative_entail]
        -- let's give up staying in SL...
        rintro s ⟨heap₁, heap₂, ⟨h_eq, h_ico⟩, h, h_disjoint, h_union⟩
        obtain ⟨heap₂₁, heap₂₂, ⟨h_ico', h_emp⟩, h_points, h₂_disjoint, h₂_union⟩ := h
        use heap₁, heap₂, h_ico
        apply And.intro ?_ ⟨h_disjoint, h_union⟩
        rw [slExists_apply]
        by_cases ∃ i : ℕ, i = s.stack "y1"
        case pos h =>
          obtain ⟨i, h_i⟩ := h
          use i
          apply And.intro
          · simp only [slEquals, var, const, h_i]
          · right; left
            simp only [slEmp] at h_emp
            rw [h_emp, State.emptyHeap_union] at h₂_union
            rw [h₂_union] at h_points
            obtain ⟨l, h_l, h_heap⟩ := h_points
            use l
            apply And.intro
            · simp only [add, var, const]
              simp only [add, var] at h_l
              rw [h_l, h_i]
            · simp only [slEquals, var, const] at h_eq
              rw [h_heap]
              simp only [var, const]
              rw [h_eq]
        case neg h =>
          exfalso
          simp only [not_exists] at h
          rw [is_in_ico, slExists_apply] at h_ico
          obtain ⟨i, h_i⟩ := h_ico
          simp only [slEquals, const, var] at h_i
          apply h i.val.toNat
          rw [← h_i]
          norm_cast
          apply Int.toNat_of_nonneg
          exact i.prop.left
    · nth_rw 1 [rInv]
      nth_rw 1 [← fslMin_self (`[fsl| ⁅is_in_ico "y1" 0 y⁆])]
      rw [fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [conservative_equals, fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [fslSepMul_comm, fslMul_assoc]
      rw [fslMul_comm, fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
      nth_rw 2 [fslSepMul_comm]
      rw [fslSepMul_assoc]
      nth_rw 2 [← fslSepMul_assoc]
      rw [← fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
      nth_rw 2 [← fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [rInv1, ico_fslBigSepMul, ← rInv1_wo]
      rw [fslIverson_fslMin_eq_fslIverson_fslMul]
      rw [fslMul_eq_emp_fslSepMul_of_pure (pure_is_in_ico _ _ _)]
      rw [fslSepMul_assoc, fslSepMul_assoc]
      nth_rw 3 [fslSepMul_comm]
      rw [←fslSepMul_assoc, ←fslSepMul_assoc]
      apply fslSepMul_mono
      · simp only [conservative_equals, conservative_pointsTo, conservative_max, conservative_min,
          conservative_sup]
        rw [conservative_entail]
        intro s h
        rw [slExists_apply] at h
        rw [slExists_apply]
        obtain ⟨i, h_eq, h_v⟩ := h
        simp only [slEquals] at h_eq
        obtain h_0 | h_1 | h_2 := h_v
        · use 0
          rw [slPointsTo, add] at h_0
          obtain ⟨l, h_l, h_heap⟩ := h_0
          rw [← h_eq] at h_l
          rw [slPointsTo, add]
          use l, h_l
          rw [const] at h_heap
          exact h_heap
        · use 1
          rw [slPointsTo, add] at h_1
          obtain ⟨l, h_l, h_heap⟩ := h_1
          rw [← h_eq] at h_l
          rw [slPointsTo, add]
          use l, h_l
          rw [const] at h_heap
          exact h_heap
        · use 2
          rw [slPointsTo, add] at h_2
          obtain ⟨l, h_l, h_heap⟩ := h_2
          rw [← h_eq] at h_l
          rw [slPointsTo, add]
          use l, h_l
          rw [const] at h_heap
          exact h_heap
      · rw [entailment_iff_pi_le, le_fslSepDiv_iff_fslSepMul_le]
        rw [← fslSepMul_assoc]
        nth_rw 2 [← fslSepMul_assoc]
        nth_rw 4 [fslSepMul_comm]
        nth_rw 2 [fslSepMul_assoc]
        nth_rw 1 [fslSepMul_assoc]
        unfold rInv
        nth_rw 2 [fslSepMul_assoc]
        apply fslSepMul_mono ?_ le_rfl
        rw [fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
        nth_rw 2 [← fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [rInv1, ico_fslBigSepMul, ← rInv1_wo]
        nth_rw 2 [fslIverson_fslMin_eq_fslIverson_fslMul]
        rw [← fslSepMul_eq_fslTrue_fslMul_of_pure (pure_is_in_ico _ _ _)]
        nth_rw 3 [fslSepMul_comm]
        nth_rw 1 [fslSepMul_assoc]
        nth_rw 1 [fslSepMul_assoc]
        apply fslSepMul_mono ?_ le_rfl
        nth_rw 1 [← fslSepMul_assoc]
        simp only [conservative_mul, conservative_emp, conservative_min, conservative_pointsTo,
          conservative_sepMul, conservative_equals, conservative_max, conservative_sup]
        rw [conservative_entail]
        -- let's give up staying in SL...
        rintro s ⟨heap₁, heap₂, ⟨h_eq, h_ico⟩, h, h_disjoint, h_union⟩
        obtain ⟨heap₂₁, heap₂₂, ⟨h_ico', h_emp⟩, h_points, h₂_disjoint, h₂_union⟩ := h
        use heap₁, heap₂, h_ico
        apply And.intro ?_ ⟨h_disjoint, h_union⟩
        rw [slExists_apply]
        by_cases ∃ i : ℕ, i = s.stack "y1"
        case pos h =>
          obtain ⟨i, h_i⟩ := h
          use i
          apply And.intro
          · simp only [slEquals, var, const, h_i]
          · right; right
            simp only [slEmp] at h_emp
            rw [h_emp, State.emptyHeap_union] at h₂_union
            rw [h₂_union] at h_points
            obtain ⟨l, h_l, h_heap⟩ := h_points
            use l
            apply And.intro
            · simp only [add, var, const]
              simp only [add, var] at h_l
              rw [h_l, h_i]
            · simp only [slEquals, var, const] at h_eq
              rw [h_heap]
              simp only [var, const]
              rw [h_eq]
        case neg h =>
          exfalso
          simp only [not_exists] at h
          rw [is_in_ico, slExists_apply] at h_ico
          obtain ⟨i, h_i⟩ := h_ico
          simp only [slEquals, const, var] at h_i
          apply h i.val.toNat
          rw [← h_i]
          norm_cast
          apply Int.toNat_of_nonneg
          exact i.prop.left

theorem producer_sound₃ (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃ ⁅is_in_ico "y1" 0 ↑y⁆ ⦄
    "y1" ≔ dec (var "y1")
    ⦃ ⁅is_in_ico "y1" (-1) ↑y⁆ ⦄ := by
  apply safeTuple_monotonicty
    `[fsl| ⁅is_in_ico "y1" (-1) ↑y⁆("y1" ↦ dec $ var "y1")]
    _ ?_ le_rfl
  swap
  · simp only [Int.reduceNeg, fslSubst_of_fslIverson]
    rw [substProp_ico_dec_var, conservative_entail]
    apply is_in_ico_le_up
    simp only [Nat.cast_add, Nat.cast_one, le_add_iff_nonneg_right, zero_le_one]
  · apply safeTuple_assign
    apply Set.not_mem_subset rInv_subset
    decide

theorem producer_sound (y : ℕ) :
    ⊢ [[rInv y]] ⦃ ⁅is_in_ico "y1" (-1) y⁆ ⦄ producer ⦃ fTrue ⦄ := by
  apply safeTuple_monotonicty
    _
    `[fsl| ⁅is_in_ico "y1" (-1) y⁆]
    le_rfl
  · intro s
    simp only [Int.reduceNeg, fslTrue]
    exact unitInterval.le_one'
  apply safeTuple_while `[fsl| ⁅is_in_ico "y1" 0 y⁆]
  · intro s
    rw [fslMax, Pi.sup_apply]
    cases eq_or_ne (s.stack "y1") (-1)
    case inl h_neg =>
      rw [le_sup_iff]
      right
      simp only [fslIverson, Int.reduceNeg, fslMul, fslNot, unitInterval.sym_iteOneZero_eq]
      nth_rw 2 [unitInterval.iteOneZero_pos]
      · simp only [Int.reduceNeg, one_mul, le_refl]
      · simp only [slExp, leq, const, var, h_neg, Left.nonneg_neg_iff, decide_eq_true_eq, not_le,
        zero_lt_one]
    case inr h_pos =>
      rw [le_sup_iff]
      left
      simp only [fslIverson, Int.reduceNeg, fslMul]
      rw [unitInterval.iteOneZero_le]
      intro h
      simp only [is_in_ico, Int.reduceNeg, slExists_apply, slEquals, const, var, Subtype.exists,
        Set.mem_Ico, exists_prop] at h
      obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h
      have h_0 : 0 ≤ i := by {
          apply lt_of_le_of_ne h_l
          qify
          rw [h_eq]
          exact h_pos.symm
      }
      rw [unitInterval.iteOneZero_pos, unitInterval.iteOneZero_pos]
      · simp only [mul_one, le_refl]
      · simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
          exists_prop]
        use i, ⟨h_0, h_u⟩
      · simp only [slExp, leq, const, var, decide_eq_true_eq]
        rw [← h_eq]
        qify at h_0
        exact h_0
  · apply safeTuple_seq _ (producer_sound₁ y)
    exact safeTuple_seq _ (producer_sound₂ y) (producer_sound₃ y)
