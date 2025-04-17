import Init.Data.Int.Order
import InvLimDiss.CFSL
import InvLimDiss.SL.ClassicalProofrules
import InvLimDiss.Examples.SyntaxHelp
import InvLimDiss.SL.Framing.VarApprox

open Syntax

noncomputable def init (y : ℕ) : Program String :=
  [Prog| "l" ≔ const 0; "y1" ≔ dec $ const y; "y2" ≔ dec $ const y; "y3" ≔ dec $ const y]

noncomputable def producer : Program String :=
  [Prog| while leq (const 0) (var "y1") begin
    pif half then "x1" ≔ (const 1) else "x1" ≔ (const 2) fi;
    add (var "z1") (var "y1") *≔ (var "x1");
    "y1" ≔ dec <| var "y1"
  fi]

noncomputable def channel (p : unitInterval) : Program String :=
  [Prog| while leq (const 0) (var "y2") begin
    "x2" ≔* add (var "z1") (var "y2");
    if eq (var "x2") (const 0) then
      skip
    else
      pif constP p then
        add (var "z2") (var "y2") *≔ var "x2"
      else
        add (var "z2") (var "y2") *≔ const (-1)
      fi;
      "y2" ≔ dec <| var "y2"
    fi
  fi]

noncomputable def consumer : Program String :=
  [Prog| while leq (const 0) (var "y3") begin
    "x3" ≔* add (var "z2") (var "y3");
    if eq (var "x3") (const 0) then
      skip
    else
      if eq (var "x3") (const (-1)) then
        skip
      else
        "l" ≔ inc (var "l")
      fi;
      "y2" ≔ dec <| var "y2"
    fi
  fi]

noncomputable def producerConsumer (y : ℕ) (p : unitInterval) : Program String :=
  [Prog| [[init y]]; ([[producer]] || [[channel p]] || [[consumer]])]



open CFSL FSL SL

noncomputable def is_in_ico (v : String) (lower upper : ℤ) : StateProp String :=
  `[sl| ∃ (i : Set.Ico lower upper). const i === var v]

theorem substProp_ico_neq {v v' : String} (h : v ≠ v') :
    substProp (is_in_ico v l u) v' e = is_in_ico v l u := by
  funext s
  rw [← iff_eq_eq]
  apply Iff.intro
  · intro h_ico
    simp only [substProp, is_in_ico, State.substituteStack, slExists_apply, Subtype.exists,
      Set.mem_Ico, exists_prop] at h_ico
    obtain ⟨i, h_bound, h_eq⟩ := h_ico
    simp only [is_in_ico, slExists_apply, Subtype.exists, Set.mem_Ico, exists_prop]
    use i, h_bound
    simp only [slEquals, const, var, State.substituteVar, if_neg h.symm] at h_eq
    exact h_eq
  · intro h_ico
    simp only [is_in_ico, slExists_apply, Subtype.exists, Set.mem_Ico, exists_prop] at h_ico
    simp only [substProp, is_in_ico, State.substituteStack, slExists_apply, Subtype.exists,
      Set.mem_Ico, exists_prop]
    obtain ⟨i, h_bound, h_eq⟩ := h_ico
    use i, h_bound
    simp only [slEquals, const, var] at h_eq
    simp only [slEquals, const, var, State.substituteVar, if_neg h.symm]
    exact h_eq

theorem substProp_ico_eq_dec_upper (v : String) (l : ℤ) (u : ℕ) (h : l < u) :
    substProp (is_in_ico v l u) v (dec $ const u) = slTrue := by
  funext
  rw [← iff_eq_eq]
  apply Iff.intro
  · exact fun a ↦ rfl
  · intro _
    simp only [substProp, is_in_ico, State.substituteStack, slExists_apply, slEquals, const, var,
      State.substituteVar, ↓reduceIte, Subtype.exists, Set.mem_Ico, exists_prop]
    use u-1
    simp only [sub_lt_self_iff, zero_lt_one, and_true, Int.cast_sub, Int.cast_one]
    apply And.intro
    · exact Int.le_sub_one_of_lt h
    · rfl

theorem substProp_ico_dec_var (v : String) (y : ℕ):
    substProp (is_in_ico v (-1) ↑y) v (dec (var v))
    = is_in_ico v 0 ↑(y+1) := by
  funext s
  rw [← iff_eq_eq]
  apply Iff.intro
  · intro h
    simp only [substProp, is_in_ico, Int.reduceNeg, State.substituteStack, dec, var, slExists_apply,
      slEquals, const, State.substituteVar, ↓reduceIte, Subtype.exists, Set.mem_Ico,
      exists_prop] at h
    obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h
    simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Nat.cast_add,
      Nat.cast_one, Set.mem_Ico, exists_prop]
    use i+1
    apply And.intro
    · apply And.intro
      · rw [Int.le_add_iff_sub_le, zero_sub]
        exact h_l
      · rw [add_lt_add_iff_right]
        exact h_u
    · rw [Int.cast_add, Int.cast_one, h_eq, sub_add_cancel]
  · intro h
    simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Nat.cast_add,
      Nat.cast_one, Set.mem_Ico, exists_prop] at h
    simp only [substProp, is_in_ico, Int.reduceNeg, State.substituteStack, dec, var, slExists_apply,
      slEquals, const, State.substituteVar, ↓reduceIte, Subtype.exists, Set.mem_Ico, exists_prop]
    obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h
    use i-1
    apply And.intro
    · apply And.intro
      · rw [neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
        exact h_l
      · rw [Int.sub_lt_iff]
        exact h_u
    · rw [Int.cast_sub, Int.cast_one, sub_left_inj]
      exact h_eq

theorem substProp_ico_le_up (v : String) (l : ℤ) {y y' : ℤ} (h : y ≤ y') :
    (is_in_ico v l y) ⊢ (is_in_ico v l y') := by
  intro s h_ico
  simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
    exists_prop] at h_ico
  simp only [is_in_ico, slExists_apply, slEquals, const, var, Subtype.exists, Set.mem_Ico,
    exists_prop]
  obtain ⟨i, ⟨h_l, h_u⟩, h_eq⟩ := h_ico
  use i
  apply And.intro ?_ h_eq
  apply And.intro h_l
  exact lt_of_lt_of_le h_u h

theorem neg_one_le_nat (n : ℕ) : (-1 : ℤ) < n := by
  apply lt_of_lt_of_le
  · apply Int.neg_neg_of_pos
    exact Int.zero_lt_one
  · exact Int.ofNat_zero_le n


noncomputable def rInv (y : ℕ) : StateRV String :=
  `[fsl| [⋆] i ∈ { ... y}. ((add (var "z1") (const i) ↦ const 0)
                          ⊔ (add (var "z1") (const i) ↦ const 1)
                          ⊔ (add (var "z1") (const i) ↦ const 2))
       ⋆ [⋆] i ∈ { ... y}. ((add (var "z2") (const i) ↦ const 0)
                          ⊔ (add (var "z2") (const i) ↦ const 1)
                          ⊔ (add (var "z2") (const i) ↦ const 2))]

theorem rInv_subset : varRV (rInv y) ⊆ {"z1", "z2"} := by sorry

lemma Set.inter_empty_iff {A B : Set String} : A ∩ B = ∅ ↔ ∀ s, (s ∈ A → ¬ s ∈ B) := by
  apply Iff.intro
  · intro h s h_A
    rw [Set.ext_iff] at h
    obtain h := (h s).mp
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, imp_false, not_and] at h
    apply h
    exact h_A
  · intro h
    apply Set.ext
    intro s
    apply Iff.intro
    · simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, imp_false, not_and]
      intro h_A
      exact h s h_A
    · simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, IsEmpty.forall_iff]

noncomputable def post_init (y : ℕ) (p : unitInterval) : StateRV String :=
  `[fsl|⁅is_in_ico "y1" (-1) y⁆
    ⋆ (⁅is_in_ico "y2" 0 y⁆ ⬝ <exp (constP p) (var "y2")>
      ⊔ ~⁅<leq (const 0) (var "y2")>⁆ ⊓ ⁅is_in_ico "y2" (-1) y⁆)
    ⋆ (⁅is_in_ico "y3" (-1) y⁆ ⊓ var "l" === sub (dec $ const y) (var "y3"))]

theorem init_sound (y : ℕ) (p : unitInterval) :
    ⊢ emp
    ⦃<exp (constP p) (dec $ const y)> ⋆ [[rInv y]]⦄
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
      simp? [fslSubst_of_fslSepMul, fslSubst_of_fslTrue, fslSubst_of_fslMax, fslSubst_of_fslMul,
        fslSubst_of_fslMin, fslSubst_of_fslIverson, substProp_of_slExp, substBool_of_leq,
        substVal_of_const, ne_eq, String.reduceEq, not_false_eq_true, substVal_of_var_neq,
        substBool_of_lt, fslSubst_of_fslReal, substProp_of_exp, substProp_of_constP,
        substVal_of_inc, fslSubst_of_fslNot, substVal_of_var, fslSubst_of_fslEquals,
        substVal_of_sub, substVal_of_dec, inc_dec_ident, substProp_ico_neq, substProp_ico_eq_dec_upper]
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
    · unfold rInv
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

syntax "match_strings" : tactic

macro_rules
| `(tactic| match_strings) =>
    `(tactic|
      intro h;
      simp only [varValue_of_var, varValue_of_const, h];
      simp;
      intro h;
      simp at h;
      simp only [varValue_of_var, varValue_of_const, h];
      simp
    )

theorem var_disjoint₁ (y : ℕ) (p : unitInterval) :
    wrtProg producer ∩
      (varProg (channel p) ∪ varProg consumer ∪ varRV `[fsl| fTrue ]
      ∪ varRV `[fsl| var "l" === const ↑y ] ∪ varRV (rInv y))
    = ∅ := by
  sorry
  -- unfold producer channel consumer
  -- simp only [wrtProg, Set.union_self, Set.union_singleton, insert_emptyc_eq, varProg,
  --   ne_eq, Set.singleton_union, Set.union_empty, Set.union_insert, Set.mem_union,
  --   Set.mem_insert_iff, Set.mem_setOf_eq, String.reduceEq, false_or, true_or, Set.insert_eq_of_mem,
  --   varBool_of_leq, varProb_of_constP, varValue_of_var, varValue_of_dec, varValue_of_const,
  --   varValue_of_inc, varRV_of_fslTrue]
  -- rw [Set.inter_empty_iff]
  -- intro v h
  -- simp only [ne_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq, not_or,
  --   not_exists, Decidable.not_not]
  -- have h_z2y2 : v ∉ varValue (add (var "z2") (var "y2")) := by
  --   apply Set.not_mem_subset varValue_of_add; apply Or.elim h; match_strings
  -- have h_z2y3 : v ∉ varValue (add (var "z2") (var "y3")) := by
  --   apply Set.not_mem_subset varValue_of_add; apply Or.elim h; match_strings
  -- have h_0y2 : v ∉ varBool (leq (const 0) (var "y2")) := by
  --   apply Set.not_mem_subset varBool_of_leq; apply Or.elim h; match_strings
  -- have h_0y3 : v ∉ varBool (leq (const 0) (var "y3")) := by
  --   apply Set.not_mem_subset varBool_of_leq; apply Or.elim h; match_strings
  -- have h_z1y2 : v ∉ varValue (add (var "z1") (var "y2")) := by
  --   apply Set.not_mem_subset varValue_of_add; apply Or.elim h; match_strings
  -- have h_x20 : v ∉ varBool (eq (var "x2") (const 0)) := by
  --   apply Set.not_mem_subset varBool_of_eq; apply Or.elim h; match_strings
  -- have h_x30 : v ∉ varBool (eq (var "x3") (const 0)) := by
  --   apply Set.not_mem_subset varBool_of_eq; apply Or.elim h; match_strings
  -- have h_x3n1 : v ∉ varBool (eq (var "x3") (const (-1))) := by
  --   apply Set.not_mem_subset varBool_of_eq; apply Or.elim h; match_strings
  -- have h_ly : v ∉ varRV `[fsl| var "l" === const ↑y ] := by
  --   apply Set.not_mem_subset varRV_of_fslEquals; apply Or.elim h; match_strings
  -- have h_rinv : v ∉ varRV (rInv y) := by
  --   unfold rInv
  --   apply Set.not_mem_subset varRV_of_fslSepMul
  --   simp only [Set.mem_union, not_or]
  --   apply And.intro
  --   repeat {
  --     apply Set.not_mem_subset varRV_of_fslBigSepMul
  --     simp only [Set.mem_setOf_eq, not_exists, not_and]
  --     intro x _
  --     apply Set.not_mem_subset varRV_of_fslMax
  --     simp only [Set.mem_union, not_or]
  --     apply And.intro
  --     · apply Set.not_mem_subset varRV_of_fslPointsTo
  --       simp only [Set.mem_union, not_or]
  --       apply And.intro
  --       · apply Set.not_mem_subset varValue_of_add; apply Or.elim h; match_strings
  --       · rw [varValue_of_const]; simp only [Set.mem_empty_iff_false, not_false_eq_true]
  --     · apply Set.not_mem_subset varRV_of_fslMax
  --       simp only [Set.mem_union, not_or]
  --       apply And.intro
  --       repeat {
  --         apply Set.not_mem_subset varRV_of_fslPointsTo
  --         simp only [Set.mem_union, not_or]
  --         apply And.intro
  --         · apply Set.not_mem_subset varValue_of_add; apply Or.elim h; match_strings
  --         · rw [varValue_of_const]; simp only [Set.mem_empty_iff_false, not_false_eq_true]
  --       }
  --   }
  -- apply And.intro ?_ h_rinv
  -- apply And.intro ?_ h_ly
  -- apply And.intro
  -- · apply Or.elim h; match_strings
  -- · apply And.intro
  --   · apply And.intro
  --     · apply Or.elim h; match_strings
  --     · apply And.intro h_0y2
  --       apply And.intro
  --       · apply And.intro ?_ h_z1y2
  --         apply Or.elim h; match_strings
  --       · apply And.intro h_x20
  --         apply And.intro ?_ h_z2y2
  --         apply And.intro
  --         · apply Or.elim h; match_strings
  --         · apply And.intro (fun a ↦ a) h_z2y2
  --   · apply And.intro h_0y3
  --     apply And.intro
  --     · apply And.intro ?_ h_z2y3
  --       apply Or.elim h; match_strings
  --     · apply And.intro h_x30 h_x3n1

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
  sorry

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
    apply substProp_ico_le_up
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
  swap
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


theorem channel_sound (y : ℕ) (p : unitInterval) :
    ⊢ [[rInv y]]
    ⦃⁅is_in_ico "y2" 0 y⁆ ⬝ <exp (constP p) (var "y2")>
      ⊔ ~⁅<leq (const 0) (var "y2")>⁆ ⊓ ⁅is_in_ico "y2" (-1) y⁆ ⦄
    channel p
    ⦃ fTrue ⦄ := sorry

theorem consumer_sound (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃⁅is_in_ico "y3" (-1) y⁆ ⊓ var "l" === sub (dec $ const y) (var "y3")⦄
  consumer
  ⦃ var "l" === const ↑y ⦄ := sorry

theorem producerConsumer_sound (y : ℕ) (p : unitInterval) :
    ⊢ emp
    ⦃<exp (constP p) (dec $ const y)> ⋆ [[rInv y]]⦄
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
