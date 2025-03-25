import InvLimDiss.CFSL
import InvLimDiss.Examples.SyntaxHelp
import InvLimDiss.SL.Framing.VarApprox

open Syntax

noncomputable def init (y : ℕ) : Program String :=
  [Prog| "l" ≔ const 0; "y1" ≔ dec $ const y; "y2" ≔ dec $ const y; "y3" ≔ dec $ const y]

noncomputable def producer : Program String :=
  [Prog| while leq (const 0) (var "y1") begin
    pif half then "x1" ≔ (const 1) else "x1" ≔ (const 2) fi;
    add (var "z1") (var "z1") *≔ (var "x1");
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



open CFSL FSL

noncomputable def rInv (y : ℕ) : StateRV String :=
  `[fsl| [⋆] i ∈ { ... y}. ((add (var "z1") (const i) ↦ const 0)
                          ⊔ (add (var "z1") (const i) ↦ const 1)
                          ⊔ (add (var "z1") (const i) ↦ const 2))
       ⋆ [⋆] i ∈ { ... y}. ((add (var "z2") (const i) ↦ const 0)
                          ⊔ (add (var "z2") (const i) ↦ const 1)
                          ⊔ (add (var "z2") (const i) ↦ const 2))]

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
  `[fsl|fTrue
    ⋆ ((⁅<leq (const 0) (var "y2")>⁆ ⊓ ⁅<lt (var "y2") (const y)>⁆) ⬝ <exp (constP p) (inc $ var "y2")>
      ⊔ ~⁅<leq (const 0) (var "y2")>⁆)
    ⋆ (⁅<leq (const 0) (var "y3")>⁆ ⊓ ⁅<lt (var "y3") (const y)>⁆
        ⊓ ((var "l") === (sub (const y) (inc $ var "y3")))
      ⊔ ~⁅<leq (const 0) (var "y3")>⁆ ⊓ (var "l") === const y)]

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
      simp only [fslSubst_of_fslSepMul, fslSubst_of_fslTrue, fslSubst_of_fslMax, fslSubst_of_fslMul,
        fslSubst_of_fslMin, fslSubst_of_fslIverson, substProp_of_slExp, substBool_of_leq,
        substVal_of_const, ne_eq, String.reduceEq, not_false_eq_true, substVal_of_var_neq,
        substBool_of_lt, fslSubst_of_fslReal, substProp_of_exp, substProp_of_constP,
        substVal_of_inc, fslSubst_of_fslNot, substVal_of_var, fslSubst_of_fslEquals,
        substVal_of_sub, substVal_of_dec, inc_dec_ident]
      nth_rw 1 [← fslReal_fslSepMul_fslTrue, fslSepMul_comm]
      apply fslSepMul_mono le_rfl
      nth_rw 1 [← fslReal_fslSepMul_fslTrue]
      apply fslSepMul_mono
      · apply le_fslMax
        cases y
        case zero =>
          right
          intro s
          simp only [fslReal, CharP.cast_eq_zero, fslNot, fslIverson,
            unitInterval.sym_iteOneZero_eq]
          rw [unitInterval.iteOneZero_pos]
          · exact unitInterval.le_one'
          · simp only [SL.slExp, leq, dec, le_sub_self_iff, decide_eq_true_eq, not_le, zero_lt_one]
        case succ y =>
          left
          rw [← fslReal_fslMul_fslTrue, fslMul_comm]
          apply fslMul_mono
          · rw [entailment_iff_pi_le, le_fslMin_iff]
            apply And.intro
            · intro s
              simp only [fslTrue, fslIverson, Nat.cast_add, Nat.cast_one]
              rw [unitInterval.iteOneZero_pos]
              simp only [SL.slExp, leq, const, dec, add_sub_cancel_right, Nat.cast_nonneg,
                decide_true]
            · intro s
              simp only [fslTrue, fslIverson, Nat.cast_add, Nat.cast_one]
              rw [unitInterval.iteOneZero_pos]
              simp only [SL.slExp, lt, dec, const, add_sub_cancel_right, lt_add_iff_pos_right,
                zero_lt_one, decide_true]
          · intro s
            simp only [fslReal, Nat.cast_add, Nat.cast_one, fslMul, fslTrue, one_mul, le_refl]
      · apply le_fslMax
        cases y
        case zero =>
          right
          rw [entailment_iff_pi_le, le_fslMin_iff]
          apply And.intro
          · intro s
            simp only [fslTrue, fslNot, fslIverson, CharP.cast_eq_zero,
              unitInterval.sym_iteOneZero_eq]
            rw [unitInterval.iteOneZero_pos]
            simp only [SL.slExp, leq, dec, le_sub_self_iff, decide_eq_true_eq, not_le, zero_lt_one]
          · intro s
            simp only [fslTrue, fslEquals, CharP.cast_eq_zero, unitInterval.iteOneZero_true,
              le_refl]
        case succ y =>
          left
          rw [entailment_iff_pi_le, le_fslMin_iff]
          apply And.intro
          · intro s
            simp only [fslTrue, fslIverson, Nat.cast_add, Nat.cast_one]
            rw [unitInterval.iteOneZero_pos]
            simp only [SL.slExp, leq, const, dec, add_sub_cancel_right, Nat.cast_nonneg,
              decide_true]
          · rw [entailment_iff_pi_le, le_fslMin_iff]
            apply And.intro
            · intro s
              simp only [fslTrue, fslIverson, Nat.cast_add, Nat.cast_one]
              rw [unitInterval.iteOneZero_pos]
              simp only [SL.slExp, lt, dec, const, add_sub_cancel_right, lt_add_iff_pos_right,
                zero_lt_one, decide_true]
            · intro s
              simp only [fslTrue, fslEquals, Nat.cast_add, Nat.cast_one]
              rw [unitInterval.iteOneZero_pos]
              simp only [const, sub, sub_self]
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
  unfold producer channel consumer
  simp only [wrtProg, Set.union_self, Set.union_singleton, insert_emptyc_eq, varProg,
    ne_eq, Set.singleton_union, Set.union_empty, Set.union_insert, Set.mem_union,
    Set.mem_insert_iff, Set.mem_setOf_eq, String.reduceEq, false_or, true_or, Set.insert_eq_of_mem,
    varBool_of_leq, varProb_of_constP, varValue_of_var, varValue_of_dec, varValue_of_const,
    varValue_of_inc, varRV_of_fslTrue]
  rw [Set.inter_empty_iff]
  intro v h
  simp only [ne_eq, Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq, not_or,
    not_exists, Decidable.not_not]
  have h_z2y2 : v ∉ varValue (add (var "z2") (var "y2")) := by
    apply Set.not_mem_subset varValue_of_add; apply Or.elim h; match_strings
  have h_z2y3 : v ∉ varValue (add (var "z2") (var "y3")) := by
    apply Set.not_mem_subset varValue_of_add; apply Or.elim h; match_strings
  have h_0y2 : v ∉ varBool (leq (const 0) (var "y2")) := by
    apply Set.not_mem_subset varBool_of_leq; apply Or.elim h; match_strings
  have h_0y3 : v ∉ varBool (leq (const 0) (var "y3")) := by
    apply Set.not_mem_subset varBool_of_leq; apply Or.elim h; match_strings
  have h_z1y2 : v ∉ varValue (add (var "z1") (var "y2")) := by
    apply Set.not_mem_subset varValue_of_add; apply Or.elim h; match_strings
  have h_x20 : v ∉ varBool (eq (var "x2") (const 0)) := by
    apply Set.not_mem_subset varBool_of_eq; apply Or.elim h; match_strings
  have h_x30 : v ∉ varBool (eq (var "x3") (const 0)) := by
    apply Set.not_mem_subset varBool_of_eq; apply Or.elim h; match_strings
  have h_x3n1 : v ∉ varBool (eq (var "x3") (const (-1))) := by
    apply Set.not_mem_subset varBool_of_eq; apply Or.elim h; match_strings
  have h_ly : v ∉ varRV `[fsl| var "l" === const ↑y ] := by
    apply Set.not_mem_subset varRV_of_fslEquals; apply Or.elim h; match_strings
  have h_rinv : v ∉ varRV (rInv y) := by
    unfold rInv
    apply Set.not_mem_subset varRV_of_fslSepMul
    simp only [Set.mem_union, not_or]
    apply And.intro
    repeat {
      apply Set.not_mem_subset varRV_of_fslBigSepMul
      simp only [Set.mem_setOf_eq, not_exists, not_and]
      intro x _
      apply Set.not_mem_subset varRV_of_fslMax
      simp only [Set.mem_union, not_or]
      apply And.intro
      · apply Set.not_mem_subset varRV_of_fslPointsTo
        simp only [Set.mem_union, not_or]
        apply And.intro
        · apply Set.not_mem_subset varValue_of_add; apply Or.elim h; match_strings
        · rw [varValue_of_const]; simp only [Set.mem_empty_iff_false, not_false_eq_true]
      · apply Set.not_mem_subset varRV_of_fslMax
        simp only [Set.mem_union, not_or]
        apply And.intro
        repeat {
          apply Set.not_mem_subset varRV_of_fslPointsTo
          simp only [Set.mem_union, not_or]
          apply And.intro
          · apply Set.not_mem_subset varValue_of_add; apply Or.elim h; match_strings
          · rw [varValue_of_const]; simp only [Set.mem_empty_iff_false, not_false_eq_true]
        }
    }
  apply And.intro ?_ h_rinv
  apply And.intro ?_ h_ly
  apply And.intro
  · apply Or.elim h; match_strings
  · apply And.intro
    · apply And.intro
      · apply Or.elim h; match_strings
      · apply And.intro h_0y2
        apply And.intro
        · apply And.intro ?_ h_z1y2
          apply Or.elim h; match_strings
        · apply And.intro h_x20
          apply And.intro ?_ h_z2y2
          apply And.intro
          · apply Or.elim h; match_strings
          · apply And.intro (fun a ↦ a) h_z2y2
    · apply And.intro h_0y3
      apply And.intro
      · apply And.intro ?_ h_z2y3
        apply Or.elim h; match_strings
      · apply And.intro h_x30 h_x3n1

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

theorem producer_sound (y : ℕ) :
   ⊢ [[rInv y]] ⦃ fTrue ⦄ producer ⦃ fTrue ⦄ := sorry

theorem channel_sound (y : ℕ) (p : unitInterval) :
    ⊢ [[rInv y]]
    ⦃(⁅<leq (const 0) (var "y2")>⁆ ⊓ ⁅<lt (var "y2") (const ↑y)>⁆)
        ⬝ <exp (constP p) (inc (var "y2"))>
      ⊔ ~⁅<leq (const 0) (var "y2")>⁆ ⦄
    channel p
    ⦃ fTrue ⦄ := sorry

theorem consumer_sound (y : ℕ) :
    ⊢ [[rInv y]]
    ⦃⁅<leq (const 0) (var "y3")>⁆ ⊓ ⁅<lt (var "y3") (const ↑y)>⁆
        ⊓ (var "l" === sub (const ↑y) (inc (var "y3")))
      ⊔ ~⁅<leq (const 0) (var "y3")>⁆ ⊓ var "l" === const ↑y ⦄
  consumer
  ⦃ var "l" === const ↑y ⦄ := sorry

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
