import CQSL4.Program.Semantics
import CQSL4.Util

open Syntax Program Notation Semantics unitInterval Set State Classical

theorem skip_eq_one_iff : programSmallStepSemantics `[Program| skip] s a c' s' = 1
    ↔ c' = `[Program| ↓] ∧ a = Action.deterministic ∧ s = s' := by
  apply Iff.intro
  · intro h
    rw [programSmallStepSemantics, skipSmallStepSemantics, iteOneZero_eq_one_def] at h
    exact h
  · intro h
    rw [programSmallStepSemantics, skipSmallStepSemantics, iteOneZero_eq_one_def]
    exact h

theorem skip_mem_zero_one : programSmallStepSemantics `[Program| skip] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, skipSmallStepSemantics,
    mem_insert_iff, mem_singleton_iff, iteOneZero_eq_one_def, iteOneZero_eq_zero_def, ← imp_iff_not_or, imp_self]
  trivial

theorem terminated_eq_zero : programSmallStepSemantics `[Program| ↓] s a c' s' = 0 := by
  simp only [programSmallStepSemantics, Pi.zero_apply]

theorem error_eq_zero : programSmallStepSemantics `[Program| ↯] s a c' s' = 0 := by
  simp only [programSmallStepSemantics, Pi.zero_apply]

theorem assign_eq_one_iff : programSmallStepSemantics `[Program| v ≔ e] s a c' s' = 1
    ↔ (c' = `[Program| ↓] ∧ a = Action.deterministic ∧ substituteStack s v (e s.stack) = s')
    := by
  rw [programSmallStepSemantics, assignSmallStepSemantics]
  cases c' with
  | terminated => simp only [iteOneZero_eq_one_def, true_and]
  | _ => simp only [zero_ne_one, false_and]

theorem assign_mem_zero_one : programSmallStepSemantics `[Program| v ≔ e] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, assignSmallStepSemantics]
  cases c' with
  | terminated => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem manipulate_eq_one_iff : programSmallStepSemantics `[Program| e_loc *≔ e_val] s a c' s' = 1
    ↔ (c' = `[Program| ↓] ∧ a = Action.deterministic ∧ s.heap (e_loc s.stack) ≠ none
        ∧ substituteHeap s (e_loc s.stack) (e_val s.stack) = s')
      ∨ (c' = `[Program| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ s.heap (e_loc s.stack) = none)
    := by
  rw [programSmallStepSemantics, manipulateSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, iteOneZero_eq_one_def, true_and, false_and, or_false]
  | error => simp only [iteOneZero_eq_one_def, ne_eq, false_and, true_and, false_or]
  | _ => simp only [zero_ne_one, ne_eq, false_and, or_self]

theorem manipulate_mem_zero_one : programSmallStepSemantics `[Program| e_loc *≔ e_val] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, manipulateSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem lookup_eq_one_iff : programSmallStepSemantics `[Program| v ≔* e] s a c' s' = 1
    ↔ (c' = `[Program| ↓] ∧ a = Action.deterministic ∧
        ∃ val, s.heap (e s.stack) = some val ∧ substituteStack s v val = s')
      ∨ (c' = `[Program| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ s.heap (e s.stack) = none)
    := by
  rw [programSmallStepSemantics, lookupSmallStepSemantics]
  cases c' with
  | terminated => simp only [iteOneZero_eq_one_def, true_and, false_and, or_false]
  | error => simp only [iteOneZero_eq_one_def, false_and, true_and, false_or]
  | _ => simp only [zero_ne_one, false_and, or_self]

theorem lookup_mem_zero_one : programSmallStepSemantics `[Program| v ≔* e] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, lookupSmallStepSemantics]
  cases c' with
  | terminated => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem compareAndSet_eq_one_iff : programSmallStepSemantics `[Program| v ≔ cas (e_loc, e_cmp, e_val)] s a c' s' = 1
    ↔ (c' = `[Program| ↓] ∧ a = Action.deterministic
      ∧ ∃ old_val, s.heap (e_loc s.stack) = some old_val
        ∧ ((old_val = (e_cmp s.stack) ∧ substituteStack (substituteHeap s (e_loc s.stack) (e_val s.stack)) v 1 = s')
          ∨ old_val ≠ (e_cmp s.stack) ∧ substituteStack s v 0 = s'))
      ∨ (c' = `[Program| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ s.heap (e_loc s.stack ) = none) := by
  rw [programSmallStepSemantics, compareAndSetSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, iteOneZero_eq_one_def, true_and, false_and, or_false]
  | error => simp only [iteOneZero_eq_one_def, ne_eq, false_and, true_and, false_or]
  | _ => simp only [zero_ne_one, ne_eq, false_and, or_self]

theorem compareAndSet_mem_zero_one :
    programSmallStepSemantics `[Program| v ≔ cas(e_loc, e_cmp , e_val)] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, compareAndSetSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem allocate_eq_one_iff : programSmallStepSemantics `[Program| v ≔ alloc n] s a c' s' = 1
    ↔ (c' = `[Program| ↓] ∧ ∃ m, a = Action.allocation m ∧ isNotAlloc s m n
      ∧ substituteStack (substituteHeap s m n) v m = s') := by
  rw [programSmallStepSemantics, allocateSmallStepSemantics]
  cases c' with
  | terminated => simp only [true_and, iteOneZero_eq_one_def]
  | _ => simp only [false_and, and_false, exists_const, iteOneZero_eq_one_def]

theorem allocate_mem_zero_one :
    programSmallStepSemantics `[Program| v ≔ alloc n] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, allocateSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | _ => simp only [false_and, and_false, exists_const, mem_insert_iff, iteOneZero_eq_zero_def,
    not_false_eq_true, mem_singleton_iff, true_or]

theorem free_eq_one_iff : programSmallStepSemantics `[Program| free(e, n)] s a c' s' = 1
    ↔ (c' = `[Program| ↓] ∧ a = Action.deterministic ∧ isAlloc s (e s.stack ) n ∧ freeHeap s (e s.stack ) n = s')
    ∨ (c' = `[Program| ↯] ∧ a = Action.deterministic ∧ s = s' ∧ ¬isAlloc s (e s.stack ) n) := by
  rw [programSmallStepSemantics, freeSmallStepSemantics]
  cases c' with
  | terminated => simp only [iteOneZero_eq_one_def, true_and, false_and, or_false]
  | error => simp only [iteOneZero_eq_one_def, false_and, true_and, false_or]
  | _ => simp only [zero_ne_one, false_and, or_self]

theorem free_mem_zero_one :
    programSmallStepSemantics `[Program| free(e, n)] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, freeSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem probabilisticChoice_eq_zero_iff :
    programSmallStepSemantics `[Program| pif e then [c₁] else [c₂] end] s a c' s' = 0
    ↔ a ≠ Action.deterministic ∨ s ≠ s'
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ ≠ c'
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ = c' ∧ c₂ ≠ c' ∧ e s.stack = 0
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ = c' ∧ e s.stack = 1 := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  apply Iff.intro
  · intro h
    simp only [ite_eq_right_iff, and_imp] at h
    simp only [ite_def] at h
    cases eq_or_ne a Action.deterministic with
    | inl h_a_eq =>
      cases eq_or_ne s s' with
      | inl h_s_eq =>
        specialize h h_a_eq h_s_eq
        simp only [one_ne_zero, and_false, and_true, false_or] at h
        let ⟨h_c₁₂, h⟩ := h
        cases h with
        | inl h =>
          rw [not_and] at h_c₁₂
          specialize h_c₁₂ h.left
          exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h_a_eq, h_s_eq, h.left, h_c₁₂, h.right⟩
        | inr h =>
          let ⟨h_c₁, h⟩ := h
          cases h with
          | inl h =>
            rw [eq_one_iff_sym_eq_zero] at h
            exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨h_a_eq, h_s_eq, h_c₁, h.left, h.right⟩
          | inr h =>
            exact Or.inr <| Or.inr <| Or.inl ⟨h_a_eq, h_s_eq, h_c₁, h⟩
      | inr h_s_ne =>
        exact Or.inr <| Or.inl h_s_ne
    | inr h_a_ne =>
      exact Or.inl h_a_ne
  · intro h
    cases h with
    | inl h =>
      rw [ite_and, if_neg h]
    | inr h =>
      cases h with
      | inl h =>
        conv => left; congr; rw [and_comm]
        rw [ite_and, if_neg h]
      | inr h =>
        cases h with
        | inl h =>
          let ⟨h_a, h_s, h_c₁, h_c₂⟩ := h; clear h
          rw [if_pos ⟨h_a, h_s⟩, ite_and, if_neg h_c₁, if_neg h_c₁, if_neg h_c₂]
        | inr h =>
          cases h with
          | inl h =>
            let ⟨h_a, h_s, h_c₁, h_c₂, h_e⟩ := h; clear h
            rw [if_pos ⟨h_a, h_s⟩, ite_and, if_pos h_c₁, if_neg h_c₂, if_pos h_c₁]
            exact h_e
          | inr h =>
            let ⟨h_a, h_s, h_c₁, h_c₂, h_e⟩ := h; clear h
            rw [if_pos ⟨h_a, h_s⟩, ite_and, if_neg h_c₁, if_neg h_c₁, if_pos h_c₂, eq_one_iff_sym_eq_zero]
            exact h_e

theorem probabilisticChoice_eq_one_iff:
    programSmallStepSemantics `[Program| pif e then [c₁] else [c₂] end] s a c' s' = 1
    ↔ a = Action.deterministic ∧ s = s' ∧ c₁ = c' ∧ c₂ = c'
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ = c' ∧ c₂ ≠ c' ∧ e s.stack = 1
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ = c' ∧ e s.stack = 0 := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  apply Iff.intro
  · intro h
    simp only [ite_eq_right_iff, and_imp] at h
    simp only [ite_def] at h
    cases h with
    | inl h =>
      let ⟨⟨h_a, h_s⟩, h_c⟩ := h; clear h
      cases h_c with
      | inl h_c =>
        exact Or.inl ⟨h_a, h_s, h_c.left⟩
      | inr h_c =>
        let ⟨h_ne_c₁₂, h_c⟩ := h_c
        cases h_c with
        | inl h_c =>
          let ⟨h_c₁, h_e⟩ := h_c
          rw [not_and] at h_ne_c₁₂
          specialize h_ne_c₁₂ h_c₁
          exact Or.inr <| Or.inl ⟨h_a, h_s, h_c₁, h_ne_c₁₂, h_e⟩
        | inr h_c =>
          let ⟨h_c₁, h_c₂⟩ := h_c; clear h_c
          cases h_c₂ with
          | inl h_c₂ =>
            let ⟨h_c₂, h_e⟩ := h_c₂
            rw [eq_zero_iff_sym_eq_one] at h_e
            exact Or.inr <| Or.inr ⟨h_a, h_s, h_c₁, h_c₂, h_e⟩
          | inr h_c₂ => exfalso; exact zero_ne_one h_c₂.right
    | inr h => exfalso; exact zero_ne_one h.right
  · intro h
    cases h with
    | inl h =>
      let ⟨h_a, h_s, h_c₁, h_c₂⟩ := h
      rw [if_pos ⟨h_a, h_s⟩, if_pos ⟨h_c₁, h_c₂⟩]
    | inr h =>
      cases h with
      | inl h =>
        let ⟨h_a, h_s, h_c₁, h_c₂, h_e⟩ := h
        rw [if_pos ⟨h_a, h_s⟩, ite_and, if_pos h_c₁, if_neg h_c₂, if_pos h_c₁]
        exact h_e
      | inr h =>
        let ⟨h_a, h_s, h_c₁, h_c₂, h_e⟩ := h
        rw [if_pos ⟨h_a, h_s⟩, ite_and, if_neg h_c₁, if_neg h_c₁, if_pos h_c₂, eq_zero_iff_sym_eq_one]
        exact h_e

theorem probabilisticChoice_eq_first_iff (h_stack : e s.stack ≠ 0 ∧ e s.stack ≠ 1):
    programSmallStepSemantics `[Program| pif e then [c₁] else [c₂] end] s a c' s' = e s.stack
    ↔ a = Action.deterministic ∧ s = s' ∧ c₁ = c' ∧ c₂ ≠ c'
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ = c' ∧ e s.stack = σ (e s.stack) := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  apply Iff.intro
  · intro h
    simp only [ite_def] at h
    cases h with
    | inl h =>
      let ⟨⟨h_a, h_s⟩, h_c⟩ := h; clear h
      cases h_c with
      | inl h_c =>
        let ⟨_, h_e⟩ := h_c
        exfalso; exact h_stack.right h_e.symm
      | inr h_c =>
        let ⟨h_c₁₂, h_c⟩ := h_c
        cases h_c with
        | inl h_c₁ =>
          let ⟨h_c₁, _⟩ := h_c₁
          rw [not_and] at h_c₁₂
          specialize h_c₁₂ h_c₁
          exact Or.inl ⟨h_a, h_s, h_c₁, h_c₁₂⟩
        | inr h_c =>
          apply Or.inr
          apply And.intro h_a; apply And.intro h_s
          let ⟨h_c₁, h_c⟩ := h_c
          apply And.intro h_c₁
          cases h_c with
          | inl h_c => exact ⟨h_c.left, h_c.right.symm⟩
          | inr h_c => exfalso; exact h_stack.left h_c.right.symm
    | inr h => exfalso; exact h_stack.left h.right.symm
  · intro h
    cases h with
    | inl h =>
      let ⟨h_a, h_s, h_c₁, h_c₂⟩ := h
      rw [if_pos ⟨h_a, h_s⟩, ite_and, if_pos h_c₁, if_neg h_c₂, if_pos h_c₁]
    | inr h =>
      let ⟨h_a, h_s, h_c₁, h_c₂, h_e⟩ := h
      rw [if_pos ⟨h_a, h_s⟩, ite_and, if_neg h_c₁, if_neg h_c₁, if_pos h_c₂]
      exact h_e.symm

theorem probabilisticChoice_eq_second_iff (h_stack : e s.stack ≠ 0 ∧ e s.stack ≠ 1):
    programSmallStepSemantics `[Program| pif e then [c₁] else [c₂] end] s a c' s' = σ (e s.stack)
    ↔ a = Action.deterministic ∧ s = s' ∧ c₁ = c' ∧ c₂ ≠ c' ∧ e s.stack = σ (e s.stack)
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ = c' := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  apply Iff.intro
  · intro h
    simp only [ite_def] at h
    cases h with
    | inl h =>
      let ⟨⟨h_a, h_s⟩, h_c⟩ := h; clear h
      cases h_c with
      | inl h_c =>
        let ⟨_, h_e⟩ := h_c
        rw [eq_comm, eq_zero_iff_sym_eq_one] at h_e
        exfalso; exact h_stack.left h_e
      | inr h_c =>
        let ⟨h_c₁₂, h_c⟩ := h_c
        cases h_c with
        | inl h_c =>
          apply Or.inl
          apply And.intro h_a; apply And.intro h_s
          let ⟨h_c₁, h_e⟩ := h_c; clear h_c; clear h_c
          apply And.intro h_c₁
          rw [not_and] at h_c₁₂
          specialize h_c₁₂ h_c₁
          exact ⟨h_c₁₂, h_e⟩
        | inr h_c₁ =>
          let ⟨h_c₁, h_c⟩ := h_c₁
          cases h_c with
          | inl h_c₂ => exact Or.inr ⟨h_a, h_s, h_c₁, h_c₂.left⟩
          | inr h_c =>
            exfalso
            let ⟨_, h_e⟩ := h_c; clear h_c; clear h_c
            rw [eq_comm, eq_one_iff_sym_eq_zero] at h_e
            exact h_stack.right h_e
    | inr h =>
      exfalso
      let ⟨_, h_e⟩ := h
      rw [eq_comm, eq_one_iff_sym_eq_zero] at h_e
      exact h_stack.right h_e
  · intro h
    cases h with
    | inl h =>
      let ⟨h_a, h_s, h_c₁, h_c₂, h_e⟩ := h
      rw [if_pos ⟨h_a, h_s⟩, ite_and, if_pos h_c₁, if_neg h_c₂, if_pos h_c₁]
      exact h_e
    | inr h =>
      let ⟨h_a, h_s, h_c₁, h_c₂⟩ := h
      rw [if_pos ⟨h_a, h_s⟩, ite_and, if_neg h_c₁, if_neg h_c₁, if_pos h_c₂]


theorem probabilisticChoice_mem :
    programSmallStepSemantics `[Program| pif e then [c₁] else [c₂] end] s a c' s'
    ∈ ({0, e s.stack, σ (e s.stack), 1} : Set I) := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  simp only [mem_insert_iff, mem_singleton_iff]
  cases eq_or_ne a Action.deterministic with
  | inl h_a =>
    cases eq_or_ne s s' with
    | inl h_s =>
      cases eq_or_ne c₁ c' with
      | inl h_c₁ =>
        cases eq_or_ne c₂ c' with
        | inl h_c₂ =>
          apply Or.inr; apply Or.inr; apply Or.inr
          rw [if_pos ⟨h_a, h_s⟩, if_pos ⟨h_c₁, h_c₂⟩]
        | inr h_c₂ =>
          apply Or.inr; apply Or.inl
          rw [if_pos ⟨h_a, h_s⟩, ite_and, if_pos h_c₁, if_neg h_c₂, if_pos h_c₁]
      | inr h_c₁ =>
        cases eq_or_ne c₂ c' with
        | inl h_c₂ =>
          apply Or.inr; apply Or.inr; apply Or.inl
          rw [if_pos ⟨h_a, h_s⟩, ite_and, if_neg h_c₁, if_neg h_c₁, if_pos h_c₂]
        | inr h_c₂ =>
          apply Or.inl
          rw [if_pos ⟨h_a, h_s⟩, ite_and, if_neg h_c₁, if_neg h_c₁, if_neg h_c₂]
    | inr h_s =>
      apply Or.inl
      rw [ite_and, if_pos h_a, if_neg h_s]
  | inr h_a =>
    apply Or.inl
    rw [ite_and, if_neg h_a]


theorem conditionalChoice_eq_one_iff :
    programSmallStepSemantics `[Program| if b then [c₁] else [c₂] end] s a c' s' = 1
    ↔ a = Action.deterministic ∧ s = s' ∧ (b s.stack ∧ c₁ = c' ∨ ¬ b s.stack ∧ c₂ = c') := by
  rw [programSmallStepSemantics, conditionalChoiceSmallStepSemantics, iteOneZero_eq_one_def]

theorem conditionalChoice_mem :
    programSmallStepSemantics `[Program| if b then [c₁] else [c₂] end] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, conditionalChoiceSmallStepSemantics]
  simp only [Bool.not_eq_true, mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def]
  rw [or_iff_not_imp_left, not_not, imp_self]
  trivial

theorem loop_eq_one_iff :
    programSmallStepSemantics `[Program| while b begin [c] end] s a c' s' = 1
    ↔ a = Action.deterministic ∧ s = s'
    ∧ (b s.stack ∧ c' = `[Program| [c] ; while b begin [c] end]
      ∨ ¬ b s.stack ∧ c' = `[Program| ↓]) := by
  rw [programSmallStepSemantics, loopSmallStepSemantics]
  apply Iff.intro
  · intro h
    cases c' with
    | terminated =>
      simp only [Bool.not_eq_true, iteOneZero_eq_one_def] at h
      let ⟨h_a, h_s, h_e⟩ := h; clear h
      apply And.intro h_a; apply And.intro h_s
      apply Or.inr
      simp only [Bool.not_eq_true, and_true]
      exact h_e
    | sequential c₁ c₂ =>
      simp only [sequential.injEq, iteOneZero_eq_one_def] at h
      let ⟨h_a, ⟨h_c₁, h_c₂⟩, h_s, h_e⟩ := h; clear h
      apply And.intro h_a; apply And.intro h_s
      apply Or.inl
      apply And.intro h_e
      rw [h_c₁, h_c₂]
    | _ => simp only [false_and, and_false, iteOneZero_eq_one_def] at h
  · intro h
    let ⟨h_a, h_s, h_c⟩ := h; clear h
    cases h_c with
    | inl h_c =>
      let ⟨h_e, h_c⟩ := h_c
      rw [h_c]
      simp only [true_and, iteOneZero_eq_one_def]
      exact ⟨h_a, h_s, h_e⟩
    | inr h_c =>
      let ⟨h_e, h_c⟩ := h_c
      rw [h_c]
      simp only [iteOneZero_eq_one_def]
      exact ⟨h_a, h_s, h_e⟩


theorem loop_mem :
    programSmallStepSemantics `[Program| while b begin [c] end] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, loopSmallStepSemantics]
  simp only [Bool.not_eq_true, mem_insert_iff, mem_singleton_iff]
  cases eq_or_ne a Action.deterministic with
  | inl h_a =>
    cases eq_or_ne s s' with
    | inl h_s =>
      cases b s.stack with
      | true =>
        cases c' with
        | terminated =>
          simp only [and_false, iteOneZero_def, not_false_eq_true, and_self, zero_ne_one, or_false,
            one_ne_zero, and_true, or_self]
        | sequential c₁ c₂ =>
          simp only [sequential.injEq, and_true, iteOneZero_def]
          cases eq_or_ne c₁ c with
          | inl h_c₁ =>
            cases eq_or_ne c₂ `[Program| while b begin [c] end] with
            | inl h_c₂ =>
              exact Or.inr <| Or.inr ⟨True.intro, h_a, ⟨h_c₁, h_c₂⟩, h_s⟩
            | inr h_c₂ =>
              apply Or.inl; apply Or.inl
              apply And.intro True.intro
              simp only [not_and, and_imp]
              intro _ _ h_c₂'
              exfalso
              exact h_c₂ h_c₂'
          | inr h_c₁ =>
            apply Or.inl; apply Or.inl
            apply And.intro True.intro
            simp only [not_and, and_imp]
            intro _ h_c₁'
            exfalso
            exact h_c₁ h_c₁'
        | _ =>
          apply Or.inl
          simp only [and_false, iteOneZero_eq_zero_def]
          intro h
          exact h.right.left.elim
      | false =>
        cases c' with
        | terminated =>
          simp only [and_true, iteOneZero_def, not_and, true_and, zero_ne_one, false_and, or_false,
            one_ne_zero, false_or]
          apply Or.inr
          exact ⟨h_a, h_s⟩
        | sequential c₁ c₂ =>
          simp only [sequential.injEq, and_false, iteOneZero_def, not_false_eq_true, and_self,
            zero_ne_one, or_false, one_ne_zero, and_true, or_self]
        | _ =>
          simp only [and_false, and_self, iteOneZero_def, not_false_eq_true, zero_ne_one, or_false,
            one_ne_zero, and_true, or_self]
    | inr h_s =>
      apply Or.inl
      cases c' with
      | terminated =>
        simp only [iteOneZero_def, not_and, Bool.not_eq_false, true_and, zero_ne_one, false_and,
          or_false]
        intro _ h_s'
        exfalso
        exact h_s h_s'
      | sequential c₁ c₂ =>
        simp only [sequential.injEq, iteOneZero_def, not_and, Bool.not_eq_true, and_imp, true_and,
          zero_ne_one, false_and, or_false]
        intro _ _ _ h_s'
        exfalso
        exact h_s h_s'
      | _ =>
        simp only [false_and, and_false, iteOneZero_def, not_false_eq_true, and_self, zero_ne_one,
          or_false]
  | inr h_a =>
    apply Or.inl
    cases c' with
    | terminated =>
      simp only [iteOneZero_def, not_and, Bool.not_eq_false, true_and, zero_ne_one, false_and,
        or_false]
      intro h_a'
      exfalso
      exact h_a h_a'
    | sequential c₁ c₂ =>
      simp only [sequential.injEq, iteOneZero_def, not_and, Bool.not_eq_true, and_imp, true_and,
        zero_ne_one, false_and, or_false]
      intro h_a'
      exfalso
      exact h_a h_a'
    | _ =>
      simp only [false_and, and_false, iteOneZero_def, not_false_eq_true, and_self, zero_ne_one,
        or_false]


theorem sequential_iff :
    programSmallStepSemantics `[Program| [c₁] ; [c₂]] s a c' s' = i
    ↔ (c₁ = `[Program| ↓] ∧ a = Action.deterministic ∧ s = s' ∧ c' = c₂ ∧ i = 1
    ∨ c₁ = `[Program| ↓] ∧ ¬ (a = Action.deterministic ∧ s = s' ∧ c' = c₂) ∧ i = 0)
    ∨ c₁ ≠ `[Program| ↓] ∧ ∃ c₁', c' = `[Program| [c₁'] ; [c₂] ] ∧ programSmallStepSemantics c₁ s a c₁' s' = i
    ∨ c₁ ≠ `[Program| ↓] ∧ ¬ (∃ c₁', c' = `[Program| [c₁'] ; [c₂] ]) ∧ i = 0 := by
  cases c₁ with
  | terminated =>
    rw [programSmallStepSemantics, programSmallStepSemantics]
    simp only [iteOneZero_def, true_and, ne_eq, not_true_eq_false, Pi.zero_apply,
      not_exists, false_and, or_false, exists_and_right]
    apply Iff.intro
    · intro h
      cases h with
      | inl h =>
        let ⟨h_i, h⟩ := h
        apply Or.inr
        exact ⟨h, h_i⟩
      | inr h =>
        let ⟨h_i, h⟩ := h
        apply Or.inl
        exact ⟨h, h_i⟩
    · intro h
      cases h with
      | inl h =>
        let ⟨h_a, h_s, h_c, h_i⟩ := h
        apply Or.inr
        exact ⟨h_i, h_a, h_s, h_c⟩
      | inr h =>
        let ⟨h, h_i⟩ := h
        apply Or.inl
        exact ⟨h_i, h⟩
  | sequential c₁' c₂' =>
    apply Iff.intro
    · intro h
      rw [programSmallStepSemantics] at h
      sorry
    · sorry
  | _ => sorry
