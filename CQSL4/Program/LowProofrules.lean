import CQSL4.Program.Semantics

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
    ↔ (c' = `[Program| ↓] ∧ a = Action.deterministic ∧
        ∃ val, (e s.stack) = some val ∧ s.stack v ≠ none ∧ substituteStack s v val = s')
      ∨ (c' = `[Program| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ ((e s.stack) = none ∨ s.stack v = none)) := by
  rw [programSmallStepSemantics, assignSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, true_and, false_and, or_false, iteOneZero_eq_one_def]
  | error => simp only [ne_eq, false_and, true_and, false_or, iteOneZero_eq_one_def]
  | _ => simp only [zero_ne_one, ne_eq, false_and, or_self]

theorem assign_mem_zero_one : programSmallStepSemantics `[Program| v ≔ e] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, assignSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem manipulate_eq_one_iff : programSmallStepSemantics `[Program| e_loc *≔ e_val] s a c' s' = 1
    ↔ (c' = `[Program| ↓] ∧ a = Action.deterministic ∧
        ∃ l, e_loc s.stack = some l ∧ s.heap l ≠ none ∧
        ∃ val, e_val s.stack = some val ∧ substituteHeap s l val = s')
      ∨ (c' = `[Program| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ (e_loc s.stack = none ∨ (∃ l, e_loc s.stack = some l ∧ s.heap l = none) ∨ e_val s.stack = none))
    := by
  rw [programSmallStepSemantics, manipulateSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, true_and, false_and, or_false,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [iteOneZero_eq_one_def, ne_eq, false_and, true_and, false_or]
  | _ => simp only [zero_ne_one, ne_eq, false_and, or_self]

theorem manipulate_mem_zero_one : programSmallStepSemantics `[Program| e_loc *≔ e_val] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, manipulateSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem lookup_eq_one_iff : programSmallStepSemantics `[Program| v ≔* e] s a c' s' = 1
    ↔ (c' = `[Program| ↓] ∧ a = Action.deterministic ∧
        ∃ l, e s.stack = some l ∧ s.stack v ≠ none ∧
        ∃ val, s.heap l = some val ∧ substituteStack s v val = s')
      ∨ (c' = `[Program| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ (e s.stack = none ∨ s.stack v = none ∨ ∃ l, e s.stack = some l ∧ s.heap l = none))
    := by
  rw [programSmallStepSemantics, lookupSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, true_and, false_and, or_false,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [iteOneZero_eq_one_def, ne_eq, false_and, true_and, false_or]
  | _ => simp only [zero_ne_one, ne_eq, false_and, or_self]

theorem lookup_mem_zero_one : programSmallStepSemantics `[Program| v ≔* e] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, lookupSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem compareAndSet_eq_one_iff : programSmallStepSemantics `[Program| v ≔ cas (e_loc, e_cmp, e_val)] s a c' s' = 1
    ↔ (c' = `[Program| ↓] ∧ a = Action.deterministic ∧
        ∃ l, e_loc s.stack = some l ∧ ∃ cmp, e_cmp s.stack = some cmp
        ∧ ∃ new_val, e_val s.stack = some new_val
        ∧ ∃ old_val, s.heap l = some old_val ∧ s.stack v ≠ none
        ∧ ((old_val = cmp ∧ substituteStack (substituteHeap s l new_val) v 1 = s')
          ∨ old_val ≠ cmp ∧ substituteStack s v 0 = s'))
      ∨ (c' = `[Program| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ (e_loc s.stack = none
          ∨ e_cmp s.stack = none ∨ e_val s.stack = none
          ∨ ∃ l, e_loc s.stack = some l ∧ s.heap l = none)) := by
  rw [programSmallStepSemantics, compareAndSetSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, true_and, false_and, or_false,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [iteOneZero_eq_one_def, ne_eq, false_and, true_and, false_or]
  | _ => simp only [zero_ne_one, ne_eq, false_and, or_self]

theorem compareAndSet_mem_zero_one :
    programSmallStepSemantics `[Program| v ≔ cas(e_loc, e_cmp , e_val)] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, compareAndSetSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
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
    ↔ (c' = `[Program| ↓] ∧ a = Action.deterministic ∧
      ∃ l, e s.stack = some l ∧ isAlloc s l n ∧ freeHeap s l n = s')
    ∨ (c' = `[Program| ↯] ∧ a = Action.deterministic ∧ s = s'
    ∧ (e s.stack = none ∨ ∃ l, e s.stack = some l ∧ ¬isAlloc s l n)) := by
  rw [programSmallStepSemantics, freeSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, true_and, false_and, or_false,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [iteOneZero_eq_one_def, ne_eq, false_and, true_and, false_or]
  | _ => simp only [zero_ne_one, ne_eq, false_and, or_self]

theorem free_mem_zero_one :
    programSmallStepSemantics `[Program| free(e, n)] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, freeSmallStepSemantics]
  cases c' with
  | terminated => simp only [ne_eq, mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | error => simp only [mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  | _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem probabilisticChoice_iff_left_of_eq_left (h_c : c₁ = c') (h_i : 0 ≠ i ∧ i ≠ 1):
    programSmallStepSemantics (Program.probabilisticChoice e c₁ c₂) s a c' s' = i
    ↔ c' ≠ `[Program| ↯] ∧ s = s' ∧ a = Action.deterministic ∧ e s.stack = some i := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  cases c' with
  | error =>
    simp only [iteOneZero_def]
    apply Iff.intro
    · intro h
      cases h with
      | inl h => exfalso; exact h_i.left h.left.symm
      | inr h => exfalso; exact h_i.right h.left
    · intro h
      exact (h.left rfl).elim
  | skip' =>
    simp only [ne_eq, not_false_eq_true]
    apply Iff.intro
    · intro h
      apply And.intro trivial
      by_cases h' : a = Action.deterministic ∧ s = s'
      · rw [if_pos h'] at h
        have : ∃ j, e s.stack = j := by use e s.stack
        let ⟨j, h_j⟩ := this; clear this
        rw [h_j] at h
        cases j with
        | none => simp only at h; exfalso; exact h_i.left h
        | some j =>
          simp only at h
          sorry
        ·
