import InvLimDiss.Program.Semantics
import InvLimDiss.Util

/-
This file contains a varity of low level proof rules to ease the use of the
probability transition function in the program semantics. It mainly rewirtes
the program semantics in more logical terms
-/

namespace Semantics

open Syntax Program ProgNotation Semantics unitInterval Set State Classical HeapValue

theorem skip_eq_one_iff : programSmallStepSemantics [Prog| skip] s a c' s' = 1
    ↔ c' = [Prog| ↓] ∧ a = Action.deterministic ∧ s = s' := by
  apply Iff.intro
  · intro h
    rw [programSmallStepSemantics, skipSmallStepSemantics, iteOneZero_eq_one_def] at h
    exact h
  · intro h
    rw [programSmallStepSemantics, skipSmallStepSemantics, iteOneZero_eq_one_def]
    exact h

theorem skip_mem_zero_one : programSmallStepSemantics [Prog| skip] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, skipSmallStepSemantics,
    mem_insert_iff, mem_singleton_iff, iteOneZero_eq_one_def, iteOneZero_eq_zero_def, ← imp_iff_not_or, imp_self]
  trivial

theorem terminated_eq_zero : programSmallStepSemantics [Prog| ↓] s a c' s' = 0 := by
  simp only [programSmallStepSemantics, Pi.zero_apply]

theorem error_eq_zero : programSmallStepSemantics [Prog| ↯] s a c' s' = 0 := by
  simp only [programSmallStepSemantics, Pi.zero_apply]

theorem assign_eq_one_iff : programSmallStepSemantics [Prog| v ≔ e] s a c' s' = 1
    ↔ (c' = [Prog| ↓] ∧ a = Action.deterministic ∧ substituteStack s v (e s.stack) = s')
    := by
  rw [programSmallStepSemantics, assignSmallStepSemantics]
  split
  case h_1 => simp only [iteOneZero_eq_one_def, true_and]
  case h_2 h => simp only [zero_ne_one, false_iff, not_and]; intro h_c; exfalso; exact h h_c

theorem assign_mem_zero_one : programSmallStepSemantics [Prog| v ≔ e] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, assignSmallStepSemantics]
  split
  case h_1 =>
    simp only [mem_insert_iff, iteOneZero_eq_zero_def, not_and, mem_singleton_iff, iteOneZero_eq_one_def]
    by_cases h : substituteStack s v (e s.stack) = s'
    · cases eq_or_ne a Action.deterministic with
      | inr h_a => apply Or.inl; intro h; exfalso; exact h_a h
      | inl h_a => apply Or.inr; exact ⟨h_a, h⟩
    · apply Or.inl; intro _; exact h
  case h_2 _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem manipulate_eq_one_iff : programSmallStepSemantics [Prog| e_loc *≔ e_val] s a c' s' = 1
    ↔ (c' = [Prog| ↓] ∧ a = Action.deterministic ∧ ∃ l : ℕ+, (e_loc s.stack) = l ∧ s.heap l ≠ undef
        ∧ substituteHeap s l (e_val s.stack) = s')
      ∨ (c' = [Prog| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ ((∃ l : ℕ+, (e_loc s.stack) = l ∧ s.heap l = undef) ∨ ¬ (e_loc s.stack).isInt ∨ 0 ≤ (e_loc s.stack)))
    := by
  rw [programSmallStepSemantics, manipulateSmallStepSemantics]
  split
  case h_1 => simp only [ne_eq, iteOneZero_eq_one_def, true_and, false_and, or_false]
  case h_2 => simp only [iteOneZero_eq_one_def, ne_eq, false_and, true_and, false_or]
  case h_3 h_term h_err =>
    simp only [zero_ne_one, ne_eq, false_iff]
    intro h
    cases h with | inl h => exact h_term h.left | inr h => exact h_err h.left

theorem manipulate_mem_zero_one : programSmallStepSemantics [Prog| e_loc *≔ e_val] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, manipulateSmallStepSemantics]
  split
  case h_1 => simp only [ne_eq, mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_2 _ => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_3 _ _ _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem lookup_eq_one_iff : programSmallStepSemantics [Prog| v ≔* e] s a c' s' = 1
    ↔ (c' = [Prog| ↓] ∧ a = Action.deterministic ∧
      ∃ l : ℕ+, l = (e s.stack) ∧ ∃ value, s.heap l = val value ∧ substituteStack s v value = s' )
      ∨ (c' = [Prog| ↯] ∧ a = Action.deterministic ∧ s = s'
      ∧ ((∃ l : ℕ+, (e s.stack) = l ∧ s.heap l = undef) ∨ ¬ (e s.stack).isInt ∨ 0 ≤ (e s.stack)))
    := by
  rw [programSmallStepSemantics, lookupSmallStepSemantics]
  split
  case h_1 => simp only [iteOneZero_eq_one_def, true_and, false_and, or_false]
  case h_2 _ => simp only [iteOneZero_eq_one_def, false_and, true_and, false_or]
  case h_3 _ h_term h_err =>
    simp only [zero_ne_one, false_iff]
    intro h
    cases h with | inl h => exact h_term h.left | inr h => exact h_err h.left

theorem lookup_mem_zero_one : programSmallStepSemantics [Prog| v ≔* e] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, lookupSmallStepSemantics]
  split
  case h_1 => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_2 _ => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_3 _ _ _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem compareAndSet_eq_one_iff : programSmallStepSemantics [Prog| v ≔ cas (e_loc, e_cmp, e_val)] s a c' s' = 1
    ↔ (c' = [Prog| ↓] ∧ a = Action.deterministic
      ∧ ∃ l : ℕ+, l = (e_loc s.stack) ∧ ∃ old_val, s.heap l = val old_val
        ∧ ((old_val = (e_cmp s.stack) ∧ substituteStack (substituteHeap s l (e_val s.stack)) v 1 = s')
          ∨ old_val ≠ (e_cmp s.stack) ∧ substituteStack s v 0 = s'))
      ∨ (c' = [Prog| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ (∃ l : ℕ+, (e_loc s.stack) = l ∧ s.heap l = undef)) := by
  rw [programSmallStepSemantics, compareAndSetSmallStepSemantics]
  split
  case h_1 => simp only [ne_eq, iteOneZero_eq_one_def, true_and, false_and, or_false]
  case h_2 _ => simp only [iteOneZero_eq_one_def, ne_eq, false_and, true_and, false_or]
  case h_3 _ h_term h_err =>
    simp only [zero_ne_one, ne_eq, false_iff]
    intro h
    cases h with | inl h => exact h_term h.left | inr h => exact h_err h.left

theorem compareAndSet_mem_zero_one :
    programSmallStepSemantics [Prog| v ≔ cas(e_loc, e_cmp , e_val)] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, compareAndSetSmallStepSemantics]
  split
  case h_1 => simp only [ne_eq, mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_2 _ => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_3 _ _ _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem allocate_eq_one_iff : programSmallStepSemantics [Prog| v ≔ alloc e] s a c' s' = 1
    ↔ (c' = [Prog| ↓] ∧ ∃ m, a = Action.allocation m ∧ ∃ n : ℕ+, n = e s.stack
      ∧ isNotAlloc s m n ∧ substituteStack (substituteHeap s m n) v m = s')
    ∨ (c' = [Prog| ↯] ∧ a = Action.deterministic ∧ ¬ ∃ n : ℕ+, n = e s.stack) := by
  rw [programSmallStepSemantics, allocateSmallStepSemantics]
  split
  case h_1 => simp only [iteOneZero_eq_one_def, true_and, not_exists, false_and, or_false]
  case h_2 => simp only [not_exists, iteOneZero_eq_one_def, false_and, true_and, false_or]
  case h_3 h_n_term h_n_err =>
    simp only [zero_ne_one, not_exists, false_iff, not_or, not_and, not_forall, Decidable.not_not]
    apply And.intro
    · rintro rfl; exfalso
      apply h_n_term; rfl
    · rintro rfl; exfalso
      apply h_n_err; rfl

theorem allocate_mem_zero_one :
    programSmallStepSemantics [Prog| v ≔ alloc e] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, allocateSmallStepSemantics]
  simp only [not_exists, mem_insert_iff, mem_singleton_iff]
  split
  · by_cases h : ∃ m, a = Action.allocation m ∧ ∃ n : ℕ+, n = e s.stack
      ∧ isNotAlloc s m n ∧ substituteStack (substituteHeap s m n) v m = s'
    case pos => apply Or.inr; rw [iteOneZero_eq_one_def]; exact h
    case neg => apply Or.inl; rw [iteOneZero_eq_zero_def]; exact h
  · by_cases h : a = Action.deterministic ∧ ∀ n : ℕ+, ¬n = e s.stack
    case pos => apply Or.inr; rw [iteOneZero_eq_one_def]; exact h
    case neg => apply Or.inl; rw [iteOneZero_eq_zero_def]; exact h
  · apply Or.inl; rfl

theorem free_eq_one_iff : programSmallStepSemantics [Prog| free(e, n)] s a c' s' = 1
    ↔ (c' = [Prog| ↓] ∧ a = Action.deterministic
      ∧ ∃ l : ℕ+, l = (e s.stack) ∧ isAlloc s l n ∧ freeHeap s l n = s')
    ∨ (c' = [Prog| ↯] ∧ a = Action.deterministic ∧ s = s'
      ∧ (∃ l : ℕ+, (e s.stack) = l ∧ ¬isAlloc s l n ∨ ¬ (e s.stack).isInt ∨ 0 ≤ (e s.stack))) := by
  rw [programSmallStepSemantics, freeSmallStepSemantics]
  split
  case h_1 _ => simp only [iteOneZero_eq_one_def, true_and, false_and, or_false]
  case h_2 _ => simp only [iteOneZero_eq_one_def, false_and, true_and, false_or]
  case h_3 _ h_term h_err =>
    simp only [zero_ne_one, false_iff]
    intro h
    cases h with | inl h => exact h_term h.left | inr h => exact h_err h.left

theorem free_mem_zero_one :
    programSmallStepSemantics [Prog| free(e, n)] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, freeSmallStepSemantics]
  split
  case h_1 _ => simp only [ne_eq, mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_2 _ => simp only [mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_3 => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem probabilisticChoice_eq_zero_iff :
    programSmallStepSemantics [Prog| pif e then [[c₁]] else [[c₂]] fi] s a c' s' = 0
    ↔ a ≠ Action.deterministic ∨ s ≠ s'
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ ≠ c'
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ = c' ∧ c₂ ≠ c' ∧ e s.stack = 0
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ = c' ∧ e s.stack = 1 := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  split
  case isTrue h =>
    obtain ⟨h_a, h_s⟩ := h
    split
    case isTrue h =>
      obtain ⟨h_c₁, h_c₂⟩ := h
      simp only [one_ne_zero, ne_eq, false_iff]
      intro h
      cases h
      case inl h_a' => exact h_a' h_a
      case inr h =>
      cases h
      case inl h_s' => exact h_s' h_s
      case inr h =>
      cases h
      case inl h_c' => exact h_c'.right.right.left h_c₁
      case inr h =>
      cases h
      case inl h => exact h.right.right.right.left h_c₂
      case inr h => exact h.right.right.left h_c₁
    case isFalse h =>
      split
      case isTrue h_c₁ =>
        rw [not_and] at h; specialize h h_c₁
        rename ¬ c₂ = c' => h_c₂
        apply Iff.intro
        case mp => intro h_e; exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h_a, h_s, h_c₁, h_c₂, h_e⟩
        case mpr =>
          intro h
          cases h
          case inl h_a' => exfalso; exact h_a' h_a
          case inr h =>
          cases h
          case inl h_s' => exfalso; exact h_s' h_s
          case inr h =>
          cases h
          case inl h => exfalso; exact h.right.right.left h_c₁
          case inr h =>
          cases h
          case inl h => exact h.right.right.right.right
          case inr h => exfalso; exact h_c₂ h.right.right.right.left
      case isFalse h_c₁ =>
        split
        case isTrue h_c₂ =>
          clear h
          apply Iff.intro
          case mp =>
            intro h
            rw [eq_one_iff_sym_eq_zero] at h
            exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨h_a, h_s, h_c₁, h_c₂, h⟩
          case mpr =>
            intro h
            cases h
            case inl h_a' => exfalso; exact h_a' h_a
            case inr h =>
            cases h
            case inl h_s' => exfalso; exact h_s' h_s
            case inr h =>
            cases h
            case inl h => exfalso; exact h.right.right.right h_c₂
            case inr h =>
            cases h
            case inl h => exfalso; exact h.right.right.right.left h_c₂
            case inr h => rw [eq_one_iff_sym_eq_zero]; exact h.right.right.right.right
        case isFalse h_c₂ =>
          clear h
          simp only [ne_eq, true_iff]
          exact Or.inr <| Or.inr <| Or.inl ⟨h_a, h_s, h_c₁, h_c₂⟩
  case isFalse h =>
    simp only [ne_eq, true_iff]
    simp only [not_and_or] at h
    cases h
    case inl h => exact Or.inl h
    case inr h => exact Or.inr <| Or.inl h

theorem probabilisticChoice_eq_one_iff:
    programSmallStepSemantics [Prog| pif e then [[c₁]] else [[c₂]] fi] s a c' s' = 1
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
    programSmallStepSemantics [Prog| pif e then [[c₁]] else [[c₂]] fi] s a c' s' = e s.stack
    ↔ a = Action.deterministic ∧ s = s' ∧ c₁ = c' ∧ c₂ ≠ c'
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ = c' ∧ e s.stack = σ (e s.stack) := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  split
  case isTrue h =>
    obtain ⟨h_a, h_s⟩ := h
    split
    case isTrue h =>
      obtain ⟨h_c₁, h_c₂⟩ := h
      apply Iff.intro
      case mp =>
        intro h_e
        exfalso
        exact h_stack.right h_e.symm
      case mpr =>
        intro h
        cases h
        case inl h => exfalso; exact h.right.right.right h_c₂
        case inr h => exfalso; exact h.right.right.left h_c₁
    case isFalse h =>
      split
      case isTrue h_c₁ =>
        rw [not_and] at h; specialize h h_c₁; rename ¬ c₂ = c' => h_c₂
        simp only [ne_eq, true_iff]
        exact Or.inl ⟨h_a, h_s, h_c₁, h_c₂⟩
      case isFalse h_c₁ =>
        split
        case isTrue h_c₂ =>
          clear h
          apply Iff.intro
          case mp => intro h; exact Or.inr ⟨h_a, h_s, h_c₁, h_c₂, h.symm⟩
          case mpr =>
            intro h
            cases h
            case inl h => exfalso; exact h.right.right.right h_c₂
            case inr h => exact h.right.right.right.right.symm
        case isFalse h_c₂ =>
          clear h
          apply Iff.intro
          case mp => intro h; exfalso; exact h_stack.left h.symm
          case mpr =>
            intro h; cases h with
              | inl h => exfalso; exact h_c₁ h.right.right.left
              | inr h => exfalso; exact h_c₂ h.right.right.right.left
  case isFalse h_as =>
    apply Iff.intro
    case mp => intro h; exfalso; exact h_stack.left h.symm
    case mpr =>
      intro h; exfalso
      cases h
      case inl h => obtain ⟨h_a, h_s, _⟩ := h; exact h_as ⟨h_a, h_s⟩
      case inr h => obtain ⟨h_a, h_s, _⟩ := h; exact h_as ⟨h_a, h_s⟩

theorem probabilisticChoice_eq_second_iff (h_stack : e s.stack ≠ 0 ∧ e s.stack ≠ 1):
    programSmallStepSemantics [Prog| pif e then [[c₁]] else [[c₂]] fi] s a c' s' = σ (e s.stack)
    ↔ a = Action.deterministic ∧ s = s' ∧ c₁ = c' ∧ c₂ ≠ c' ∧ e s.stack = σ (e s.stack)
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ = c' := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  split
  case isTrue h =>
    obtain ⟨h_a, h_s⟩ := h
    split
    case isTrue h =>
      obtain ⟨h_c₁, h_c₂⟩ := h
      apply Iff.intro
      case mp =>
        intro h_e
        rw [eq_comm, eq_zero_iff_sym_eq_one] at h_e
        exfalso
        exact h_stack.left h_e
      case mpr =>
        intro h
        cases h
        case inl h => exfalso; exact h.right.right.right.left h_c₂
        case inr h => exfalso; exact h.right.right.left h_c₁
    case isFalse h =>
      split
      case isTrue h_c₁ =>
          rw [not_and] at h; specialize h h_c₁; rename ¬c₂ = c' => h_c₂
          apply Iff.intro
          case mp => intro h; exact Or.inl ⟨h_a, h_s, h_c₁, h_c₂, h⟩
          case mpr =>
            intro h
            cases h
            case inl h => exact h.right.right.right.right
            case inr h => exfalso; exact h.right.right.left h_c₁
      case isFalse h_c₁ =>
        split
        case isTrue h_c₂ =>
          simp only [ne_eq, true_iff]
          clear h
          exact Or.inr ⟨h_a, h_s, h_c₁, h_c₂⟩
        case isFalse h_c₂ =>
          clear h
          apply Iff.intro
          case mp => intro h; rw [eq_comm, eq_one_iff_sym_eq_zero] at h; exfalso; exact h_stack.right h
          case mpr =>
            intro h; cases h with
              | inl h => exfalso; exact h_c₁ h.right.right.left
              | inr h => exfalso; exact h_c₂ h.right.right.right
  case isFalse h_as =>
    apply Iff.intro
    case mp => intro h; rw [eq_comm, eq_one_iff_sym_eq_zero] at h; exfalso; exact h_stack.right h
    case mpr =>
      intro h; exfalso
      cases h
      case inl h => obtain ⟨h_a, h_s, _⟩ := h; exact h_as ⟨h_a, h_s⟩
      case inr h => obtain ⟨h_a, h_s, _⟩ := h; exact h_as ⟨h_a, h_s⟩

theorem probabilisticChoice_mem :
    programSmallStepSemantics [Prog| pif e then [[c₁]] else [[c₂]] fi] s a c' s'
    ∈ ({0, e s.stack, σ (e s.stack), 1} : Set I) := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  simp only [mem_insert_iff, mem_singleton_iff]
  split
  case isTrue h =>
    split
    case isTrue _ => simp only [one_ne_zero, or_true]
    case isFalse _ =>
    split
    case isTrue _ => simp only [true_or, or_true]
    case isFalse _ =>
    split
    case isTrue _ => simp only [true_or, or_true]
    case isFalse _ => simp only [zero_ne_one, or_false, true_or]
  case isFalse h => simp only [zero_ne_one, or_false, true_or]

theorem conditionalChoice_eq_one_iff :
    programSmallStepSemantics [Prog| if b then [[c₁]] else [[c₂]] fi] s a c' s' = 1
    ↔ a = Action.deterministic ∧ s = s' ∧ (b s.stack ∧ c₁ = c' ∨ ¬ b s.stack ∧ c₂ = c') := by
  rw [programSmallStepSemantics, conditionalChoiceSmallStepSemantics, iteOneZero_eq_one_def]

theorem conditionalChoice_mem :
    programSmallStepSemantics [Prog| if b then [[c₁]] else [[c₂]] fi] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, conditionalChoiceSmallStepSemantics]
  simp only [Bool.not_eq_true, mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def]
  rw [or_iff_not_imp_left, not_not, imp_self]
  trivial

theorem loop_eq_one_iff :
    programSmallStepSemantics [Prog| while b begin [[c]] fi] s a c' s' = 1
    ↔ a = Action.deterministic ∧ s = s'
    ∧ (b s.stack ∧ c' = [Prog| [[c]] ; while b begin [[c]] fi]
      ∨ ¬ b s.stack ∧ c' = [Prog| ↓]) := by
  rw [programSmallStepSemantics, loopSmallStepSemantics]
  split
  case h_1 => simp only [Bool.not_eq_true, iteOneZero_eq_one_def, and_false, and_true, false_or]
  case h_2 _ h_term =>
    simp only [iteOneZero_eq_one_def, Bool.not_eq_true, and_congr_right_iff]
    intro _
    apply Iff.intro
    case mp =>
      rintro ⟨h_c', h_s, h_b⟩
      exact ⟨h_s, Or.inl ⟨h_b, h_c'⟩⟩
    case mpr =>
      rintro ⟨h_s, ⟨h_b, h_c'⟩ | ⟨_, h_c'⟩⟩
      case inl.intro => exact ⟨h_c', h_s, h_b⟩
      case inr.intro => exfalso; exact h_term h_c'

theorem loop_mem :
    programSmallStepSemantics [Prog| while b begin [[c]] fi] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, loopSmallStepSemantics]
  simp only [Bool.not_eq_true, mem_insert_iff, mem_singleton_iff]
  split
  case h_1 =>
    simp only [iteOneZero_def, not_and, Bool.not_eq_false, true_and, zero_ne_one, false_and,
      or_false, one_ne_zero, false_or]
    cases eq_or_ne a Action.deterministic with
    | inl h_a =>
      cases eq_or_ne s s' with
      | inl h_s =>
        cases eq_or_ne (b s.stack) false with
        | inl h_b => exact Or.inr ⟨h_a, h_s, h_b⟩
        | inr h_b =>
          simp only [ne_eq, Bool.not_eq_false] at h_b
          exact Or.inl (fun _ _ => h_b)
      | inr h_s => exact Or.inl (fun _ h_s' => (h_s h_s').elim)
    | inr h_a => exact Or.inl (fun h_a' => (h_a h_a').elim)
  case h_2 _ h_term =>
    simp only [iteOneZero_def, not_and, Bool.not_eq_true, true_and, zero_ne_one, false_and,
      or_false, one_ne_zero, false_or]
    cases eq_or_ne a Action.deterministic with
    | inl h_a =>
      cases eq_or_ne c' [Prog| [[c]] ; while b begin [[c]] fi] with
      | inl h_c =>
        cases eq_or_ne s s' with
        | inl h_s =>
          cases eq_or_ne (b s.stack) true with
          | inl h_b => exact Or.inr ⟨h_a, h_c, h_s, h_b⟩
          | inr h_b =>
            simp only [ne_eq, Bool.not_eq_true] at h_b
            exact Or.inl (fun _ _ _ => h_b)
        | inr h_s => exact Or.inl (fun _ _ h_s' => (h_s h_s').elim)
      | inr h_c => exact Or.inl (fun _ h_c' => (h_c h_c').elim)
    | inr h_a => exact Or.inl (fun h_a' => (h_a h_a').elim)


theorem sequential_iff :
    programSmallStepSemantics [Prog| [[c₁]] ; [[c₂]]] s a c' s' = i
    ↔ c₁ ≠ [Prog| ↓] ∧ c' = [Prog| ↯] ∧ programSmallStepSemantics c₁ s a [Prog| ↯] s' = i
    ∨ c₁ = [Prog| ↓] ∧ a = Action.deterministic ∧ s = s' ∧ c' = c₂ ∧ i = 1
    ∨ c₁ = [Prog| ↓] ∧ ¬ (a = Action.deterministic ∧ s = s' ∧ c' = c₂) ∧ i = 0
    ∨ (c₁ ≠ [Prog| ↓] ∧ c' ≠ [Prog| ↯] ∧ (∃ c₁', c' = [Prog| [[c₁']] ; [[c₂]] ] ∧ programSmallStepSemantics c₁ s a c₁' s' = i)
    ∨ c₁ ≠ [Prog| ↓] ∧ c' ≠ [Prog| ↯] ∧ ¬ (∃ c₁', c' = [Prog| [[c₁']] ; [[c₂]] ]) ∧ i = 0) := by
  apply Iff.intro
  case mp =>
    intro h
    unfold programSmallStepSemantics at h
    split at h
    case isTrue h_term =>
      obtain rfl := h_term
      simp only [iteOneZero_def] at h
      obtain (⟨rfl, h⟩ | h) := h
      case inl =>
        apply Or.inr; apply Or.inr; apply Or.inl
        trivial
      case inr h =>
        apply Or.inr; apply Or.inl
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        trivial
    case isFalse h_n_term =>
      split at h
      case isTrue h_error =>
        apply Or.inl
        trivial
      case isFalse h_n_error =>
        apply Or.inr; apply Or.inr; apply Or.inr
        split at h
        case h_1 _ c₁' c₂' =>
          split at h
          case isTrue h_c₂ =>
            obtain rfl := h_c₂
            obtain rfl := h
            apply Or.inl
            use h_n_term, h_n_error, c₁'
          case isFalse h_c₂ =>
            obtain rfl := h
            apply Or.inr
            use h_n_term, h_n_error
            refine And.intro ?_ rfl
            intro h
            obtain ⟨_, h⟩ := h
            simp only [sequential.injEq] at h
            exact h_c₂ h.right.symm
        case h_2 a c h_c =>
          apply Or.inr
          apply And.intro h_n_term
          apply And.intro h_n_error
          rw [and_comm]
          apply And.intro h.symm; clear h
          rintro ⟨c₁', h_c'⟩
          exact h_c c₁' c₂ h_c'
  case mpr =>
    rintro (h | h | h | h | h)
    · unfold programSmallStepSemantics
      obtain ⟨h_term, h_error, h⟩ := h
      rw [if_neg h_term, if_pos h_error]
      exact h
    · unfold programSmallStepSemantics
      obtain ⟨h_term, rfl, rfl, rfl, rfl⟩ := h
      rw [if_pos h_term, iteOneZero_eq_one_def]
      trivial
    · unfold programSmallStepSemantics
      obtain ⟨h_term, h, rfl⟩ := h
      rw [if_pos h_term, iteOneZero_eq_zero_def]
      exact h
    · unfold programSmallStepSemantics
      obtain ⟨h_n_term, _, _, rfl, rfl⟩ := h
      simp only [↓reduceIte, if_neg h_n_term]
    · unfold programSmallStepSemantics
      obtain ⟨h_n_term, h_n_error, h, rfl⟩ := h
      rw [if_neg h_n_term, if_neg h_n_error]
      split
      case h_1 _ c₁' c₂' =>
        split
        case isTrue h_c₂ =>
          rw [h_c₂] at h
          simp only [sequential.injEq, and_true, exists_eq', not_true_eq_false] at h
        case isFalse h_c₂ => rfl
      case h_2 => rfl

theorem concurrent_iff_of_term :
    programSmallStepSemantics [Prog| [[c₁]] || [[c₂]]] s Action.deterministic c' s' = i
    ↔ (c₁ = [Prog| ↓] ∧ c₂ = [Prog| ↓] ∧ c' = [Prog| ↓] ∧ s = s' ∧ i = 1)
    ∨ (¬(c₁ = [Prog| ↓] ∧ c₂ = [Prog| ↓] ∧ c' = [Prog| ↓]  ∧ s = s') ∧ i = 0) := by
  rw [programSmallStepSemantics]
  simp only [true_and, not_and]
  split
  case isTrue h_term =>
    obtain ⟨rfl, rfl⟩ := h_term
    apply Iff.intro
    case mp =>
      rw [iteOneZero_def]
      rintro (⟨rfl, h⟩ | ⟨rfl, rfl, rfl⟩)
      · apply Or.inr
        refine And.intro ?_ rfl
        rintro _ _ rfl rfl
        exact h ⟨rfl, rfl⟩
      · apply Or.inl
        trivial
    case mpr =>
      rintro (⟨_, _, rfl, rfl, rfl⟩ | ⟨h, rfl⟩)
      · simp only [and_self, iteOneZero_pos]
      · rw [iteOneZero_neg]
        rintro ⟨rfl, rfl⟩
        exact h rfl rfl rfl rfl
  case isFalse h_n_term =>
    apply Iff.intro
    case mp =>
      rintro rfl
      apply Or.inr
      refine And.intro ?_ rfl
      rintro rfl rfl
      simp only [and_self, not_true_eq_false] at h_n_term
    case mpr =>
      rintro (h | h)
      · obtain ⟨rfl, rfl, _⟩ := h
        simp only [and_self, not_true_eq_false] at h_n_term
      · obtain ⟨_, rfl⟩ := h
        rfl

theorem concurrent_iff_of_left :
    programSmallStepSemantics [Prog| [[c₁]] || [[c₂]]] s (Action.concurrentLeft a) c' s' = i
    ↔ c₁ ≠ [Prog| ↓] ∧ c' ≠ [Prog| ↯]
      ∧ (∃ c₁', c' = [Prog| [[c₁']] || [[c₂]]] ∧ programSmallStepSemantics c₁ s a c₁' s' = i)
    ∨ c₁ ≠ [Prog| ↓] ∧ c' = [Prog| ↯] ∧ programSmallStepSemantics c₁ s a [Prog| ↯] s' = i
    ∨ ¬ (c₁ ≠ [Prog| ↓] ∧ (c' = [Prog| ↯] ∨ ∃ c₁', c' = [Prog| [[c₁']] || [[c₂]]])) ∧ i = 0
    := by
  rw [programSmallStepSemantics]
  simp only [false_and, and_false, iteOneZero_false, ne_eq, not_and, not_exists]
  split
  case isTrue h_term =>
    obtain ⟨rfl, rfl⟩ := h_term
    apply Iff.intro
    case mp =>
      rintro rfl
      apply Or.inr; apply Or.inr
      rw [and_comm]; apply And.intro rfl
      intro h
      simp only [not_true_eq_false] at h
    case mpr =>
      rintro (⟨h,_⟩ | ⟨h,_⟩ | ⟨_,rfl⟩)
      · simp only [not_true_eq_false] at h
      · simp only [not_true_eq_false] at h
      · rfl
  case isFalse h_n_term =>
    clear h_n_term
    split
    case isTrue h_error =>
      obtain rfl := h_error
      apply Iff.intro
      case mp =>
        rintro rfl
        cases eq_or_ne c₁ [Prog| ↓]
        case inl h_eq =>
          obtain rfl := h_eq
          apply Or.inr; apply Or.inr
          simp only [not_true_eq_false, IsEmpty.forall_iff, true_and]
          exact terminated_eq_zero
        case inr h_ne =>
          apply Or.inr; apply Or.inl
          exact ⟨h_ne, rfl, rfl⟩
      case mpr =>
        rintro (h | h | h )
        · obtain ⟨_, h, _⟩ := h
          simp only [not_true_eq_false] at h
        · obtain ⟨_, _, rfl⟩ := h
          rfl
        · cases eq_or_ne c₁ [Prog| ↯]
          case inl h_eq =>
            rw [h_eq] at h
            simp only [not_false_eq_true, exists_false, or_false, not_true_eq_false,
              forall_true_left, false_and] at h
          case inr h_ne =>
            simp only [exists_false, or_false, not_true_eq_false, imp_false, not_not] at h
            obtain ⟨rfl, rfl⟩ := h
            exact terminated_eq_zero
    case isFalse h_n_error =>
      split
      case h_1 _ c₁' c₂' =>
        split
        case isTrue h_c₂ =>
          obtain rfl := h_c₂
          apply Iff.intro
          case mp =>
            rintro rfl
            cases eq_or_ne c₁ [Prog| ↓]
            case inl h_term =>
              apply Or.inr; apply Or.inr
              obtain rfl := h_term
              refine And.intro ?_ terminated_eq_zero
              intro h
              simp only [not_true_eq_false] at h
            case inr h_term =>
              apply Or.inl
              simp only [h_term, not_false_eq_true, concurrent.injEq, and_true, exists_eq_left',
                and_self]
          case mpr =>
            rintro (h | h | h)
            · obtain ⟨_, _, _, h, rfl⟩ := h
              cases h
              rfl
            · obtain ⟨_, h, _⟩ := h
              exact h.elim
            · obtain ⟨h, rfl⟩ := h
              cases eq_or_ne c₁ [Prog| ↓]
              case inl h_eq =>
                rw [h_eq]
                exact terminated_eq_zero
              case inr h_ne =>
                exact (h h_ne (Or.inr <| Exists.intro c₁' rfl)).elim
        case isFalse h_c₂ =>
          apply Iff.intro
          case mp =>
            rintro rfl
            cases eq_or_ne c₁ [Prog| ↓]
            case inl h_eq =>
              obtain rfl := h_eq
              apply Or.inr; apply Or.inr
              refine And.intro ?_ rfl
              intro h
              simp only [not_true_eq_false] at h
            case inr h_ne =>
              apply Or.inr; apply Or.inr
              refine And.intro ?_ rfl
              rintro _ (h | h)
              · exact h
              · obtain ⟨_, h⟩ := h
                cases h
                exact h_c₂ rfl
          case mpr =>
            rintro (h | h | h)
            · obtain ⟨_, _, ⟨_, h, _⟩⟩ := h
              cases h
              simp only [not_true_eq_false] at h_c₂
            · obtain ⟨_, h, _⟩ := h
              exact h.elim
            · obtain ⟨_, rfl⟩ := h
              rfl
      case h_2 _ h_n_concur =>
        apply Iff.intro
        case mp =>
          rintro rfl
          apply Or.inr; apply Or.inr
          refine And.intro ?_ rfl
          rintro _ (rfl | h)
          · simp only [not_true_eq_false] at h_n_error
          · obtain ⟨c₁', h_c'⟩ := h
            exact h_n_concur c₁' c₂ h_c'
        case mpr =>
          rintro (h | h | h)
          · obtain ⟨_, _, ⟨c₁', rfl, rfl⟩⟩ := h
            exact (h_n_concur c₁' c₂ rfl).elim
          · obtain ⟨_, rfl, _⟩ := h
            simp only [not_true_eq_false] at h_n_error
          · obtain ⟨_, rfl⟩ := h
            rfl

theorem concurrent_iff_of_right :
    programSmallStepSemantics [Prog| [[c₁]] || [[c₂]]] s (Action.concurrentRight a) c' s' = i
    ↔ c₂ ≠ [Prog| ↓] ∧ c' ≠ [Prog| ↯]
      ∧ (∃ c₂', c' = [Prog| [[c₁]] || [[c₂']]] ∧ programSmallStepSemantics c₂ s a c₂' s' = i)
    ∨ c₂ ≠ [Prog| ↓] ∧ c' = [Prog| ↯] ∧ programSmallStepSemantics c₂ s a [Prog| ↯] s' = i
    ∨ ¬ (c₂ ≠ [Prog| ↓] ∧ (c' = [Prog| ↯] ∨ ∃ c₂', c' = [Prog| [[c₁]] || [[c₂']]])) ∧ i = 0
    := by
  rw [programSmallStepSemantics]
  simp only [false_and, and_false, iteOneZero_false, ne_eq, not_and, not_exists]
  split
  case isTrue h_term =>
    obtain ⟨rfl, rfl⟩ := h_term
    apply Iff.intro
    case mp =>
      rintro rfl
      apply Or.inr; apply Or.inr
      rw [and_comm]; apply And.intro rfl
      intro h
      simp only [not_true_eq_false] at h
    case mpr =>
      rintro (⟨h,_⟩ | ⟨h,_⟩ | ⟨_,rfl⟩)
      · simp only [not_true_eq_false] at h
      · simp only [not_true_eq_false] at h
      · rfl
  case isFalse h_n_term =>
    clear h_n_term
    split
    case isTrue h_error =>
      obtain rfl := h_error
      apply Iff.intro
      case mp =>
        rintro rfl
        cases eq_or_ne c₂ [Prog| ↓]
        case inl h_eq =>
          obtain rfl := h_eq
          apply Or.inr; apply Or.inr
          simp only [not_true_eq_false, IsEmpty.forall_iff, true_and]
          exact terminated_eq_zero
        case inr h_ne =>
          apply Or.inr; apply Or.inl
          exact ⟨h_ne, rfl, rfl⟩
      case mpr =>
        rintro (h | h | h )
        · obtain ⟨_, h, _⟩ := h
          simp only [not_true_eq_false] at h
        · obtain ⟨_, _, rfl⟩ := h
          rfl
        · cases eq_or_ne c₂ [Prog| ↯]
          case inl h_eq =>
            rw [h_eq] at h
            simp only [not_false_eq_true, exists_false, or_false, not_true_eq_false,
              forall_true_left, false_and] at h
          case inr h_ne =>
            simp only [exists_false, or_false, not_true_eq_false, imp_false, not_not] at h
            obtain ⟨rfl, rfl⟩ := h
            exact terminated_eq_zero
    case isFalse h_n_error =>
      split
      case h_1 _ c₁' c₂' =>
        split
        case isTrue h_c₁ =>
          obtain rfl := h_c₁
          apply Iff.intro
          case mp =>
            rintro rfl
            cases eq_or_ne c₂ [Prog| ↓]
            case inl h_term =>
              apply Or.inr; apply Or.inr
              obtain rfl := h_term
              refine And.intro ?_ terminated_eq_zero
              intro h
              simp only [not_true_eq_false] at h
            case inr h_n_term =>
              apply Or.inl
              simp only [h_n_term, not_false_eq_true, concurrent.injEq, true_and, exists_eq_left',
                and_self]
          case mpr =>
            rintro (h | h | h)
            · obtain ⟨_, _, _, h, rfl⟩ := h
              cases h
              rfl
            · obtain ⟨_, h, _⟩ := h
              exact h.elim
            · obtain ⟨h, rfl⟩ := h
              cases eq_or_ne c₂ [Prog| ↓]
              case inl h_eq =>
                rw [h_eq]
                exact terminated_eq_zero
              case inr h_ne =>
                exact (h h_ne (Or.inr <| Exists.intro c₂' rfl)).elim
        case isFalse h_c₂ =>
          apply Iff.intro
          case mp =>
            rintro rfl
            cases eq_or_ne c₂ [Prog| ↓]
            case inl h_eq =>
              obtain rfl := h_eq
              apply Or.inr; apply Or.inr
              refine And.intro ?_ rfl
              intro h
              simp only [not_true_eq_false] at h
            case inr h_ne =>
              apply Or.inr; apply Or.inr
              refine And.intro ?_ rfl
              rintro _ (h | h)
              · exact h
              · obtain ⟨_, h⟩ := h
                cases h
                exact h_c₂ rfl
          case mpr =>
            rintro (h | h | h)
            · obtain ⟨_, _, ⟨_, h, _⟩⟩ := h
              cases h
              simp only [not_true_eq_false] at h_c₂
            · obtain ⟨_, h, _⟩ := h
              exact h.elim
            · obtain ⟨_, rfl⟩ := h
              rfl
      case h_2 _ h_n_concur =>
        apply Iff.intro
        case mp =>
          rintro rfl
          apply Or.inr; apply Or.inr
          refine And.intro ?_ rfl
          rintro _ (rfl | h)
          · simp only [not_true_eq_false] at h_n_error
          · obtain ⟨c₂', h_c'⟩ := h
            exact h_n_concur c₁ c₂' h_c'
        case mpr =>
          rintro (h | h | h)
          · obtain ⟨_, _, ⟨c₂', rfl, rfl⟩⟩ := h
            exact (h_n_concur c₁ c₂' rfl).elim
          · obtain ⟨_, rfl, _⟩ := h
            simp only [not_true_eq_false] at h_n_error
          · obtain ⟨_, rfl⟩ := h
            rfl

end Semantics
