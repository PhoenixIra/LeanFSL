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
    ↔ (c' = [Prog| ↓] ∧ a = Action.deterministic ∧ ∃ l:ℕ, (e_loc s.stack) = l ∧ s.heap l ≠ undef
        ∧ substituteHeap s l (e_val s.stack) = s')
      ∨ (c' = [Prog| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ ((∃ l : ℕ, (e_loc s.stack) = l ∧ s.heap l = undef) ∨ ¬ (e_loc s.stack).isInt ∨ 0 ≤ (e_loc s.stack)))
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
      ∃ l : ℕ, l = (e s.stack) ∧ ∃ value, s.heap l = val value ∧ substituteStack s v value = s' )
      ∨ (c' = [Prog| ↯] ∧ a = Action.deterministic ∧ s = s'
      ∧ ((∃ l : ℕ, (e s.stack) = l ∧ s.heap l = undef) ∨ ¬ (e s.stack).isInt ∨ 0 ≤ (e s.stack)))
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
      ∧ ∃ l : ℕ, l = (e_loc s.stack) ∧ ∃ old_val, s.heap l = val old_val
        ∧ ((old_val = (e_cmp s.stack) ∧ substituteStack (substituteHeap s l (e_val s.stack)) v 1 = s')
          ∨ old_val ≠ (e_cmp s.stack) ∧ substituteStack s v 0 = s'))
      ∨ (c' = [Prog| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ (∃ l : ℕ, (e_loc s.stack) = l ∧ s.heap l = undef)) := by
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

theorem allocate_eq_one_iff : programSmallStepSemantics [Prog| v ≔ alloc n] s a c' s' = 1
    ↔ (c' = [Prog| ↓] ∧ ∃ m, a = Action.allocation m ∧ isNotAlloc s m n
      ∧ substituteStack (substituteHeap s m n) v m = s') := by
  rw [programSmallStepSemantics, allocateSmallStepSemantics]
  simp only [iteOneZero_eq_one_def]

theorem allocate_mem_zero_one :
    programSmallStepSemantics [Prog| v ≔ alloc n] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, allocateSmallStepSemantics]
  simp only [mem_insert_iff, iteOneZero_eq_zero_def, not_and, not_exists, mem_singleton_iff,
    iteOneZero_eq_one_def]
  cases eq_or_ne c' [Prog| ↓] with
  | inl h_c =>
    by_cases h : ∃ m, a = Action.allocation m ∧ isNotAlloc s m n ∧ substituteStack (substituteHeap s m n) v m = s'
    case pos => apply Or.inr; exact ⟨h_c, h⟩
    case neg => apply Or.inl; intro _; simp only [not_exists, not_and] at h; exact h
  | inr h_c => apply Or.inl; intro h; exfalso; exact h_c h

theorem free_eq_one_iff : programSmallStepSemantics [Prog| free(e, n)] s a c' s' = 1
    ↔ (c' = [Prog| ↓] ∧ a = Action.deterministic
      ∧ ∃ l : ℕ, l = (e s.stack) ∧ isAlloc s l n ∧ freeHeap s l n = s')
    ∨ (c' = [Prog| ↯] ∧ a = Action.deterministic ∧ s = s'
      ∧ (∃ l : ℕ, (e s.stack) = l ∧ ¬isAlloc s l n ∨ ¬ (e s.stack).isInt ∨ 0 ≤ (e s.stack))) := by
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
    programSmallStepSemantics [Prog| pif e then [[c₁]] else [[c₂]] end] s a c' s' = 0
    ↔ a ≠ Action.deterministic ∨ s ≠ s'
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ ≠ c'
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ = c' ∧ c₂ ≠ c' ∧ e s.stack = 0
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ = c' ∧ e s.stack = 1 := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  split
  case inl h =>
    obtain ⟨h_a, h_s⟩ := h
    split
    case inl h =>
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
    case inr h =>
      split
      case inl h_c₁ =>
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
      case inr h_c₁ =>
        split
        case inl h_c₂ =>
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
        case inr h_c₂ =>
          clear h
          simp only [ne_eq, true_iff]
          exact Or.inr <| Or.inr <| Or.inl ⟨h_a, h_s, h_c₁, h_c₂⟩
  case inr h =>
    simp only [ne_eq, true_iff]
    simp only [not_and_or] at h
    cases h
    case inl h => exact Or.inl h
    case inr h => exact Or.inr <| Or.inl h

theorem probabilisticChoice_eq_one_iff:
    programSmallStepSemantics [Prog| pif e then [[c₁]] else [[c₂]] end] s a c' s' = 1
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
    programSmallStepSemantics [Prog| pif e then [[c₁]] else [[c₂]] end] s a c' s' = e s.stack
    ↔ a = Action.deterministic ∧ s = s' ∧ c₁ = c' ∧ c₂ ≠ c'
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ = c' ∧ e s.stack = σ (e s.stack) := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  split
  case inl h =>
    obtain ⟨h_a, h_s⟩ := h
    split
    case inl h =>
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
    case inr h =>
      split
      case inl h_c₁ =>
        rw [not_and] at h; specialize h h_c₁; rename ¬ c₂ = c' => h_c₂
        simp only [ne_eq, true_iff]
        exact Or.inl ⟨h_a, h_s, h_c₁, h_c₂⟩
      case inr h_c₁ =>
        split
        case inl h_c₂ =>
          clear h
          apply Iff.intro
          case mp => intro h; exact Or.inr ⟨h_a, h_s, h_c₁, h_c₂, h.symm⟩
          case mpr =>
            intro h
            cases h
            case inl h => exfalso; exact h.right.right.right h_c₂
            case inr h => exact h.right.right.right.right.symm
        case inr h_c₂ =>
          clear h
          apply Iff.intro
          case mp => intro h; exfalso; exact h_stack.left h.symm
          case mpr =>
            intro h; cases h with
              | inl h => exfalso; exact h_c₁ h.right.right.left
              | inr h => exfalso; exact h_c₂ h.right.right.right.left
  case inr h_as =>
    apply Iff.intro
    case mp => intro h; exfalso; exact h_stack.left h.symm
    case mpr =>
      intro h; exfalso
      cases h
      case inl h => obtain ⟨h_a, h_s, _⟩ := h; exact h_as ⟨h_a, h_s⟩
      case inr h => obtain ⟨h_a, h_s, _⟩ := h; exact h_as ⟨h_a, h_s⟩

theorem probabilisticChoice_eq_second_iff (h_stack : e s.stack ≠ 0 ∧ e s.stack ≠ 1):
    programSmallStepSemantics [Prog| pif e then [[c₁]] else [[c₂]] end] s a c' s' = σ (e s.stack)
    ↔ a = Action.deterministic ∧ s = s' ∧ c₁ = c' ∧ c₂ ≠ c' ∧ e s.stack = σ (e s.stack)
    ∨ a = Action.deterministic ∧ s = s' ∧ c₁ ≠ c' ∧ c₂ = c' := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  split
  case inl h =>
    obtain ⟨h_a, h_s⟩ := h
    split
    case inl h =>
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
    case inr h =>
      split
      case inl h_c₁ =>
          rw [not_and] at h; specialize h h_c₁; rename ¬c₂ = c' => h_c₂
          apply Iff.intro
          case mp => intro h; exact Or.inl ⟨h_a, h_s, h_c₁, h_c₂, h⟩
          case mpr =>
            intro h
            cases h
            case inl h => exact h.right.right.right.right
            case inr h => exfalso; exact h.right.right.left h_c₁
      case inr h_c₁ =>
        split
        case inl h_c₂ =>
          simp only [ne_eq, true_iff]
          clear h
          exact Or.inr ⟨h_a, h_s, h_c₁, h_c₂⟩
        case inr h_c₂ =>
          clear h
          apply Iff.intro
          case mp => intro h; rw [eq_comm, eq_one_iff_sym_eq_zero] at h; exfalso; exact h_stack.right h
          case mpr =>
            intro h; cases h with
              | inl h => exfalso; exact h_c₁ h.right.right.left
              | inr h => exfalso; exact h_c₂ h.right.right.right
  case inr h_as =>
    apply Iff.intro
    case mp => intro h; rw [eq_comm, eq_one_iff_sym_eq_zero] at h; exfalso; exact h_stack.right h
    case mpr =>
      intro h; exfalso
      cases h
      case inl h => obtain ⟨h_a, h_s, _⟩ := h; exact h_as ⟨h_a, h_s⟩
      case inr h => obtain ⟨h_a, h_s, _⟩ := h; exact h_as ⟨h_a, h_s⟩

theorem probabilisticChoice_mem :
    programSmallStepSemantics [Prog| pif e then [[c₁]] else [[c₂]] end] s a c' s'
    ∈ ({0, e s.stack, σ (e s.stack), 1} : Set I) := by
  rw [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
  simp only [mem_insert_iff, mem_singleton_iff]
  split
  case inl h =>
    split
    case inl _ => simp only [one_ne_zero, or_true]
    case inr _ =>
    split
    case inl _ => simp only [true_or, or_true]
    case inr _ =>
    split
    case inl _ => simp only [true_or, or_true]
    case inr _ => simp only [zero_ne_one, or_false, true_or]
  case inr h => simp only [zero_ne_one, or_false, true_or]

theorem conditionalChoice_eq_one_iff :
    programSmallStepSemantics [Prog| if b then [[c₁]] else [[c₂]] end] s a c' s' = 1
    ↔ a = Action.deterministic ∧ s = s' ∧ (b s.stack ∧ c₁ = c' ∨ ¬ b s.stack ∧ c₂ = c') := by
  rw [programSmallStepSemantics, conditionalChoiceSmallStepSemantics, iteOneZero_eq_one_def]

theorem conditionalChoice_mem :
    programSmallStepSemantics [Prog| if b then [[c₁]] else [[c₂]] end] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, conditionalChoiceSmallStepSemantics]
  simp only [Bool.not_eq_true, mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def]
  rw [or_iff_not_imp_left, not_not, imp_self]
  trivial

theorem loop_eq_one_iff :
    programSmallStepSemantics [Prog| while b begin [[c]] end] s a c' s' = 1
    ↔ a = Action.deterministic ∧ s = s'
    ∧ (b s.stack ∧ c' = [Prog| [[c]] ; while b begin [[c]] end]
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
    programSmallStepSemantics [Prog| while b begin [[c]] end] s a c' s' ∈ ({0, 1} : Set I) := by
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
      cases eq_or_ne c' [Prog| [[c]] ; while b begin [[c]] end] with
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
    ↔ (c₁ = [Prog| ↓] ∧ a = Action.deterministic ∧ s = s' ∧ c' = c₂ ∧ i = 1
    ∨ c₁ = [Prog| ↓] ∧ ¬ (a = Action.deterministic ∧ s = s' ∧ c' = c₂) ∧ i = 0)
    ∨ c₁ ≠ [Prog| ↓] ∧ (∃ c₁', c' = [Prog| [[c₁']] ; [[c₂]] ] ∧ programSmallStepSemantics c₁ s a c₁' s' = i)
    ∨ c₁ ≠ [Prog| ↓] ∧ ¬ (∃ c₁', c' = [Prog| [[c₁']] ; [[c₂]] ]) ∧ i = 0 := by
  apply Iff.intro
  case mp =>
    intro h
    unfold programSmallStepSemantics at h
    split at h
    case inl h_term =>
      apply Or.inl
      simp [iteOneZero_def] at h
      cases h
      case inl h =>
        obtain ⟨rfl, h⟩ := h
        apply Or.inr
        apply And.intro h_term
        rw [and_comm]
        apply And.intro rfl
        rintro ⟨h_a, h_s, h_c₂⟩
        exact h h_a h_s h_c₂
      case inr h =>
        obtain ⟨rfl, h_a, h_s, h_c₂⟩ := h
        apply Or.inl
        exact ⟨h_term, h_a, h_s, h_c₂, rfl⟩
    case inr h_term =>
      apply Or.inr
      split at h
      case h_1 _ c₁' c₂' =>
        split at h
        case inl h_c₂ =>
          apply Or.inl
          apply And.intro h_term
          use c₁'
          rw [h_c₂]
          exact ⟨rfl, h⟩
        case inr h_c₂ =>
          apply Or.inr
          apply And.intro h_term
          rw [and_comm]
          apply And.intro h.symm
          intro h
          obtain ⟨c₁'', h⟩ := h
          simp only [sequential.injEq] at h
          exact h_c₂ h.right.symm
      case h_2 a c h_c =>
        apply Or.inr
        apply And.intro h_term
        rw [and_comm]
        apply And.intro h.symm; clear h
        rintro ⟨c₁', h_c'⟩
        exact h_c c₁' c₂ h_c'
  case mpr =>
    rintro ((⟨h_term, h_a, h_s, h_c₂, rfl⟩ | ⟨h_term, h, rfl⟩)
      | ⟨h_term, c₁', rfl, h⟩ | ⟨h_term, h, rfl⟩)
    · unfold programSmallStepSemantics
      rw [if_pos h_term, iteOneZero_eq_one_def]
      exact ⟨h_a, h_s, h_c₂⟩
    · unfold programSmallStepSemantics
      rw [if_pos h_term, iteOneZero_eq_zero_def]
      exact h
    · unfold programSmallStepSemantics
      simp only [↓reduceIte, if_neg h_term]
      exact h
    · unfold programSmallStepSemantics
      rw [if_neg h_term]
      split
      case h_1 _ c₁' c₂' =>
        split
        case inl h_c₂ =>
          rw [h_c₂] at h
          simp only [sequential.injEq, and_true, exists_eq', not_true_eq_false] at h
        case inr h_c₂ => rfl
      case h_2 => rfl

theorem concurrent_iff_of_term :
    programSmallStepSemantics [Prog| [[c₁]] || [[c₂]]] s Action.deterministic c' s' = i
    ↔ c₁ = [Prog| ↓] ∧ c₂ = [Prog| ↓] ∧ c' = [Prog| ↓] ∧ s = s' ∧ i = 1
    ∨ ¬ (c₁ = [Prog| ↓] ∧ c₂ = [Prog| ↓] ∧ c' = [Prog| ↓] ∧ s = s') ∧ i = 0 := by
  rw [programSmallStepSemantics]
  simp only [true_and, not_and]
  split
  case inl h_term =>
    apply Iff.intro
    case mp =>
      intro h_i
      rw [iteOneZero_def] at h_i
      cases h_i
      case inl h =>
        obtain ⟨rfl, h_neg⟩ := h
        apply Or.inr
        rw [and_comm]; apply And.intro rfl
        intro _ _ h
        rw [not_and] at h_neg
        exact h_neg h
      case inr h =>
        obtain ⟨rfl, h_c', h_s⟩ := h
        apply Or.inl
        exact ⟨h_term.left, h_term.right, h_c', h_s, rfl⟩
    case mpr =>
      rintro (⟨_, _, h_c', h_s, rfl⟩ | ⟨h, rfl⟩)
      case inl =>
        rw [iteOneZero_pos]
        exact ⟨h_c', h_s⟩
      case inr =>
        rw [iteOneZero_neg]; rw [not_and]
        intro h_c'
        exact h h_term.left h_term.right h_c'
  case inr h_term =>
    split
    case h_1 _ c₁' c₂' =>
      apply Iff.intro
      case mp =>
        rintro rfl
        apply Or.inr
        rw [and_comm]; apply And.intro rfl
        intro h_c₁ h_c₂
        exact (h_term ⟨h_c₁, h_c₂⟩).elim
      case mpr =>
        rintro (⟨h_c₁, h_c₂, _⟩ | ⟨_, rfl⟩)
        case inl => exact (h_term ⟨h_c₁, h_c₂⟩).elim
        case inr => rfl
    case h_2 _ h_c' =>
      apply Iff.intro
      case mp =>
        rintro rfl
        apply Or.inr
        rw [and_comm]; apply And.intro rfl
        intro h_c₁ h_c₂
        exact (h_term ⟨h_c₁, h_c₂⟩).elim
      case mpr =>
        rintro (⟨h_c₁, h_c₂, _⟩ | ⟨_, rfl⟩)
        case inl => exact (h_term ⟨h_c₁, h_c₂⟩).elim
        case inr => rfl

theorem concurrent_iff_of_left :
    programSmallStepSemantics [Prog| [[c₁]] || [[c₂]]] s (Action.concurrentLeft a) c' s' = i
    ↔ c₁ ≠ [Prog| ↓] ∧ (∃ c₁', c' = [Prog| [[c₁']] || [[c₂]]] ∧ programSmallStepSemantics c₁ s a c₁' s' = i)
    ∨ ¬ (c₁ ≠ [Prog| ↓] ∧ ∃ c₁', c' = [Prog| [[c₁']] || [[c₂]]]) ∧ i = 0 := by
  rw [programSmallStepSemantics]
  simp only [false_and, and_false, iteOneZero_false, ne_eq, not_and, not_exists]
  split
  case inl h_term =>
    apply Iff.intro
    case mp =>
      rintro rfl
      apply Or.inr
      rw [and_comm]; apply And.intro rfl
      intro h_c₁
      exact (h_c₁ h_term.left).elim
    case mpr =>
      rintro (⟨h_c₁, _⟩ | ⟨_, rfl⟩)
      case inl => exact (h_c₁ h_term.left).elim
      case inr => rfl
  case inr h_term =>
    split
    case h_1 _ c₁' c₂' =>
      split
      case inl h_c₂ =>
        rw [h_c₂]; clear h_c₂
        apply Iff.intro
        case mp =>
          intro h
          cases eq_or_ne c₁ terminated
          case inl h_term =>
            apply Or.inr
            rw [h_term, terminated_eq_zero] at h
            rw [← h]
            rw [and_comm]; apply And.intro rfl
            intro h_term'
            exact (h_term' h_term).elim
          case inr h_term =>
            apply Or.inl
            apply And.intro h_term
            use c₁'
        case mpr =>
          intro h
          cases h
          case inl h =>
            obtain ⟨_, c₁', h_c, h⟩ := h
            cases h_c
            exact h
          case inr h =>
            obtain ⟨h, rfl⟩ := h
            cases eq_or_ne c₁ [Prog| ↓]
            case inl h_term => rw [h_term, terminated_eq_zero]
            case inr h_term =>
              specialize h h_term c₁'
              simp only [not_true_eq_false] at h
      case inr h_c₂ =>
        apply Iff.intro
        case mp =>
          rintro rfl
          cases eq_or_ne c₁ [Prog| ↓]
          case inl h_c₁ =>
            apply Or.inr
            rw [and_comm]; apply And.intro rfl
            intro h_c₁'
            exact (h_c₁' h_c₁).elim
          case inr h_c₁ =>
            apply Or.inr
            rw [and_comm]; apply And.intro rfl
            intro _ c'
            simp only [concurrent.injEq, not_and]
            intro _
            exact Ne.symm h_c₂
        case mpr =>
          rintro (⟨_, c₁'', h_c, h⟩ | ⟨_, rfl⟩)
          case inl => cases h_c; simp only [not_true_eq_false] at h_c₂
          case inr => rfl
    case h_2 _ h =>
      apply Iff.intro
      case mp =>
        rintro rfl
        apply Or.inr
        rw [and_comm]; apply And.intro rfl
        intro _ c₁
        exact h c₁ c₂
      case mpr =>
        rintro (⟨_, c₁', h_c, _⟩ | ⟨_, rfl⟩)
        case inl => exact (h c₁' c₂ h_c).elim
        case inr => rfl

theorem concurrent_iff_of_right :
    programSmallStepSemantics [Prog| [[c₁]] || [[c₂]]] s (Action.concurrentRight a) c' s' = i
    ↔ c₂ ≠ [Prog| ↓] ∧ (∃ c₂', c' = [Prog| [[c₁]] || [[c₂']]] ∧ programSmallStepSemantics c₂ s a c₂' s' = i)
    ∨ ¬ (c₂ ≠ [Prog| ↓] ∧ ∃ c₂', c' = [Prog| [[c₁]] || [[c₂']]]) ∧ i = 0 := by
  rw [programSmallStepSemantics]
  simp only [false_and, and_false, iteOneZero_false, not_and, not_exists]
  split
  case inl h_term =>
    apply Iff.intro
    case mp =>
      rintro rfl
      apply Or.inr
      rw [and_comm]; apply And.intro rfl
      intro h
      exact (h h_term.right).elim
    case mpr =>
      rintro (⟨h_c₂, _⟩ | ⟨_, rfl⟩)
      case inl => exact (h_c₂ h_term.right).elim
      case inr => rfl
  case inr _ =>
    split
    case h_1 _ c₁' c₂' =>
      split
      case inl h_c₁ =>
        apply Iff.intro
        case mp =>
          intro h
          cases eq_or_ne c₂ terminated
          case inl h_c₂ =>
            rw [h_c₂, terminated_eq_zero] at h
            rw [← h]
            apply Or.inr
            rw [and_comm]; apply And.intro rfl
            intro h
            exact (h h_c₂).elim
          case inr h_c₂ =>
            apply Or.inl
            apply And.intro h_c₂
            rw [h_c₁]
            use c₂'
        case mpr =>
          rintro (⟨_, c₂'', h_c, h⟩ | ⟨h, rfl⟩)
          case inl => cases h_c; exact h
          case inr =>
            cases eq_or_ne c₂ [Prog| ↓]
            case inl h_c₂ =>
              rw [h_c₂, terminated_eq_zero]
            case inr h_c₂ =>
              specialize h h_c₂ c₂'
              simp only [concurrent.injEq, and_true] at h
              exact (h h_c₁.symm).elim
      case inr h_c₁ =>
        apply Iff.intro
        case mp =>
          rintro rfl
          apply Or.inr
          rw [and_comm]; apply And.intro rfl
          intro _ c₂'' h
          cases h
          simp at h_c₁
        case mpr =>
          rintro (⟨_, _, h_c, _⟩ | ⟨_, rfl⟩)
          case inl =>
            cases h_c
            simp only [not_true_eq_false] at h_c₁
          case inr => rfl
    case h_2 h_c =>
      apply Iff.intro
      case mp =>
        rintro rfl
        apply Or.inr
        rw [and_comm]; apply And.intro rfl
        intro _ c₂
        exact h_c c₁ c₂
      case mpr =>
        rintro (⟨_, c₂, h_c', _⟩ | ⟨_, rfl⟩)
        case inl => exact (h_c c₁ c₂ h_c').elim
        case inr => rfl

end Semantics
