import CQSL4.Program.Semantics
import CQSL4.Util

open Syntax Program Notation Semantics unitInterval Set State Classical

theorem skip_eq_one_iff : programSmallStepSemantics `[Prog| skip] s a c' s' = 1
    ↔ c' = `[Prog| ↓] ∧ a = Action.deterministic ∧ s = s' := by
  apply Iff.intro
  · intro h
    rw [programSmallStepSemantics, skipSmallStepSemantics, iteOneZero_eq_one_def] at h
    exact h
  · intro h
    rw [programSmallStepSemantics, skipSmallStepSemantics, iteOneZero_eq_one_def]
    exact h

theorem skip_mem_zero_one : programSmallStepSemantics `[Prog| skip] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, skipSmallStepSemantics,
    mem_insert_iff, mem_singleton_iff, iteOneZero_eq_one_def, iteOneZero_eq_zero_def, ← imp_iff_not_or, imp_self]
  trivial

theorem terminated_eq_zero : programSmallStepSemantics `[Prog| ↓] s a c' s' = 0 := by
  simp only [programSmallStepSemantics, Pi.zero_apply]

theorem error_eq_zero : programSmallStepSemantics `[Prog| ↯] s a c' s' = 0 := by
  simp only [programSmallStepSemantics, Pi.zero_apply]

theorem assign_eq_one_iff : programSmallStepSemantics `[Prog| v ≔ e] s a c' s' = 1
    ↔ (c' = `[Prog| ↓] ∧ a = Action.deterministic ∧ substituteStack s v (e s.stack) = s')
    := by
  rw [programSmallStepSemantics, assignSmallStepSemantics]
  split
  case h_1 => simp only [iteOneZero_eq_one_def, true_and]
  case h_2 h => simp only [zero_ne_one, false_iff, not_and]; intro h_c; exfalso; exact h h_c

theorem assign_mem_zero_one : programSmallStepSemantics `[Prog| v ≔ e] s a c' s' ∈ ({0, 1} : Set I) := by
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

theorem manipulate_eq_one_iff : programSmallStepSemantics `[Prog| e_loc *≔ e_val] s a c' s' = 1
    ↔ (c' = `[Prog| ↓] ∧ a = Action.deterministic ∧ s.heap (e_loc s.stack) ≠ none
        ∧ substituteHeap s (e_loc s.stack) (e_val s.stack) = s')
      ∨ (c' = `[Prog| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ s.heap (e_loc s.stack) = none)
    := by
  rw [programSmallStepSemantics, manipulateSmallStepSemantics]
  split
  case h_1 => simp only [ne_eq, iteOneZero_eq_one_def, true_and, false_and, or_false]
  case h_2 => simp only [iteOneZero_eq_one_def, ne_eq, false_and, true_and, false_or]
  case h_3 h_term h_err =>
    simp only [zero_ne_one, ne_eq, false_iff]
    intro h
    cases h with | inl h => exact h_term h.left | inr h => exact h_err h.left

theorem manipulate_mem_zero_one : programSmallStepSemantics `[Prog| e_loc *≔ e_val] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, manipulateSmallStepSemantics]
  split
  case h_1 => simp only [ne_eq, mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_2 _ => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_3 _ _ _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem lookup_eq_one_iff : programSmallStepSemantics `[Prog| v ≔* e] s a c' s' = 1
    ↔ (c' = `[Prog| ↓] ∧ a = Action.deterministic ∧
        ∃ val, s.heap (e s.stack) = some val ∧ substituteStack s v val = s')
      ∨ (c' = `[Prog| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ s.heap (e s.stack) = none)
    := by
  rw [programSmallStepSemantics, lookupSmallStepSemantics]
  split
  case h_1 => simp only [iteOneZero_eq_one_def, true_and, false_and, or_false]
  case h_2 _ => simp only [iteOneZero_eq_one_def, false_and, true_and, false_or]
  case h_3 _ h_term h_err =>
    simp only [zero_ne_one, false_iff]
    intro h
    cases h with | inl h => exact h_term h.left | inr h => exact h_err h.left

theorem lookup_mem_zero_one : programSmallStepSemantics `[Prog| v ≔* e] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, lookupSmallStepSemantics]
  split
  case h_1 => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_2 _ => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_3 _ _ _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem compareAndSet_eq_one_iff : programSmallStepSemantics `[Prog| v ≔ cas (e_loc, e_cmp, e_val)] s a c' s' = 1
    ↔ (c' = `[Prog| ↓] ∧ a = Action.deterministic
      ∧ ∃ old_val, s.heap (e_loc s.stack) = some old_val
        ∧ ((old_val = (e_cmp s.stack) ∧ substituteStack (substituteHeap s (e_loc s.stack) (e_val s.stack)) v 1 = s')
          ∨ old_val ≠ (e_cmp s.stack) ∧ substituteStack s v 0 = s'))
      ∨ (c' = `[Prog| ↯] ∧ a = Action.deterministic ∧ s = s'
        ∧ s.heap (e_loc s.stack ) = none) := by
  rw [programSmallStepSemantics, compareAndSetSmallStepSemantics]
  split
  case h_1 => simp only [ne_eq, iteOneZero_eq_one_def, true_and, false_and, or_false]
  case h_2 _ => simp only [iteOneZero_eq_one_def, ne_eq, false_and, true_and, false_or]
  case h_3 _ h_term h_err =>
    simp only [zero_ne_one, ne_eq, false_iff]
    intro h
    cases h with | inl h => exact h_term h.left | inr h => exact h_err h.left

theorem compareAndSet_mem_zero_one :
    programSmallStepSemantics `[Prog| v ≔ cas(e_loc, e_cmp , e_val)] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, compareAndSetSmallStepSemantics]
  split
  case h_1 => simp only [ne_eq, mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_2 _ => simp only [mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_3 _ _ _ => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem allocate_eq_one_iff : programSmallStepSemantics `[Prog| v ≔ alloc n] s a c' s' = 1
    ↔ (c' = `[Prog| ↓] ∧ ∃ m, a = Action.allocation m ∧ isNotAlloc s m n
      ∧ substituteStack (substituteHeap s m n) v m = s') := by
  rw [programSmallStepSemantics, allocateSmallStepSemantics]
  simp only [iteOneZero_eq_one_def]

theorem allocate_mem_zero_one :
    programSmallStepSemantics `[Prog| v ≔ alloc n] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, allocateSmallStepSemantics]
  simp only [mem_insert_iff, iteOneZero_eq_zero_def, not_and, not_exists, mem_singleton_iff,
    iteOneZero_eq_one_def]
  cases eq_or_ne c' `[Prog| ↓] with
  | inl h_c =>
    by_cases h : ∃ m, a = Action.allocation m ∧ isNotAlloc s m n ∧ substituteStack (substituteHeap s m n) v m = s'
    case pos => apply Or.inr; exact ⟨h_c, h⟩
    case neg => apply Or.inl; intro _; simp only [not_exists, not_and] at h; exact h
  | inr h_c => apply Or.inl; intro h; exfalso; exact h_c h

theorem free_eq_one_iff : programSmallStepSemantics `[Prog| free(e, n)] s a c' s' = 1
    ↔ (c' = `[Prog| ↓] ∧ a = Action.deterministic ∧ isAlloc s (e s.stack ) n ∧ freeHeap s (e s.stack ) n = s')
    ∨ (c' = `[Prog| ↯] ∧ a = Action.deterministic ∧ s = s' ∧ ¬isAlloc s (e s.stack ) n) := by
  rw [programSmallStepSemantics, freeSmallStepSemantics]
  split
  case h_1 _ => simp only [iteOneZero_eq_one_def, true_and, false_and, or_false]
  case h_2 _ => simp only [iteOneZero_eq_one_def, false_and, true_and, false_or]
  case h_3 _ h_term h_err =>
    simp only [zero_ne_one, false_iff]
    intro h
    cases h with | inl h => exact h_term h.left | inr h => exact h_err h.left

theorem free_mem_zero_one :
    programSmallStepSemantics `[Prog| free(e, n)] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, freeSmallStepSemantics]
  split
  case h_1 _ => simp only [ne_eq, mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_2 _ => simp only [mem_insert_iff, mem_singleton_iff,
    iteOneZero_eq_zero_def, iteOneZero_eq_one_def, ← imp_iff_not_or, imp_self]
  case h_3 => simp only [mem_insert_iff, mem_singleton_iff, zero_ne_one, or_false]

theorem probabilisticChoice_eq_zero_iff :
    programSmallStepSemantics `[Prog| pif e then [[c₁]] else [[c₂]] end] s a c' s' = 0
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
    programSmallStepSemantics `[Prog| pif e then [[c₁]] else [[c₂]] end] s a c' s' = 1
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
    programSmallStepSemantics `[Prog| pif e then [[c₁]] else [[c₂]] end] s a c' s' = e s.stack
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
    programSmallStepSemantics `[Prog| pif e then [[c₁]] else [[c₂]] end] s a c' s' = σ (e s.stack)
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
    programSmallStepSemantics `[Prog| pif e then [[c₁]] else [[c₂]] end] s a c' s'
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
    programSmallStepSemantics `[Prog| if b then [[c₁]] else [[c₂]] end] s a c' s' = 1
    ↔ a = Action.deterministic ∧ s = s' ∧ (b s.stack ∧ c₁ = c' ∨ ¬ b s.stack ∧ c₂ = c') := by
  rw [programSmallStepSemantics, conditionalChoiceSmallStepSemantics, iteOneZero_eq_one_def]

theorem conditionalChoice_mem :
    programSmallStepSemantics `[Prog| if b then [[c₁]] else [[c₂]] end] s a c' s' ∈ ({0, 1} : Set I) := by
  rw [programSmallStepSemantics, conditionalChoiceSmallStepSemantics]
  simp only [Bool.not_eq_true, mem_insert_iff, iteOneZero_eq_zero_def, mem_singleton_iff,
    iteOneZero_eq_one_def]
  rw [or_iff_not_imp_left, not_not, imp_self]
  trivial

theorem loop_eq_one_iff :
    programSmallStepSemantics `[Prog| while b begin [[c]] end] s a c' s' = 1
    ↔ a = Action.deterministic ∧ s = s'
    ∧ (b s.stack ∧ c' = `[Prog| [[c]] ; while b begin [[c]] end]
      ∨ ¬ b s.stack ∧ c' = `[Prog| ↓]) := by
  rw [programSmallStepSemantics, loopSmallStepSemantics]
  split
  case h_1 => simp only [Bool.not_eq_true, iteOneZero_eq_one_def, and_false, and_true, false_or]
  case h_2 _ h_term =>
    simp only [iteOneZero_eq_one_def, Bool.not_eq_true, and_congr_right_iff]
    intro h_a
    apply Iff.intro
    case mp =>
      rintro ⟨h_c', h_s, h_b⟩
      exact ⟨h_s, Or.inl ⟨h_b, h_c'⟩⟩
    case mpr =>
      rintro ⟨h_s, ⟨h_b, h_c'⟩ | ⟨_, h_c'⟩⟩
      case inl.intro => exact ⟨h_c', h_s, h_b⟩
      case inr.intro => exfalso; exact h_term h_c'

theorem loop_mem :
    programSmallStepSemantics `[Prog| while b begin [[c]] end] s a c' s' ∈ ({0, 1} : Set I) := by
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
            cases eq_or_ne c₂ `[Prog| while b begin [[c]] end] with
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
    programSmallStepSemantics `[Prog| [[c₁]] ; [[c₂]]] s a c' s' = i
    ↔ (c₁ = `[Prog| ↓] ∧ a = Action.deterministic ∧ s = s' ∧ c' = c₂ ∧ i = 1
    ∨ c₁ = `[Prog| ↓] ∧ ¬ (a = Action.deterministic ∧ s = s' ∧ c' = c₂) ∧ i = 0)
    ∨ c₁ ≠ `[Prog| ↓] ∧ ∃ c₁', c' = `[Prog| [[c₁']] ; [[c₂]] ] ∧ programSmallStepSemantics c₁ s a c₁' s' = i
    ∨ c₁ ≠ `[Prog| ↓] ∧ ¬ (∃ c₁', c' = `[Prog| [[c₁']] ; [[c₂]] ]) ∧ i = 0 := by sorry
--   cases c₁ with
--   | terminated =>
--     rw [programSmallStepSemantics, programSmallStepSemantics]
--     simp only [iteOneZero_def, true_and, ne_eq, not_true_eq_false, Pi.zero_apply,
--       not_exists, false_and, or_false, exists_and_right]
--     apply Iff.intro
--     · intro h
--       cases h with
--       | inl h =>
--         let ⟨h_i, h⟩ := h
--         apply Or.inr
--         exact ⟨h, h_i⟩
--       | inr h =>
--         let ⟨h_i, h⟩ := h
--         apply Or.inl
--         exact ⟨h.left, h.right.left, h.right.right, h_i⟩
--     · intro h
--       cases h with
--       | inl h =>
--         let ⟨h_a, h_s, h_c, h_i⟩ := h
--         apply Or.inr
--         exact ⟨h_i, h_a, h_s, h_c⟩
--       | inr h =>
--         let ⟨h, h_i⟩ := h
--         apply Or.inl
--         exact ⟨h_i, h⟩
--   | _ =>
--     apply Iff.intro
--     · intro h
--       unfold programSmallStepSemantics at h
--       cases c' with
--       | sequential c₁' c₂' =>
--         simp only [false_and, not_and, or_self, ne_eq, not_false_eq_true, sequential.injEq,
--           exists_and_right, exists_eq', true_and, false_or]
--         simp only at h
--         use c₁'
--         cases eq_or_ne c₂ c₂' with
--         | inl h_c₂_eq =>
--           rw [if_pos h_c₂_eq] at h
--           apply Or.inl
--           apply And.intro ⟨rfl, h_c₂_eq.symm⟩
--           exact h
--         | inr h_c₂_ne =>
--           rw [if_neg h_c₂_ne] at h
--           apply Or.inr
--           exact ⟨Ne.symm h_c₂_ne, h.symm⟩
--       | _ =>
--         simp only [false_and, not_and, or_self, ne_eq, not_false_eq_true, exists_false, true_and,
--           false_or]
--         simp only at h
--         use c₂
--         exact h.symm
--     · intro h
--       simp only [false_and, not_and, or_self, ne_eq, not_false_eq_true, not_exists, true_and,
--         false_or] at h
--       unfold programSmallStepSemantics
--       cases c' with
--       | sequential c₁' c₂' =>
--         simp only
--         cases eq_or_ne c₂ c₂' with
--         | inl h_c₂_eq =>
--           rw [if_pos h_c₂_eq]
--           obtain ⟨_, ⟨h_seq, h⟩ | ⟨h_seq, _⟩⟩ := h
--           · cases h_seq
--             exact h
--           · exfalso
--             specialize h_seq c₁'
--             exact h_seq (congrArg (sequential c₁') (h_c₂_eq.symm))
--         | inr h_c₂_ne =>
--           rw [if_neg h_c₂_ne]
--           obtain ⟨_, ⟨h_seq, _⟩ | ⟨_, h_i⟩⟩ := h
--           · exfalso
--             cases h_seq
--             exact h_c₂_ne rfl
--           · exact h_i.symm
--       | _ =>
--         simp only
--         obtain ⟨c, ⟨h_seq, h_c⟩ | ⟨h_seq, h_i⟩⟩ := h
--         · exfalso; cases h_seq
--         · exact h_i.symm

theorem concurrent_iff :
    programSmallStepSemantics `[Prog| [[c₁]] || [[c₂]]] s a c' s' = i
    ↔ sorry := by sorry
