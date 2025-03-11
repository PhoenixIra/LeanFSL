import InvLimDiss.Program.Semantics
import InvLimDiss.Program.Enabled
import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal.Lemmas
import InvLimDiss.Mathlib.Tsum

namespace Semantics

open Syntax State Action Program unitInterval

variable {Var : Type}

noncomputable abbrev semantics := @programSmallStepSemantics Var

theorem skip_sum_one (s : State Var) :
    ∑' (cs : (Program Var) × (State Var)),
    ENNReal.ofReal (semantics skip' s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics
  have : (Function.support fun cs ↦ ENNReal.ofReal (skipSmallStepSemantics s deterministic cs.1 cs.2))
      ⊆ {(⟨[Prog| ↓ ], s⟩ : (Program Var) × (State Var))} := by {
    simp only [Function.support, skipSmallStepSemantics, true_and, ne_eq, ENNReal.ofReal_eq_zero,
      not_le, coe_pos, zero_lt_iteOneZero]
    intro cs h
    simp only [Set.mem_setOf_eq, zero_lt_iteOneZero] at h
    obtain ⟨h_c, h_s⟩ := h
    rw [Set.mem_singleton_iff]
    apply Prod.ext
    · simp only
      exact h_c
    · simp only
      exact h_s.symm
  }
  rw [← tsum_subtype_eq_of_support_subset this]; clear this
  rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(skipSmallStepSemantics _ _ _ _))]
  simp only [skipSmallStepSemantics, and_self, iteOneZero_true, Set.Icc.coe_one, ENNReal.ofReal_one]

theorem assign_sum_one (s : State Var) :
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| v ≔ e]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  have : (Function.support fun cs => ENNReal.ofReal ↑(assignSmallStepSemantics v e s deterministic cs.1 cs.2))
      ⊆ {(⟨[Prog| ↓ ], ⟨substituteVar s.stack v (e s.stack), s.heap⟩⟩ : (Program Var) × (State Var))} := by {
    simp only [Function.support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    intro cs h
    cases eq_or_ne cs.1 [Prog| ↓]
    case inl h_cs =>
      simp only [Set.mem_setOf_eq, h_cs, coe_pos, zero_lt_iteOneZero] at h
      simp only [Set.mem_singleton_iff]
      apply Prod.ext
      · simp only [h_cs]
      · simp only [assignSmallStepSemantics, substituteStack, true_and, zero_lt_iteOneZero] at h
        simp only [h]
    case inr h_cs =>
      simp only [assignSmallStepSemantics, substituteStack, true_and, coe_pos, Set.mem_setOf_eq,
        lt_self_iff_false] at h
  }
  rw [← tsum_subtype_eq_of_support_subset this]; clear this
  rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(assignSmallStepSemantics _ _ _ _ _ _))]
  simp only [assignSmallStepSemantics, substituteStack, and_self, iteOneZero_true, Set.Icc.coe_one,
    ENNReal.ofReal_one]

theorem mutate_sum_one (s : State Var) :
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| e *≔ e']) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  by_cases ∃ l : ℕ+, l = e s.stack ∧  s.heap l ≠ HeapValue.undef
  case pos h =>
    obtain ⟨l, h_e, h_undef⟩ := h
    have : (Function.support fun cs => ENNReal.ofReal ↑(mutateSmallStepSemantics e e' s deterministic cs.1 cs.2))
        ⊆ {(⟨[Prog| ↓ ], ⟨s.stack, substituteLoc s.heap l (e' s.stack)⟩⟩ : (Program Var) × (State Var))} := by {
      simp only [Function.support, mutateSmallStepSemantics, ne_eq, substituteHeap, true_and,
        not_exists, ENNReal.ofReal_eq_zero, not_le, coe_pos, Set.subset_singleton_iff,
        Set.mem_setOf_eq, Prod.forall, Prod.mk.injEq]
      intro c s h
      split at h
      case h_1 _ s' =>
        simp only [zero_lt_iteOneZero] at h
        obtain ⟨l', h_e', h_l', h_state⟩ := h
        rw [h_e', Nat.cast_inj, PNat.coe_inj] at h_e
        simp only [← h_state, mk.injEq, true_and, h_e]
      case h_2 _ s' =>
        exfalso
        simp only [zero_lt_iteOneZero] at h
        obtain ⟨h_s, ⟨l', h_e', h_l'⟩ | h⟩ := h
        · rw [← h_l'] at h_undef
          rw [h_e', Nat.cast_inj, PNat.coe_inj] at h_e
          simp only [h_e, ne_eq, not_true_eq_false] at h_undef
        · apply h l
          exact h_e.symm
      case h_3 _ s' => exfalso; exact (lt_self_iff_false 0).mp h
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(mutateSmallStepSemantics _ _ _ _ _ _))]
    simp only [mutateSmallStepSemantics, ne_eq, substituteHeap, mk.injEq, true_and,
      ENNReal.ofReal_eq_one, Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
    use l, h_e.symm
  case neg h =>
    simp only [ne_eq, not_exists, not_and, not_not] at h
    have : (Function.support fun cs => ENNReal.ofReal ↑(mutateSmallStepSemantics e e' s deterministic cs.1 cs.2))
        ⊆ {(⟨[Prog| ↯ ], s⟩ : (Program Var) × (State Var))} := by {
      simp only [Function.support, mutateSmallStepSemantics, ne_eq, substituteHeap, true_and,
        not_exists, ENNReal.ofReal_eq_zero, not_le, coe_pos, Set.subset_singleton_iff,
        Set.mem_setOf_eq, Prod.forall, Prod.mk.injEq]
      intro c s h'
      split at h'
      case h_1 _ s' =>
        rw [zero_lt_iteOneZero] at h'
        obtain ⟨l, h_l, h_alloc, h_s⟩ := h'
        specialize h l h_l.symm
        simp only [h, not_true_eq_false] at h_alloc
      case h_2 _ s' =>
        rw [zero_lt_iteOneZero] at h'
        obtain ⟨h_s, _⟩ := h'
        use rfl, h_s.symm
      case h_3 _ s' => exfalso; exact (lt_self_iff_false 0).mp h'
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(mutateSmallStepSemantics _ _ _ _ _ _))]
    simp only [mutateSmallStepSemantics, not_exists, true_and, ENNReal.ofReal_eq_one,
      Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
    by_cases h_l : ∃ l : ℕ+, l = e s.stack
    case pos =>
      obtain ⟨l, h_l⟩ := h_l
      left; use l, h_l.symm, h l h_l
    case neg =>
      simp only [not_exists] at h_l
      right; intro l h_l'
      exact h_l l h_l'.symm

theorem lookup_sum_one (s : State Var) :
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| v ≔* e]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  by_cases ∃ l : ℕ+, l = e s.stack ∧  s.heap l ≠ HeapValue.undef
  case pos h =>
    obtain ⟨l, h_e, h_undef⟩ := h
    rw [neq_undef_iff_exists_val] at h_undef
    obtain ⟨q, h_q⟩ := h_undef
    have : (Function.support fun cs => ENNReal.ofReal ↑(lookupSmallStepSemantics v e s deterministic cs.1 cs.2))
        ⊆ {(⟨[Prog| ↓ ], ⟨substituteVar s.stack v q, s.heap⟩⟩ : (Program Var) × (State Var))} := by {
      simp only [Function.support, lookupSmallStepSemantics, substituteStack, true_and, not_exists,
        ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos, Set.subset_singleton_iff, Set.mem_setOf_eq,
        Prod.forall, Prod.mk.injEq]
      intro c s h
      split at h
      case h_1 _ s' =>
        rw [zero_lt_iteOneZero] at h
        obtain ⟨l', h_e', q', h_q', rfl⟩ := h
        simp only [mk.injEq, and_true, true_and]
        rw [← h_e, Nat.cast_inj, PNat.coe_inj] at h_e'
        rw [h_e', h_q, HeapValue.val.injEq] at h_q'
        rw [h_q']
      case h_2 _ s' =>
        exfalso
        rw [zero_lt_iteOneZero] at h
        obtain ⟨h_s, ⟨l', h_e', h_l'⟩ | h⟩ := h
        · rw [← h_e, Nat.cast_inj, PNat.coe_inj] at h_e'
          simp only [← h_e', h_q, reduceCtorEq] at h_l'
        · apply h l
          exact h_e.symm
      case h_3 _ s' => exfalso; exact (lt_self_iff_false 0).mp h
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(lookupSmallStepSemantics _ _ _ _ _ _))]
    simp only [lookupSmallStepSemantics, substituteStack, mk.injEq, and_true, true_and,
      ENNReal.ofReal_eq_one, Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
    use l, h_e, q
  case neg h =>
    simp only [ne_eq, not_exists, not_and, not_not] at h
    have : (Function.support fun cs => ENNReal.ofReal ↑(lookupSmallStepSemantics v e s deterministic cs.1 cs.2))
        ⊆ {(⟨[Prog| ↯ ], s⟩ : (Program Var) × (State Var))} := by {
      simp only [Function.support, lookupSmallStepSemantics, substituteStack, true_and, not_exists,
        ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos, Set.subset_singleton_iff, Set.mem_setOf_eq,
        Prod.forall, Prod.mk.injEq]
      intro c s h'
      split at h'
      case h_1 _ s' =>
        rw [zero_lt_iteOneZero] at h'
        obtain ⟨l, h_l, q, h_q, h_s⟩ := h'
        specialize h l h_l
        simp only [h, reduceCtorEq] at h_q
      case h_2 _ s' =>
        rw [zero_lt_iteOneZero] at h'
        obtain ⟨h_s, _⟩ := h'
        use rfl, h_s.symm
      case h_3 _ s' => exfalso; exact (lt_self_iff_false 0).mp h'
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(lookupSmallStepSemantics _ _ _ _ _ _))]
    simp only [lookupSmallStepSemantics, not_exists, true_and, ENNReal.ofReal_eq_one,
      Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
    by_cases h_l : ∃ l : ℕ+, l = e s.stack
    case pos =>
      obtain ⟨l, h_l⟩ := h_l
      left; use l, h_l.symm, h l h_l
    case neg =>
      simp only [not_exists] at h_l
      right; intro l h_l'
      exact h_l l h_l'.symm

theorem compareAndSet_sum_one (s : State Var) :
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| v ≔ cas(e_l, e_c, e_s)]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  by_cases ∃ l : ℕ+, l = e_l s.stack ∧ s.heap l ≠ HeapValue.undef
  case pos h =>
    obtain ⟨l, h_e, h_undef⟩ := h
    rw [neq_undef_iff_exists_val] at h_undef
    obtain ⟨q, h_q⟩ := h_undef
    cases eq_or_ne q (e_c s.stack)
    case inl h_c =>
      have : (Function.support fun cs => ENNReal.ofReal ↑(compareAndSetSmallStepSemantics v e_l e_c e_s s deterministic cs.1 cs.2))
          ⊆ {(⟨[Prog| ↓ ], ⟨substituteVar s.stack v 1, substituteLoc s.heap l (e_s s.stack)⟩⟩ : (Program Var) × (State Var))} := by {
        simp only [Function.support, compareAndSetSmallStepSemantics, substituteStack,
          substituteHeap, ne_eq, true_and, not_exists, ENNReal.ofReal_eq_zero, not_le, coe_pos,
          Set.subset_singleton_iff, Set.mem_setOf_eq, Prod.forall, Prod.mk.injEq]
        intro c s h
        split at h
        case h_1 _ s' =>
          rw [zero_lt_iteOneZero] at h
          obtain ⟨l', h_e', q', h_q', (⟨h_c', h_stack⟩ | ⟨h_c', h_stack⟩)⟩ := h
          · simp only [mk.injEq, and_true, true_and]
            rw [← h_e, Nat.cast_inj, PNat.coe_inj] at h_e'
            rw [h_e', h_q, HeapValue.val.injEq] at h_q'
            rw [← h_stack, h_e']
          · exfalso
            rw [← h_e, Nat.cast_inj, PNat.coe_inj] at h_e'
            rw [h_e', h_q, HeapValue.val.injEq] at h_q'
            rw [← h_c] at h_c'
            exact h_c' h_q'
        case h_2 _ s' =>
          exfalso
          rw [zero_lt_iteOneZero] at h
          obtain ⟨h_s, ⟨l', h_e', h_l'⟩ | h⟩ := h
          · rw [← h_e, Nat.cast_inj, PNat.coe_inj] at h_e'
            simp only [← h_e', h_q, reduceCtorEq] at h_l'
          · apply h l
            exact h_e.symm
        case h_3 _ s' => exfalso; exact (lt_self_iff_false 0).mp h
      }
      rw [← tsum_subtype_eq_of_support_subset this]; clear this
      rw [tsum_singleton _ (fun cs => ENNReal.ofReal
        ↑(compareAndSetSmallStepSemantics _ _ _ _ _ _ _ _))]
      simp only [compareAndSetSmallStepSemantics, substituteStack, substituteHeap, mk.injEq, ne_eq,
        and_true, true_and, ENNReal.ofReal_eq_one, Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
      use l, h_e, q, h_q
      left
      use h_c
    case inr h_c =>
      have : (Function.support fun cs => ENNReal.ofReal ↑(compareAndSetSmallStepSemantics v e_l e_c e_s s deterministic cs.1 cs.2))
          ⊆ {(⟨[Prog| ↓ ], ⟨substituteVar s.stack v 0, s.heap⟩⟩ : (Program Var) × (State Var))} := by {
        simp only [Function.support, compareAndSetSmallStepSemantics, substituteStack,
          substituteHeap, ne_eq, true_and, not_exists, ENNReal.ofReal_eq_zero, not_le, coe_pos,
          Set.subset_singleton_iff, Set.mem_setOf_eq, Prod.forall, Prod.mk.injEq]
        intro c s h
        split at h
        case h_1 _ s' =>
          rw [zero_lt_iteOneZero] at h
          obtain ⟨l', h_e', q', h_q', (⟨h_c', h_stack⟩ | ⟨h_c', h_stack⟩)⟩ := h
          · simp only [mk.injEq, and_true, true_and]
            rw [← h_e, Nat.cast_inj, PNat.coe_inj] at h_e'
            rw [h_e', h_q, HeapValue.val.injEq] at h_q'
            simp only [h_q', h_c', ne_eq, not_true_eq_false] at h_c
          · simp only [true_and]
            rw [← h_stack]
        case h_2 _ s' =>
          exfalso
          rw [zero_lt_iteOneZero] at h
          obtain ⟨h_s, ⟨l', h_e', h_l'⟩ | h⟩ := h
          · rw [← h_e, Nat.cast_inj, PNat.coe_inj] at h_e'
            simp only [← h_e', h_q, reduceCtorEq] at h_l'
          · apply h l
            exact h_e.symm
        case h_3 _ s' => exfalso; exact (lt_self_iff_false 0).mp h
      }
      rw [← tsum_subtype_eq_of_support_subset this]; clear this
      rw [tsum_singleton _ (fun cs => ENNReal.ofReal
        ↑(compareAndSetSmallStepSemantics _ _ _ _ _ _ _ _))]
      simp only [compareAndSetSmallStepSemantics, substituteStack, mk.injEq, and_true, true_and,
        ENNReal.ofReal_eq_one, Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
      use l, h_e, q, h_q
      right
      exact h_c
  case neg h =>
    simp only [ne_eq, not_exists, not_and, not_not] at h
    have : (Function.support fun cs => ENNReal.ofReal ↑(compareAndSetSmallStepSemantics v e_l e_c e_s s deterministic cs.1 cs.2))
        ⊆ {(⟨[Prog| ↯ ], s⟩ : (Program Var) × (State Var))} := by {
      simp only [Function.support, compareAndSetSmallStepSemantics, substituteStack, substituteHeap,
        ne_eq, true_and, not_exists, ENNReal.ofReal_eq_zero, not_le, coe_pos,
        Set.subset_singleton_iff, Set.mem_setOf_eq, Prod.forall, Prod.mk.injEq]
      intro c s h'
      split at h'
      case h_1 _ s' =>
        rw [zero_lt_iteOneZero] at h'
        obtain ⟨l, h_l, q, h_q, h_s⟩ := h'
        specialize h l h_l
        simp only [h, reduceCtorEq] at h_q
      case h_2 _ s' =>
        rw [zero_lt_iteOneZero] at h'
        obtain ⟨h_s, _⟩ := h'
        use rfl, h_s.symm
      case h_3 _ s' => exfalso; exact (lt_self_iff_false 0).mp h'
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal
      ↑(compareAndSetSmallStepSemantics _ _ _ _ _ _ _ _))]
    simp only [compareAndSetSmallStepSemantics, not_exists, true_and, ENNReal.ofReal_eq_one,
      Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
    by_cases h_l : ∃ l : ℕ+, l = e_l s.stack
    case pos =>
      obtain ⟨l, h_l⟩ := h_l
      left; use l, h_l.symm, h l h_l
    case neg =>
      simp only [not_exists] at h_l
      right; intro l h_l'
      exact h_l l h_l'.symm

theorem alloc_sum_one (s : State Var) (h_n : ↑n = e s.stack) (h_not_alloc : isNotAlloc s.heap m n) :
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| v ≔ alloc(e)]) s (allocation m) cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  have : (Function.support fun cs ↦ ENNReal.ofReal (allocateSmallStepSemantics v e s (allocation m) cs.1 cs.2))
      ⊆ {(⟨[Prog| ↓ ], ⟨substituteVar s.stack v m, allocateLoc s.heap m n⟩⟩ : (Program Var) × (State Var))} := by {
    simp only [Function.support, allocateSmallStepSemantics, allocation.injEq, substituteStack,
      allocateHeap, exists_eq_left', reduceCtorEq, not_exists, false_and, iteOneZero_false, ne_eq,
      ENNReal.ofReal_eq_zero, not_le, coe_pos, Set.subset_singleton_iff, Set.mem_setOf_eq,
      Prod.forall, Prod.mk.injEq]
    intro c s h
    split at h
    case h_1 s' =>
      rw [zero_lt_iteOneZero] at h
      obtain ⟨n', h_n', h_not_alloc', h_stack⟩ := h
      simp only [← h_stack, mk.injEq, true_and]
      rw [← h_n, Nat.cast_inj] at h_n'
      rw [h_n']
    case h_2 s' => simp only [lt_self_iff_false] at h
    case h_3 s' => simp only [lt_self_iff_false] at h
  }
  rw [← tsum_subtype_eq_of_support_subset this]; clear this
  rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(allocateSmallStepSemantics _  _ _ _ _ _))]
  simp only [allocateSmallStepSemantics, allocation.injEq, substituteStack, allocateHeap, mk.injEq,
    exists_eq_left', true_and, ENNReal.ofReal_eq_one, Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
  use n

theorem alloc_sum_one_abort (s : State Var) (h_n : ∀ n: ℕ, ↑n ≠ e s.stack) :
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| v ≔ alloc(e)]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  have : (Function.support fun cs ↦ ENNReal.ofReal (allocateSmallStepSemantics v e s deterministic cs.1 cs.2))
      ⊆ {(⟨[Prog| ↯ ], s⟩ : (Program Var) × (State Var))} := by {
    simp only [allocateSmallStepSemantics, reduceCtorEq, substituteStack, allocateHeap, false_and,
      exists_const, iteOneZero_false, not_exists, true_and, Set.subset_singleton_iff,
      Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos, Prod.forall,
      Prod.mk.injEq]
    intro c s h
    split at h
    case h_1 s' => simp only [lt_self_iff_false] at h
    case h_2 s' =>
      rw [zero_lt_iteOneZero] at h
      use rfl, h.left.symm
    case h_3 s' => simp only [lt_self_iff_false] at h
  }
  rw [← tsum_subtype_eq_of_support_subset this]; clear this
  rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(allocateSmallStepSemantics _  _ _ _ _ _))]
  simp only [allocateSmallStepSemantics, not_exists, true_and, ENNReal.ofReal_eq_one,
    Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
  exact h_n

theorem free_sum_one (s : State Var):
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| free(e_l, e_n)]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  by_cases h : ∃ l : ℕ+, l = e_l s.stack ∧ ∃ n : ℕ, n = e_n s.stack ∧ isAlloc s.heap l n
  case pos =>
    obtain ⟨l, h_l, n, h_n, h_alloc⟩ := h
    have : (Function.support fun cs ↦ ENNReal.ofReal (freeSmallStepSemantics e_l e_n s deterministic cs.1 cs.2))
        ⊆ {(⟨[Prog| ↓ ], ⟨s.stack, freeLoc s.heap l n⟩⟩ : (Program Var) × (State Var))} := by {
      simp only [freeSmallStepSemantics, freeHeap, true_and, not_exists, exists_and_right,
        Set.subset_singleton_iff, Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le,
        coe_pos, Prod.forall, Prod.mk.injEq]
      intro c s h
      split at h
      case h_1 =>
        rw [zero_lt_iteOneZero] at h
        obtain ⟨l', h_l', n', h_n', h_alloc', h_stack⟩ := h
        simp only [← h_stack, mk.injEq, true_and]
        rw [← h_l, Nat.cast_inj, PNat.coe_inj] at h_l'
        rw [← h_n, Nat.cast_inj] at h_n'
        rw [h_l', h_n']
      case h_2 =>
        exfalso
        rw [zero_lt_iteOneZero] at h
        obtain ⟨_, (⟨l', h_l', n', h_n', h_not_alloc'⟩ | ⟨_, h_n'⟩ | h)⟩ := h
        · apply h_not_alloc'
          rw [← h_l, Nat.cast_inj, PNat.coe_inj] at h_l'
          rw [← h_n, Nat.cast_inj] at h_n'
          rw [← h_l', h_n']
          exact h_alloc
        · apply h_n' n
          exact h_n
        · exact h l h_l.symm
      case h_3 => simp only [lt_self_iff_false] at h
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(freeSmallStepSemantics _ _ _ _ _ _))]
    simp only [freeSmallStepSemantics, not_exists, exists_and_right, true_and, ENNReal.ofReal_eq_one,
      Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
    use l, h_l, n, h_n, h_alloc
    rfl
  case neg =>
    simp only [not_exists, not_and] at h
    have : (Function.support fun cs ↦ ENNReal.ofReal (freeSmallStepSemantics e_l e_n s deterministic cs.1 cs.2))
        ⊆ {(⟨[Prog| ↯ ], s⟩ : (Program Var) × (State Var))} := by {
      simp only [Function.support, freeSmallStepSemantics, freeHeap, true_and, not_exists,
        exists_and_right, ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos, Set.subset_singleton_iff,
        Set.mem_setOf_eq, Prod.forall, Prod.mk.injEq]
      intro c s h'
      split at h'
      case h_1 =>
        exfalso
        rw [zero_lt_iteOneZero] at h'
        obtain ⟨l, h_l, n, h_n, h_alloc, h_stack⟩ := h'
        apply h l h_l n h_n
        exact h_alloc
      case h_2 =>
        rw [zero_lt_iteOneZero] at h'
        rw [h'.left]
        trivial
      case h_3 => simp only [lt_self_iff_false] at h'
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(freeSmallStepSemantics _ _ _ _ _ _))]
    simp only [freeSmallStepSemantics, not_exists, exists_and_right, true_and,
      ENNReal.ofReal_eq_one, Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
    by_cases h_l : ∃ l : ℕ+, l = e_l s.stack
    case pos =>
      obtain ⟨l, h_l⟩ := h_l
      by_cases h_n : ∃ n : ℕ, n = e_n s.stack
      case pos =>
        obtain ⟨n, h_n⟩ := h_n
        specialize h l h_l n h_n
        left
        use l, h_l.symm, n
      case neg =>
        simp only [not_exists] at h_n
        right; left
        apply And.intro
        · use l, h_l.symm
        · intro n' h_n'; exact h_n n' h_n'
    case neg =>
      simp only [not_exists] at h_l
      right; right
      intro l h_l'
      exact (h_l l) h_l'.symm

theorem probabilisticBranching_sum_one (s : State Var):
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| pif e then [[c₁]] else [[c₂]] fi]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  by_cases h_c : c₁ = c₂
  case pos =>
    have : (Function.support fun cs ↦ ENNReal.ofReal
        (probabilisticBranchingSmallStepSemantics e c₁ c₂ s deterministic cs.1 cs.2))
        ⊆ {(⟨c₁, s⟩ : (Program Var) × (State Var))} := by {
      simp only [probabilisticBranchingSmallStepSemantics, true_and, Set.subset_singleton_iff,
        Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos, Prod.forall,
        Prod.mk.injEq]
      intro c s h
      split_ifs at h
      case pos s' h_s h_c => use h_c.left.symm, h_s.right.symm
      case pos s' h_s _ h_c' => use h_c'.symm, h_s.right.symm
      case pos s' h_s _ _ h_c' => rw [h_c]; use h_c'.symm, h_s.right.symm
      case neg => simp only [lt_self_iff_false] at h
      case neg => simp only [lt_self_iff_false] at h
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal
      ↑(probabilisticBranchingSmallStepSemantics _ _ _ _ _ _ _))]
    simp only [probabilisticBranchingSmallStepSemantics, and_self, ↓reduceIte, true_and,
      ENNReal.ofReal_eq_one, Set.Icc.coe_eq_one, ite_eq_left_iff]
    intro h; exfalso; exact h h_c.symm
  case neg =>
    have : (Function.support fun cs ↦ ENNReal.ofReal
        (probabilisticBranchingSmallStepSemantics e c₁ c₂ s deterministic cs.1 cs.2))
        ⊆ {(⟨c₁, s⟩ : (Program Var) × (State Var)), ⟨c₂, s⟩} := by {
      simp only [probabilisticBranchingSmallStepSemantics, true_and, Function.support_subset_iff,
        ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos, Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.forall, Prod.mk.injEq]
      intro c s h
      split_ifs at h
      case pos s h_s h_c' => left; use h_c'.left.symm, h_s.right.symm
      case pos s h_s _ h_c' => left; use h_c'.symm, h_s.right.symm
      case pos s h_s _ _ h_c' => right; use h_c'.symm, h_s.right.symm
      case neg => simp only [lt_self_iff_false] at h
      case neg => simp only [lt_self_iff_false] at h
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    have : (⟨c₁, s⟩ : (Program Var) × (State Var)) ≠ ⟨c₂, s⟩ := by simp [h_c]
    rw [tsum_pair (fun cs => ENNReal.ofReal
      ↑(probabilisticBranchingSmallStepSemantics _ _ _ _ _ _ _)) this]
    simp only [probabilisticBranchingSmallStepSemantics, and_self, ↓reduceIte, true_and, and_true]
    rw [if_neg, if_neg, if_neg]
    · rw [← ENNReal.ofReal_add]
      · simp only [coe_symm_eq, add_sub_cancel, ENNReal.ofReal_one]
      · exact nonneg'
      · exact nonneg'
    · exact h_c
    · intro h; exact h_c h.left
    · intro h; exact h_c h.right.symm

theorem conditionalBranching_sum_one (s : State Var):
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| if e then [[c₁]] else [[c₂]] fi]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  cases eq_or_ne c₁ c₂
  case inl h_c =>
    have : (Function.support fun cs ↦ ENNReal.ofReal
        (conditionalBranchingSmallStepSemantics e c₁ c₂ s deterministic cs.1 cs.2))
        ⊆ {(⟨c₁, s⟩ : (Program Var) × (State Var))} := by {
      simp only [conditionalBranchingSmallStepSemantics, Bool.not_eq_true, true_and,
        Function.support_subset_iff, ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos,
        zero_lt_iteOneZero, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp, Prod.forall,
        Prod.mk.injEq, forall_eq', and_true]
      rintro c (⟨_, h_c'⟩ | ⟨_, h_c'⟩)
      · exact h_c'.symm
      · rw [h_c]; exact h_c'.symm
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal
      ↑(conditionalBranchingSmallStepSemantics _ _ _ _ _ _ _))]
    simp only [conditionalBranchingSmallStepSemantics, and_true, Bool.not_eq_true, true_and,
      ENNReal.ofReal_eq_one, Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
    by_cases h : e s.stack
    case pos => left; use h
    case neg => right; simp only [Bool.not_eq_true] at h; use h, h_c.symm
  case inr h_c =>
  have : (Function.support fun cs ↦ ENNReal.ofReal
      (conditionalBranchingSmallStepSemantics e c₁ c₂ s deterministic cs.1 cs.2))
      ⊆ {(⟨c₁, s⟩ : (Program Var) × (State Var)), ⟨c₂, s⟩} := by {
    simp only [conditionalBranchingSmallStepSemantics, Bool.not_eq_true, true_and,
      Function.support_subset_iff, ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos,
      zero_lt_iteOneZero, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp, Prod.forall,
      Prod.mk.injEq, forall_eq', and_true]
    rintro c (⟨_, h_c⟩ | ⟨_, h_c⟩)
    · left; exact h_c.symm
    · right; exact h_c.symm
  }
  rw [← tsum_subtype_eq_of_support_subset this]; clear this
  have : (⟨c₁, s⟩ : (Program Var) × (State Var)) ≠ ⟨c₂, s⟩ := by simp [h_c]
  rw [tsum_pair (fun cs => ENNReal.ofReal
    ↑(conditionalBranchingSmallStepSemantics _ _ _ _ _ _ _)) this]
  simp only [conditionalBranchingSmallStepSemantics, and_true, Bool.not_eq_true, true_and]
  by_cases h : e s.stack
  case pos =>
    rw [iteOneZero_pos, iteOneZero_neg]
    · simp
    · simp only [not_or, not_and, Bool.not_eq_false]
      apply And.intro ?_ h
      intro _; exact h_c
    · left; exact h
  case neg =>
    simp only [Bool.not_eq_true] at h
    rw [iteOneZero_neg, iteOneZero_pos]
    · simp
    · right; exact h
    · simp only [not_or, Bool.not_eq_true, not_and]
      use h
      intro _; exact Ne.symm h_c

theorem loop_sum_one (s : State Var):
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| while e begin [[c]] fi]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  by_cases h : e s.stack
  case pos =>
    have : (Function.support fun cs ↦ ENNReal.ofReal
        (loopSmallStepSemantics e c s deterministic cs.1 cs.2))
        ⊆ {(⟨[Prog| [[c]] ; while e begin [[c]] fi], s⟩ : (Program Var) × (State Var))} := by {
      simp only [loopSmallStepSemantics, Bool.not_eq_true, true_and, Set.subset_singleton_iff,
        Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos, Prod.forall,
        Prod.mk.injEq]
      intro c s h'
      split at h'
      case h_1 =>
        exfalso
        rw [zero_lt_iteOneZero] at h'
        simp only [h'.right, Bool.false_eq_true] at h
      case h_2 =>
        rw [zero_lt_iteOneZero] at h'
        use h'.left, h'.right.left.symm
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(loopSmallStepSemantics _ _ _ _ _ _))]
    simp only [loopSmallStepSemantics, true_and, ENNReal.ofReal_eq_one, Set.Icc.coe_eq_one,
      iteOneZero_eq_one_def]
    exact h
  case neg =>
    have : (Function.support fun cs ↦ ENNReal.ofReal
        (loopSmallStepSemantics e c s deterministic cs.1 cs.2))
        ⊆ {(⟨[Prog| ↓], s⟩ : (Program Var) × (State Var))} := by {
      simp only [loopSmallStepSemantics, Bool.not_eq_true, true_and, Set.subset_singleton_iff,
        Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos, Prod.forall,
        Prod.mk.injEq]
      intro c s h'
      split at h'
      case h_1 =>
        rw [zero_lt_iteOneZero] at h'
        use rfl, h'.left.symm
      case h_2 =>
        exfalso
        rw [zero_lt_iteOneZero] at h'
        exact h h'.right.right
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(loopSmallStepSemantics _ _ _ _ _ _))]
    simp only [loopSmallStepSemantics, true_and, ENNReal.ofReal_eq_one, Set.Icc.coe_eq_one,
      iteOneZero_eq_one_def]
    exact h

theorem sequential_sum_one_term (s : State Var):
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| ↓ ; [[c₂]]]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  simp only [↓reduceIte, true_and]
  have : (Function.support fun cs ↦ ENNReal.ofReal (iteOneZero (s = cs.2 ∧ cs.1 = c₂)))
      ⊆ {(⟨c₂, s⟩ : (Program Var) × (State Var))} := by simp
  rw [← tsum_subtype_eq_of_support_subset this]; clear this
  rw [tsum_singleton (⟨c₂, s⟩ : (Program Var) × (State Var))
    (fun cs => ENNReal.ofReal ↑(iteOneZero (s = cs.2 ∧ cs.1 = c₂)))]
  simp only [and_self, iteOneZero_true, Set.Icc.coe_one, ENNReal.ofReal_one]

theorem sequential_sum_one_abort (s : State Var):
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| ↯ ; [[c₂]]]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  simp only [reduceCtorEq, ↓reduceIte, true_and]
  have : (Function.support fun cs ↦ ENNReal.ofReal (iteOneZero (s = cs.2 ∧ cs.1 = [Prog| ↯])))
      ⊆ {(⟨[Prog| ↯], s⟩ : (Program Var) × (State Var))} := by simp
  rw [← tsum_subtype_eq_of_support_subset this]; clear this
  rw [tsum_singleton (⟨[Prog| ↯], s⟩ : (Program Var) × (State Var))
    (fun cs => ENNReal.ofReal ↑(iteOneZero (s = cs.2 ∧ cs.1 = [Prog| ↯])))]
  simp only [and_self, iteOneZero_true, Set.Icc.coe_one, ENNReal.ofReal_one]

open Classical

private noncomputable def inj (c₁ c₂ : Program Var) (s : State Var) (a : Action) :
  ↑(Function.support (fun cs : (Program Var) × (State Var) =>
    ENNReal.ofReal ↑(semantics c₁ s a cs.1 cs.2)))
  → (Program Var) × (State Var):=
  fun cs => match cs with
  | ⟨⟨c, s⟩, _⟩ => if c = [Prog| ↯] then ⟨[Prog| ↯], s⟩ else ⟨[Prog| [[c]] ; [[c₂]]], s⟩

private theorem inj_injective (c₁ c₂ : Program Var) (s : State Var) (a : Action) :
    Function.Injective (@inj Var c₁ c₂ s a) := by
  intro cs₁ cs₂ h
  unfold inj at h
  simp only at h
  split_ifs at h
  case pos h_abort₁ h_abort₂ =>
    simp only [Prod.mk.injEq, true_and] at h
    simp only [Subtype.ext_iff, Prod.ext_iff]
    apply And.intro
    · rw [h_abort₁, h_abort₂]
    · exact h
  case neg => simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
  case pos => simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
  case neg h_abort₁ h_abort₂ =>
    simp only [Prod.mk.injEq, sequential.injEq, and_true] at h
    apply Subtype.ext_val
    exact Prod.ext_iff.mpr h

theorem tsum_sequential_cont (s : State Var)
    (h_term : c₁ ≠ [Prog| ↓]) (h_abort : c₁ ≠ [Prog| ↯]) :
    (∑' cs : (Program Var) × (State Var),
        ENNReal.ofReal ↑(semantics [Prog| [[c₁]] ; [[c₂]]] s a cs.1 cs.2))
    = (∑' cs : (Program Var) × (State Var),
        ENNReal.ofReal ↑(semantics c₁ s a cs.1 cs.2)) := by
  apply tsum_eq_tsum_of_ne_zero_bij (inj c₁ c₂ s a) (inj_injective c₁ c₂ s a)
  · simp only [Function.support_subset_iff, ne_eq, Set.mem_range, Subtype.exists,
      Function.mem_support, Prod.exists, Prod.forall]
    intro c s' h
    by_cases h_c : ∃ c₁', c = [Prog| [[c₁']] ; [[c₂]]]
    case pos =>
      obtain ⟨c₁', rfl⟩ := h_c
      use c₁', s'
      unfold semantics programSmallStepSemantics at h
      simp only [reduceCtorEq, and_false, iteOneZero_false, ↓reduceIte, if_neg h_abort,
        if_neg h_term, not_le, coe_pos] at h
      split at h
      case isTrue => simp only [Set.Icc.coe_zero, ENNReal.ofReal_zero, not_true_eq_false] at h
      case isFalse h_abort₁ =>
        use h
        simp only [inj, h_abort₁, ↓reduceIte]
    case neg =>
      cases eq_or_ne c [Prog| ↯ ]
      case inl h_c_abort =>
        rw [h_c_abort] at h
        use [Prog| ↯], s'
        unfold semantics programSmallStepSemantics at h
        simp only [and_true, ↓reduceIte, if_neg h_abort, if_neg h_term] at h
        unfold semantics
        use h
        simp only [inj, ↓reduceIte, h_c_abort]
      case inr h_c_abort =>
        unfold semantics programSmallStepSemantics at h
        simp only [if_neg h_c_abort, if_neg h_abort, if_neg h_term] at h
        split at h
        case h_1 =>
          split_ifs at h
          case pos => simp only [Set.Icc.coe_zero, ENNReal.ofReal_zero, not_true_eq_false] at h
          case pos c₁' c₂' h_abort₁ h_c₂ =>
            use c₁', s', h
            simp only [inj, h_c₂, if_neg h_abort₁]
          case neg => simp only [Set.Icc.coe_zero, ENNReal.ofReal_zero, not_true_eq_false] at h
        case h_2 => simp only [Set.Icc.coe_zero, ENNReal.ofReal_zero, not_true_eq_false] at h
  · intro cs
    unfold semantics inj
    rw [programSmallStepSemantics]
    simp only [h_term, ↓reduceIte, h_abort]
    split_ifs
    case pos h_abort₁ _ => simp only [h_abort₁]
    case neg _ h => simp only [not_true_eq_false] at h
    case pos _ h => simp only at h
    case neg h_abort₁ _ => simp only [h_abort₁, ↓reduceIte]

theorem concurrent_sum_one_term (s : State Var):
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| ↓ || ↓]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  simp only [↓reduceIte, true_and]
  have : (Function.support fun cs ↦ ENNReal.ofReal (iteOneZero (cs.1 = [Prog| ↓] ∧ s = cs.2)))
      ⊆ {(⟨[Prog| ↓], s⟩ : (Program Var) × (State Var))} := by simp
  rw [← tsum_subtype_eq_of_support_subset this]; clear this
  rw [tsum_singleton (⟨[Prog| ↓], s⟩ : (Program Var) × (State Var))
    (fun cs => ENNReal.ofReal ↑(iteOneZero (cs.1 = [Prog| ↓] ∧ s = cs.2)))]
  simp only [and_self, iteOneZero_true, Set.Icc.coe_one, ENNReal.ofReal_one]

theorem concurrent_sum_one_abort_left (s : State Var):
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| ↯ || [[c₂]]]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  simp only [reduceCtorEq, false_and, ↓reduceIte, true_or, true_and]
  have : (Function.support fun cs ↦ ENNReal.ofReal (iteOneZero (s = cs.2 ∧ cs.1 = [Prog| ↯])))
      ⊆ {(⟨[Prog| ↯], s⟩ : (Program Var) × (State Var))} := by simp
  rw [← tsum_subtype_eq_of_support_subset this]; clear this
  rw [tsum_singleton (⟨[Prog| ↯], s⟩ : (Program Var) × (State Var))
    (fun cs => ENNReal.ofReal ↑(iteOneZero (s = cs.2 ∧ cs.1 = [Prog| ↯])))]
  simp only [and_self, iteOneZero_true, Set.Icc.coe_one, ENNReal.ofReal_one]

theorem concurrent_sum_one_abort_right (s : State Var):
    ∑' (cs : Program Var × State Var),
    ENNReal.ofReal (semantics ([Prog| [[c₁]] || ↯]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold semantics programSmallStepSemantics
  simp only [reduceCtorEq, and_false, ↓reduceIte, or_true, true_and]
  have : (Function.support fun cs ↦ ENNReal.ofReal (iteOneZero (s = cs.2 ∧ cs.1 = [Prog| ↯])))
      ⊆ {(⟨[Prog| ↯], s⟩ : (Program Var) × (State Var))} := by simp
  rw [← tsum_subtype_eq_of_support_subset this]; clear this
  rw [tsum_singleton (⟨[Prog| ↯], s⟩ : (Program Var) × (State Var))
    (fun cs => ENNReal.ofReal ↑(iteOneZero (s = cs.2 ∧ cs.1 = [Prog| ↯])))]
  simp only [and_self, iteOneZero_true, Set.Icc.coe_one, ENNReal.ofReal_one]

private noncomputable def inj_left (c₁ c₂ : Program Var) (s : State Var) (a : Action) :
  ↑(Function.support (fun cs : (Program Var) × (State Var) =>
    ENNReal.ofReal ↑(semantics c₁ s a cs.1 cs.2)))
  → (Program Var) × (State Var):=
  fun cs => match cs with
  | ⟨⟨c, s⟩, _⟩ => if c = [Prog| ↯] then ⟨[Prog| ↯], s⟩ else ⟨[Prog| [[c]] || [[c₂]]], s⟩

private theorem inj_left_injective (c₁ c₂ : Program Var) (s : State Var) (a : Action) :
    Function.Injective (@inj_left Var c₁ c₂ s a) := by
  intro cs₁ cs₂ h
  unfold inj_left at h
  simp only at h
  split_ifs at h
  case pos h_abort₁ h_abort₂ =>
    simp only [Prod.mk.injEq, true_and] at h
    simp only [Subtype.ext_iff, Prod.ext_iff]
    apply And.intro
    · rw [h_abort₁, h_abort₂]
    · exact h
  case neg => simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
  case pos => simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
  case neg h_abort₁ h_abort₂ =>
    simp only [Prod.mk.injEq, concurrent.injEq, and_true] at h
    apply Subtype.ext_val
    exact Prod.ext_iff.mpr h

theorem tsum_concurrent_cont_left (s : State Var)
    (h_term₁ : c₁ ≠ [Prog| ↓]) (h_abort₁ : c₁ ≠ [Prog| ↯]) (h_abort₂ : c₂ ≠ [Prog| ↯]) :
    (∑' cs : (Program Var) × (State Var),
        ENNReal.ofReal ↑(semantics [Prog| [[c₁]] || [[c₂]]] s a.concurrentLeft cs.1 cs.2))
    = (∑' cs : (Program Var) × (State Var),
        ENNReal.ofReal ↑(semantics c₁ s a cs.1 cs.2)) := by
  apply tsum_eq_tsum_of_ne_zero_bij (inj_left c₁ c₂ s a) (inj_left_injective c₁ c₂ s a)
  · simp only [Function.support_subset_iff, ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos,
    Set.mem_range, Subtype.exists, Function.mem_support, Prod.exists, Prod.forall]
    intro c s' h
    by_cases h_c : ∃ c₁', c = [Prog| [[c₁']] || [[c₂]]]
    case pos =>
      obtain ⟨c₁', rfl⟩ := h_c
      use c₁', s'
      unfold semantics programSmallStepSemantics at h
      simp only [h_term₁, false_and, ↓reduceIte, h_abort₁, h_abort₂, or_self, reduceCtorEq] at h
      split at h
      case isTrue => simp only [lt_self_iff_false] at h
      case isFalse h_abort₁ =>
        use h
        simp only [inj_left, h_abort₁, ↓reduceIte]
    case neg =>
      cases eq_or_ne c [Prog| ↯ ]
      case inl h_c_abort =>
        rw [h_c_abort] at h
        use [Prog| ↯], s'
        unfold semantics programSmallStepSemantics at h
        simp only [h_term₁, false_and, ↓reduceIte, h_abort₁, h_abort₂, or_self] at h
        unfold semantics
        use h
        simp only [inj_left, ↓reduceIte, h_c_abort]
      case inr h_c_abort =>
        unfold semantics programSmallStepSemantics at h
        simp only [h_term₁, false_and, ↓reduceIte, h_abort₁, h_abort₂, or_self, h_c_abort] at h
        split at h
        case h_1 =>
          split_ifs at h
          case pos => simp only [lt_self_iff_false] at h
          case pos c₁' c₂' h_abort₁ h_c₂ =>
            use c₁', s', h
            simp only [inj_left, h_c₂, if_neg h_abort₁]
          case neg => simp only [lt_self_iff_false] at h
        case h_2 => simp only [lt_self_iff_false] at h
  · intro cs
    unfold semantics inj_left
    rw [programSmallStepSemantics]
    simp only [h_term₁, false_and, ↓reduceIte, h_abort₁, h_abort₂, or_self]
    split_ifs
    case pos h_abort₁ _ => simp only [h_abort₁]
    case neg _ h => simp only [not_true_eq_false] at h
    case pos _ h => simp only at h
    case neg h_abort₁ _ => simp only [h_abort₁, ↓reduceIte]

private noncomputable def inj_right (c₁ c₂ : Program Var) (s : State Var) (a : Action) :
  ↑(Function.support (fun cs : (Program Var) × (State Var) =>
    ENNReal.ofReal ↑(semantics c₂ s a cs.1 cs.2)))
  → (Program Var) × (State Var):=
  fun cs => match cs with
  | ⟨⟨c, s⟩, _⟩ => if c = [Prog| ↯] then ⟨[Prog| ↯], s⟩ else ⟨[Prog| [[c₁]] || [[c]]], s⟩

private theorem inj_right_injective (c₁ c₂ : Program Var) (s : State Var) (a : Action) :
    Function.Injective (@inj_right Var c₁ c₂ s a) := by
  intro cs₁ cs₂ h
  unfold inj_right at h
  simp only at h
  split_ifs at h
  case pos h_abort₁ h_abort₂ =>
    simp only [Prod.mk.injEq, true_and] at h
    simp only [Subtype.ext_iff, Prod.ext_iff]
    apply And.intro
    · rw [h_abort₁, h_abort₂]
    · exact h
  case neg => simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
  case pos => simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
  case neg h_abort₁ h_abort₂ =>
    simp only [Prod.mk.injEq, concurrent.injEq, true_and] at h
    apply Subtype.ext_val
    exact Prod.ext_iff.mpr h

theorem tsum_concurrent_cont_right (s : State Var)
    (h_term₂ : c₂ ≠ [Prog| ↓]) (h_abort₁ : c₁ ≠ [Prog| ↯]) (h_abort₂ : c₂ ≠ [Prog| ↯]) :
    (∑' cs : (Program Var) × (State Var),
        ENNReal.ofReal ↑(semantics [Prog| [[c₁]] || [[c₂]]] s a.concurrentRight cs.1 cs.2))
    = (∑' cs : (Program Var) × (State Var),
        ENNReal.ofReal ↑(semantics c₂ s a cs.1 cs.2)) := by
  apply tsum_eq_tsum_of_ne_zero_bij (inj_right c₁ c₂ s a) (inj_right_injective c₁ c₂ s a)
  · simp only [Function.support_subset_iff, ne_eq, ENNReal.ofReal_eq_zero, not_le, coe_pos,
    Set.mem_range, Subtype.exists, Function.mem_support, Prod.exists, Prod.forall]
    intro c s' h
    by_cases h_c : ∃ c₂', c = [Prog| [[c₁]] || [[c₂']]]
    case pos =>
      obtain ⟨c₂', rfl⟩ := h_c
      use c₂', s'
      unfold semantics programSmallStepSemantics at h
      simp only [h_term₂, and_false, ↓reduceIte, h_abort₁, h_abort₂, or_self, reduceCtorEq] at h
      split at h
      case isTrue => simp only [lt_self_iff_false] at h
      case isFalse h_abort₁ =>
        use h
        simp only [inj_right, h_abort₁, ↓reduceIte]
    case neg =>
      cases eq_or_ne c [Prog| ↯ ]
      case inl h_c_abort =>
        rw [h_c_abort] at h
        use [Prog| ↯], s'
        unfold semantics programSmallStepSemantics at h
        simp only [h_term₂, and_false, ↓reduceIte, h_abort₁, h_abort₂, or_self] at h
        unfold semantics
        use h
        simp only [inj_right, ↓reduceIte, h_c_abort]
      case inr h_c_abort =>
        unfold semantics programSmallStepSemantics at h
        simp only [h_term₂, and_false, ↓reduceIte, h_abort₁, h_abort₂, or_self, h_c_abort] at h
        split at h
        case h_1 =>
          split_ifs at h
          case pos => simp only [lt_self_iff_false] at h
          case pos c₁' c₂' h_abort₁ h_c₂ =>
            use c₂', s', h
            simp only [inj_right, h_c₂, if_neg h_abort₁]
          case neg => simp only [lt_self_iff_false] at h
        case h_2 => simp only [lt_self_iff_false] at h
  · intro cs
    unfold semantics inj_right
    rw [programSmallStepSemantics]
    simp only [h_term₂, and_false, ↓reduceIte, h_abort₁, h_abort₂, or_self]
    split_ifs
    case pos h_abort₁ _ => simp only [h_abort₁]
    case neg _ h => simp only [not_true_eq_false] at h
    case pos _ h => simp only at h
    case neg h_abort₁ _ => simp only [h_abort₁, ↓reduceIte]

theorem sum_one (c : Program Var) (s : State Var) :
    ∀ a ∈ enabledAction c s,
    ∑' (cs : (Program Var) × (State Var)),
    ENNReal.ofReal (semantics c s a cs.1 cs.2) = 1 := by
  intro a h_a
  induction c generalizing s a with
  | terminated => simp only [enabledAction, Set.mem_empty_iff_false] at h_a
  | abort => simp only [enabledAction, Set.mem_empty_iff_false] at h_a
  | skip' =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    exact skip_sum_one s
  | assign v e =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    exact assign_sum_one s
  | mutate e e' =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    exact mutate_sum_one s
  | lookup v e =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    exact lookup_sum_one s
  | compareAndSet v e_l e_c e_s =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    exact compareAndSet_sum_one s
  | allocate v e =>
    simp only [enabledAction] at h_a
    split at h_a
    case isTrue _ =>
      obtain ⟨m, h_a, n', h_n', h_not_alloc⟩ := h_a
      rw [h_a]
      exact alloc_sum_one s h_n' h_not_alloc
    case isFalse h_n =>
      simp only [not_exists] at h_n
      simp only [Set.mem_singleton_iff] at h_a
      rw [h_a]
      exact alloc_sum_one_abort s h_n
  | free' e_l e_n =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    exact free_sum_one s
  | probabilisticBranching e c₁ c₂ =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    exact probabilisticBranching_sum_one s
  | conditionalBranching e c₁ c₂ =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    exact conditionalBranching_sum_one s
  | loop e c₁ =>
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a]
    exact loop_sum_one s
  | sequential c₁ c₂ ih₁ =>
    simp only [enabledAction] at h_a
    split_ifs at h_a
    case pos h_c =>
      simp only [Set.mem_singleton_iff] at h_a
      rw [h_a]
      cases h_c
      case inl h_c_term =>
        rw [h_c_term]
        exact sequential_sum_one_term s
      case inr h_c_abort =>
        rw [h_c_abort]
        exact sequential_sum_one_abort s
    case neg h_c =>
      simp only [not_or] at h_c
      rw [tsum_sequential_cont s h_c.left h_c.right]
      exact ih₁ s a h_a
  | concurrent c₁ c₂ ih₁ ih₂ =>
    simp only [enabledAction] at h_a
    split_ifs at h_a
    case pos h_c =>
      simp only [Set.mem_singleton_iff] at h_a
      cases h_c
      case inl h_c =>
        rw [h_c.left, h_c.right, h_a]
        exact concurrent_sum_one_term s
      case inr h_c =>
        cases h_c
        case inl h_c =>
          rw [h_c, h_a]
          exact concurrent_sum_one_abort_left s
        case inr h_c =>
          rw [h_c, h_a]
          exact concurrent_sum_one_abort_right s
    case neg h_c =>
      simp only [not_or, not_and] at h_c
      obtain ⟨_, h_abort₁, h_abort₂⟩ := h_c
      simp only [ne_eq, Set.mem_union, Set.mem_setOf_eq] at h_a
      cases h_a
      case inl h_a =>
        obtain ⟨a', rfl, h_term₁, h_a'⟩ := h_a
        rw [tsum_concurrent_cont_left s h_term₁ h_abort₁ h_abort₂]
        exact ih₁ s a' h_a'
      case inr h_a =>
        obtain ⟨a', rfl, h_term₂, h_a'⟩ := h_a
        rw [tsum_concurrent_cont_right s h_term₂ h_abort₁ h_abort₂]
        exact ih₂ s a' h_a'

end Semantics
