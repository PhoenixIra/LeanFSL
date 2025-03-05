import InvLimDiss.Program.Semantics
import InvLimDiss.Program.Enabled
import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace Semantics

open Syntax State Action Program unitInterval

variable {Var : Type}

theorem skip_sum_one (s : State Var) :
    ∑' (cs : (Program Var) × (State Var)),
    ENNReal.ofReal (programSmallStepSemantics skip' s deterministic cs.1 cs.2)
    = 1 := by
  unfold programSmallStepSemantics
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
    ENNReal.ofReal (programSmallStepSemantics ([Prog| v ≔ e]) s deterministic cs.1 cs.2)
    = 1 := by
  unfold programSmallStepSemantics
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
    ENNReal.ofReal (programSmallStepSemantics ([Prog| e *≔ e']) s deterministic cs.1 cs.2)
    = 1 := by
  unfold programSmallStepSemantics
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
    }
    rw [← tsum_subtype_eq_of_support_subset this]; clear this
    rw [tsum_singleton _ (fun cs => ENNReal.ofReal ↑(mutateSmallStepSemantics _ _ _ _ _ _))]
    simp only [mutateSmallStepSemantics, ne_eq, substituteHeap, mk.injEq, true_and,
      ENNReal.ofReal_eq_one, Set.Icc.coe_eq_one, iteOneZero_eq_one_def]
    use l, h_e.symm
  case neg h =>
    sorry


theorem sum_one (c : Program Var) (s : State Var) :
    ∀ a ∈ enabledAction c s,
    ∑' (cs : (Program Var) × (State Var)),
    ENNReal.ofReal (programSmallStepSemantics c s a cs.1 cs.2) = 1 := by
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



end Semantics
