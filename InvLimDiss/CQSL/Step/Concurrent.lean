import InvLimDiss.CQSL.Step.Basic
import InvLimDiss.Program.Support


namespace CQSL

variable {Var : Type}

open Syntax Semantics QSL unitInterval Action State HeapValue Classical Function

theorem tsum_concurrent_term_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : reachState Var,
    (semantics [Prog| ↓ || ↓] s deterministic cs.prog cs.state) * inner cs.prog cs.state)
    = inner [Prog| ↓] s := by sorry
  -- rw[← tsum_subtype_eq_of_support_subset]
  -- pick_goal 2
  -- · apply mul_support_superset_left
  --   exact tsum_sequential_term_support_superset s
  -- · split
  --   case isTrue h_abort =>
  --     rw [dif_pos h_abort, tsum_empty]
  --   case isFalse h_ne_abort =>
  --     rw [dif_neg h_ne_abort]
  --     simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, reachState.prog, reachState.state]
  --     rw [tsum_singleton (⟨⟨c, s⟩, h_ne_abort⟩ : reachState Var)
  --       (fun cs => semantics _ s deterministic cs.1.1 cs.1.2 * inner cs.1.1 cs.1.2)]
  --     unfold programSmallStepSemantics
  --     simp only [↓reduceIte, and_self, iteOneZero_true, one_mul]

theorem step_concurrent_term (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| ↓ || ↓] inner s
    = inner [Prog| ↓] s := by sorry
  -- unfold step
  -- apply le_antisymm
  -- · apply sInf_le
  --   use deterministic
  --   simp only [enabledAction, or_false, ↓reduceIte, Set.mem_singleton_iff, true_and]
  --   exact tsum_sequential_term_of_deterministic s inner
  -- · apply le_sInf
  --   rintro _ ⟨a, h_a, rfl⟩
  --   simp only [enabledAction, Set.mem_singleton_iff] at h_a
  --   rw [h_a, tsum_sequential_term_of_deterministic s inner]
