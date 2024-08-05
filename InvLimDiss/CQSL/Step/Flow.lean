import InvLimDiss.CQSL.Step.Basic
import InvLimDiss.Program.Support
import InvLimDiss.Mathlib.Tsum

namespace CQSL

variable {Var : Type}

open Syntax Semantics QSL unitInterval Action State HeapValue Classical

theorem tsum_probChoice_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : reachState Var,
      (semantics [Prog| pif e then [[c₁]] else [[c₂]] fi] s deterministic cs.prog cs.state)
      * inner cs.prog cs.state)
    = (if c₁ = [Prog|↯] then 0 else (e s.stack) * inner c₁ s)
      + (if c₂ = [Prog|↯] then 0 else σ (e s.stack) * inner c₂ s) := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_probChoice_support_superset s
  · cases eq_or_ne c₂ c₁ with
    | inl h_eq =>
      rw [h_eq]
      cases eq_or_ne c₁ [Prog|↯] with
      | inl h_c₁ =>
        rw [dif_pos h_c₁, if_pos h_c₁, if_pos h_c₁]
        simp only [Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state,
          Set.union_self, isEmpty_subtype, Set.mem_empty_iff_false, not_false_eq_true, implies_true,
          tsum_empty, add_zero]
      | inr h_c₁ =>
        rw [dif_neg h_c₁, if_neg h_c₁, if_neg h_c₁, Set.union_self]
        rw [tsum_singleton (⟨⟨c₁, s⟩, h_c₁⟩ : reachState Var)
          (fun cs : reachState Var => semantics _ s deterministic cs.prog cs.state * inner cs.prog cs.state)]
        unfold programSmallStepSemantics probabilisticBranchingSmallStepSemantics
        simp only [reachState.state, and_self, ↓reduceIte, reachState.prog, one_mul]
        rw [truncatedAdd_symm_eq]
    | inr h_ne =>
      cases eq_or_ne c₁ [Prog|↯] with
      | inl h_c₁ =>
        rw [dif_pos h_c₁, if_pos h_c₁]
        have h_c₂ : c₂ ≠ [Prog| ↯] := by rw [← h_c₁]; exact h_ne
        rw [dif_neg h_c₂, if_neg h_c₂, Set.empty_union]
        simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, reachState.prog, reachState.state,
          zero_add]
        rw [tsum_singleton (⟨⟨c₂, s⟩, h_c₂⟩ : reachState Var)
          (fun cs : reachState Var => semantics _ s deterministic cs.1.1 cs.1.2 * inner cs.1.1 cs.1.2)]
        unfold programSmallStepSemantics probabilisticBranchingSmallStepSemantics
        simp only [and_self, ↓reduceIte, and_true, ite_mul, one_mul, if_neg (Ne.symm h_ne)]
      | inr h_c₁ =>
        rw [dif_neg h_c₁, if_neg h_c₁]
        cases eq_or_ne c₂ [Prog|↯] with
        | inl h_c₂ =>
          rw [dif_pos h_c₂, if_pos h_c₂, Set.union_empty]
          simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, reachState.prog, reachState.state,
            add_zero]
          rw [tsum_singleton (⟨⟨c₁, s⟩, h_c₁⟩ : reachState Var)
            (fun cs : reachState Var => semantics _ s deterministic cs.1.1 cs.1.2 * inner cs.1.1 cs.1.2)]
          unfold programSmallStepSemantics probabilisticBranchingSmallStepSemantics
          simp only [and_self, ↓reduceIte, true_and, ite_mul, one_mul, ite_eq_right_iff]
          intro h_eq
          exfalso
          exact h_ne h_eq
        | inr h_c₂ =>
          rw [dif_neg h_c₂, if_neg h_c₂, Set.union_singleton]
          simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, reachState.prog, reachState.state]
          have : (⟨⟨c₁, s⟩,h_c₁⟩ : reachState Var) ≠ ⟨⟨c₂, s⟩, h_c₂⟩ := by simp [Prod.mk.inj_iff, Ne.symm h_ne]
          rw [tsum_pair (fun cs => semantics _ s deterministic cs.1.1 cs.1.2 * inner cs.1.1 cs.1.2) this.symm]
          unfold programSmallStepSemantics probabilisticBranchingSmallStepSemantics
          simp only [and_self, ↓reduceIte, and_true, ite_mul, one_mul, true_and]
          rw [if_neg h_ne, if_neg h_ne.symm, if_neg h_ne.symm]
          rw [add_comm]

theorem step_probChoice (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| pif e then [[c₁]] else [[c₂]] fi] inner s
    = (if c₁ = [Prog|↯] then 0 else (e s.stack) * inner c₁ s)
      + (if c₂ = [Prog|↯] then 0 else σ (e s.stack) * inner c₂ s) := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, reachState.prog, ne_eq, Set.mem_setOf_eq,
      reachState.state, true_and]
    exact tsum_probChoice_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_probChoice_of_deterministic s inner]

theorem tsum_condChoice_left_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = true) :
    (∑' cs : reachState Var,
      (semantics [Prog| if e then [[c₁]] else [[c₂]] fi] s deterministic cs.prog cs.state)
      * inner cs.prog cs.state)
    = if c₁ = [Prog|↯] then 0 else inner c₁ s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_condChoice_left_support_superset s h
  · cases eq_or_ne c₁ [Prog|↯] with
    | inl h_c₁ =>
      rw [dif_pos h_c₁, if_pos h_c₁]
      simp only [Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state,
        tsum_empty]
    | inr h_c₁ =>
      rw [dif_neg h_c₁, if_neg h_c₁]
      rw [tsum_singleton (⟨⟨c₁, s⟩, h_c₁⟩ : reachState Var)
        (fun cs => semantics _ s deterministic cs.1.1 cs.1.2 * inner cs.1.1 cs.1.2) ]
      unfold programSmallStepSemantics conditionalBranchingSmallStepSemantics
      simp only [h, and_self, not_true_eq_false, false_and, or_false, iteOneZero_true, one_mul]

theorem step_condChoice_left (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = true):
    step [Prog| if e then [[c₁]] else [[c₂]] fi] inner s
    = if c₁ = [Prog|↯] then 0 else inner c₁ s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_condChoice_left_of_deterministic s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_condChoice_left_of_deterministic s inner h]

theorem tsum_condChoice_right_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = false) :
    (∑' cs : reachState Var,
      (semantics [Prog| if e then [[c₁]] else [[c₂]] fi] s deterministic cs.prog cs.state)
      * inner cs.prog cs.state)
    = if c₂ = [Prog|↯] then 0 else inner c₂ s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_condChoice_right_support_superset s h
  · cases eq_or_ne c₂ [Prog|↯] with
    | inl h_c₂ =>
      rw [dif_pos h_c₂, if_pos h_c₂]
      simp only [Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state,
        tsum_empty]
    | inr h_c₂ =>
      rw [dif_neg h_c₂, if_neg h_c₂]
      rw [tsum_singleton (⟨⟨c₂, s⟩, h_c₂⟩ : reachState Var)
        (fun cs => semantics _ s deterministic cs.1.1 cs.1.2 * inner cs.1.1 cs.1.2) ]
      unfold programSmallStepSemantics conditionalBranchingSmallStepSemantics
      simp only [h, Bool.false_eq_true, false_and, not_false_eq_true, and_self, or_true,
        iteOneZero_true, one_mul]

theorem step_condChoice_right (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = false):
    step [Prog| if e then [[c₁]] else [[c₂]] fi] inner s
    = if c₂ = [Prog|↯] then 0 else inner c₂ s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_condChoice_right_of_deterministic s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_condChoice_right_of_deterministic s inner h]

theorem tsum_loop_cont_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = true) :
    (∑' cs : reachState Var,
      (semantics [Prog| while e begin [[c]] fi] s deterministic cs.prog cs.state)
      * inner cs.prog cs.state)
    = inner [Prog| [[c]] ; while e begin [[c]] fi] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_loop_cont_support_superset s h
  · rw [tsum_singleton (⟨⟨[Prog| [[c]] ; while e begin [[c]] fi], s⟩, by simp⟩ : reachState Var)
      (fun cs => semantics _ s deterministic cs.1.1 cs.1.2 * inner cs.1.1 cs.1.2) ]
    unfold programSmallStepSemantics loopSmallStepSemantics
    simp only [h, and_self, iteOneZero_true, one_mul]

theorem step_loop_cont (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = true):
    step [Prog| while e begin [[c]] fi] inner s
    = inner [Prog| [[c]] ; while e begin [[c]] fi] s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_loop_cont_of_deterministic s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_loop_cont_of_deterministic s inner h]

theorem tsum_loop_term_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = false) :
    (∑' cs : reachState Var,
    (semantics [Prog| while e begin [[c]] fi] s deterministic cs.1.1 cs.1.2) * inner cs.1.1 cs.1.2)
    = inner [Prog| ↓] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_loop_term_support_superset s h
  · rw [tsum_singleton (⟨⟨[Prog| ↓], s⟩, by simp⟩ : reachState Var)
      (fun cs => semantics _ s deterministic cs.1.1 cs.1.2 * inner cs.1.1 cs.1.2) ]
    unfold programSmallStepSemantics loopSmallStepSemantics
    simp only [h, Bool.false_eq_true, not_false_eq_true, and_self, iteOneZero_true, one_mul]

theorem step_loop_term (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = false):
    step [Prog| while e begin [[c]] fi] inner s
    = inner [Prog| ↓] s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_loop_term_of_deterministic s inner h
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_loop_term_of_deterministic s inner h]

end CQSL
