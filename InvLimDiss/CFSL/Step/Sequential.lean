import InvLimDiss.CFSL.Step.Basic
import InvLimDiss.Program.Support


namespace CFSL

variable {Var : Type}

open Syntax Semantics FSL unitInterval Action State HeapValue Classical Function

theorem tsum_sequential_term_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : reachState Var,
    (semantics [Prog| ↓ ; [[c]]] s deterministic cs.prog cs.state) * inner cs.prog cs.state)
    = if c = [Prog| ↯] then 0 else inner c s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_sequential_term_support_superset s
  · split
    case isTrue h_abort =>
      rw [dif_pos h_abort, tsum_empty]
    case isFalse h_ne_abort =>
      rw [dif_neg h_ne_abort]
      simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, reachState.prog, reachState.state]
      rw [tsum_singleton (⟨⟨c, s⟩, h_ne_abort⟩ : reachState Var)
        (fun cs => semantics _ s deterministic cs.1.1 cs.1.2 * inner cs.1.1 cs.1.2)]
      unfold programSmallStepSemantics
      simp only [↓reduceIte, and_self, iteOneZero_true, one_mul]

theorem step_sequential_term (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| ↓ ; [[c]]] inner s
    = if c = [Prog|↯] then 0 else inner c s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, or_false, ↓reduceIte, Set.mem_singleton_iff, true_and]
    exact tsum_sequential_term_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_sequential_term_of_deterministic s inner]

theorem tsum_sequential_abort_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : reachState Var,
    (semantics [Prog| ↯ ; [[c]]] s deterministic cs.prog cs.state) * inner cs.prog cs.state)
    = 0 := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_sequential_abort_support_superset s
  · simp only [Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state,
      tsum_empty]

theorem step_sequential_abort (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| ↯ ; [[c]]] inner s
    = 0 := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, or_true, ↓reduceIte, Set.mem_singleton_iff, Set.coe_setOf, ne_eq,
      reachState.prog, Set.mem_setOf_eq, reachState.state, true_and]
    exact tsum_sequential_abort_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, or_true, ↓reduceIte, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_sequential_abort_of_deterministic s inner]


private def inj (c₁ c₂ : Program Var) (s : State Var) (a : Action) (inner : Program Var → StateRV Var) :
  ↑(support (fun cs : reachState Var => semantics c₁ s a cs.prog cs.state
                      * inner ([Prog| [[cs.prog]] ; [[c₂]]]) cs.state))
  → @reachState Var :=
  fun cs => match cs with
  | ⟨⟨⟨c, s⟩,_⟩, _⟩ => ⟨⟨[Prog| [[c]] ; [[c₂]]], s⟩, by simp⟩

private theorem inj_injective (c₁ c₂ : Program Var) (s : State Var) (a : Action) (inner : Program Var → StateRV Var) :
    Injective (@inj Var c₁ c₂ s a inner) := by
  intro cs₁ cs₂ h
  unfold inj at h
  simp only [Subtype.mk_eq_mk, Prod.mk.injEq, Program.sequential.injEq, and_true] at h
  apply Subtype.ext_val; apply Subtype.ext_val
  exact Prod.ext_iff.mpr h


theorem tsum_sequential_cont (s : State Var) (inner : Program Var → StateRV Var)
    (h_term : c₁ ≠ [Prog| ↓]) (h_abort : c₁ ≠ [Prog| ↯]) :
    (∑' cs : reachState Var,
        (semantics [Prog| [[c₁]] ; [[c₂]]] s a cs.prog cs.state) * inner cs.prog cs.state)
    = (∑' cs : reachState Var,
        (semantics c₁ s a cs.prog cs.state) * inner [Prog| [[cs.prog]] ; [[c₂]]] cs.state) := by
    apply tsum_eq_tsum_of_ne_zero_bij (inj c₁ c₂ s a inner) (inj_injective c₁ c₂ s a inner)
    · apply subset_trans (tsum_sequential_cont_support_superset s inner h_term h_abort)
      rintro ⟨⟨c, s⟩,h⟩ ⟨c₁', _, ⟨rfl, rfl⟩, h_sem, h_inner⟩
      simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Set.range, reachState.prog,
        reachState.state, inj, Subtype.exists, support_mul, Set.mem_inter_iff, mem_support,
        Prod.exists, Subtype.mk.injEq, Prod.mk.injEq, Program.sequential.injEq, and_true,
        exists_and_left, exists_prop, exists_eq_right_right, exists_eq_left]
      unfold programSmallStepSemantics at h_sem
      simp only [↓reduceIte, if_neg h_term, if_neg h_abort, ne_eq, ite_eq_left_iff, Classical.not_imp] at h_sem
      obtain ⟨h_abort, h_sem⟩ := h_sem
      exact ⟨⟨h_sem, h_inner⟩, h_abort⟩
    · intro cs
      conv => left; unfold programSmallStepSemantics
      simp only [reachState.state, ne_eq, Set.mem_setOf_eq, inj, reachState.prog, ↓reduceIte,
        if_neg h_term, if_neg h_abort, ite_mul, zero_mul, Set.coe_setOf, ite_eq_right_iff, zero_eq_mul]
      obtain ⟨⟨⟨c,s⟩,h⟩,h'⟩ := cs
      intro h_abort
      exfalso
      simp only at h_abort
      simp only [ne_eq, Set.mem_setOf_eq] at h
      exact h h_abort


theorem step_sequential_cont (s : State Var) (inner : Program Var → StateRV Var)
    (h_term : c₁ ≠ [Prog| ↓]) (h_abort : c₁ ≠ [Prog| ↯]) :
    step [Prog| [[c₁]] ; [[c₂]]] inner s
    = step [Prog| [[c₁]]] (fun c => inner [Prog| [[c]] ; [[c₂]]]) s := by
  unfold step
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    apply sInf_le
    use a
    simp only [enabledAction]
    rw [if_neg (by simp only [h_term, h_abort, or_self, not_false_eq_true])]
    use h_a
    exact tsum_sequential_cont s inner h_term h_abort
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction] at h_a
    rw [if_neg (by simp only [h_term, h_abort, or_self, not_false_eq_true])] at h_a
    apply sInf_le
    use a, h_a
    simp only
    rw [tsum_sequential_cont s inner h_term h_abort]

end CFSL
