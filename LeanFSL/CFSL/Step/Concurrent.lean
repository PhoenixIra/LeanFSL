import LeanFSL.CFSL.Step.Basic
import LeanFSL.Program.Support


namespace CFSL

variable {Var : Type}

open Syntax Semantics FSL unitInterval Action State HeapValue Classical Function

theorem tsum_concurrent_term_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : reachState Var,
    (programSmallStepSemantics [Prog| ↓ || ↓] s deterministic cs.prog cs.state) * inner cs.prog cs.state)
    = inner [Prog| ↓] s := by
  rw [← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_concurrent_term_support_superset s
  · rw [tsum_singleton (⟨⟨[Prog| ↓], s⟩, by simp⟩ : reachState Var)
        (fun cs => programSmallStepSemantics _ s deterministic cs.1.1 cs.1.2 * inner cs.1.1 cs.1.2)]
    unfold programSmallStepSemantics
    simp only [and_self, ↓reduceIte, iteOneZero_true, one_mul]

theorem step_concurrent_term (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| ↓ || ↓] inner s
    = inner [Prog| ↓] s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, and_self, reduceCtorEq, or_self, or_false, ↓reduceIte,
      Set.mem_singleton_iff, Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq,
      reachState.state, true_and]
    exact tsum_concurrent_term_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_concurrent_term_of_deterministic s inner]

theorem tsum_concurrent_abort_left_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : reachState Var,
    (programSmallStepSemantics [Prog| ↯ || [[c]]] s deterministic cs.prog cs.state) * inner cs.prog cs.state)
    = 0 := by
  rw [← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_concurrent_abort_left_support_superset s
  · simp only [Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state,
      tsum_empty]

theorem step_concurrent_abort_left (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| ↯ || [[c]]] inner s = 0 := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, false_and, true_or, or_true, ↓reduceIte, Set.mem_singleton_iff,
      Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state, true_and]
    exact tsum_concurrent_abort_left_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, false_and, true_or, or_true, ↓reduceIte, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_concurrent_abort_left_of_deterministic s inner]

theorem tsum_concurrent_abort_right_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : reachState Var,
    (programSmallStepSemantics [Prog| [[c]] || ↯] s deterministic cs.prog cs.state) * inner cs.prog cs.state)
    = 0 := by
  rw [← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_concurrent_abort_right_support_superset s
  · simp only [Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state,
      tsum_empty]

theorem step_concurrent_abort_right (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| [[c]] || ↯] inner s = 0 := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, and_false, or_true, ↓reduceIte, Set.mem_singleton_iff, Set.coe_setOf,
      ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state, true_and]
    exact tsum_concurrent_abort_right_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, and_false, or_true, ↓reduceIte, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_concurrent_abort_right_of_deterministic s inner]

section cont_left

private def inj_left (c₁ c₂ : Program Var) (s : State Var) (a : Action) (inner : Program Var → StateRV Var) :
  ↑(support (fun cs : reachState Var => programSmallStepSemantics c₁ s a cs.prog cs.state
                      * inner ([Prog| [[cs.prog]] || [[c₂]]]) cs.state))
  → @reachState Var :=
  fun cs => match cs with
  | ⟨⟨⟨c, s⟩,_⟩, _⟩ => ⟨⟨[Prog| [[c]] || [[c₂]]], s⟩, by simp⟩

private theorem inj_left_injective (c₁ c₂ : Program Var) (s : State Var) (a : Action) (inner : Program Var → StateRV Var) :
    Injective (@inj_left Var c₁ c₂ s a inner) := by
  intro cs₁ cs₂ h
  unfold inj_left at h
  simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Subtype.mk.injEq, Prod.mk.injEq,
    Program.concurrent.injEq, and_true] at h
  apply Subtype.ext_val; apply Subtype.ext_val
  exact Prod.ext_iff.mpr h


theorem tsum_concurrent_cont_left (s : State Var) (inner : Program Var → StateRV Var)
    (h_term : c₁ ≠ [Prog| ↓]) (h_abort₁ : c₁ ≠ [Prog| ↯]) (h_abort₂ : c₂ ≠ [Prog| ↯]) :
    (∑' cs : reachState Var,
    (programSmallStepSemantics [Prog| [[c₁]] || [[c₂]]] s a.concurrentLeft cs.prog cs.state)
      * inner cs.prog cs.state)
    = (∑' cs : reachState Var,
    (programSmallStepSemantics c₁ s a cs.prog cs.state) * inner [Prog| [[cs.prog]] || [[c₂]]] cs.state) := by
  apply tsum_eq_tsum_of_ne_zero_bij (inj_left c₁ c₂ s a inner) (inj_left_injective c₁ c₂ s a inner)
  · apply subset_trans (tsum_concurrent_cont_left_support_superset s inner h_abort₁ h_abort₂)
    rintro ⟨⟨c, s⟩,h⟩ ⟨c₁', _, ⟨rfl, rfl⟩, h_sem, h_inner⟩
    simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Set.range, reachState.prog, reachState.state,
      inj_left, Subtype.exists, support_mul, Set.mem_inter_iff, mem_support, Prod.exists,
      Subtype.mk.injEq, Prod.mk.injEq, Program.concurrent.injEq, and_true, exists_and_left,
      exists_prop, exists_eq_right_right, exists_eq_left]
    unfold programSmallStepSemantics at h_sem
    simp only [reduceCtorEq, false_and, and_self, iteOneZero_false, and_false, ↓reduceIte, ne_eq,
      ite_eq_left_iff, not_and, not_or, and_imp, Classical.not_imp] at h_sem
    obtain ⟨_, _, _, h_abort, h_sem⟩ := h_sem
    exact ⟨⟨h_sem, h_inner⟩, h_abort⟩
  · intro cs
    conv => left; unfold programSmallStepSemantics
    simp only [reachState.prog, ne_eq, Set.mem_setOf_eq, reachState.state, false_and, and_false,
      iteOneZero_false, ite_mul, zero_mul, Set.coe_setOf]
    rw [if_neg (by simp only [h_term, false_and, not_false_eq_true])]
    rw [if_neg (by simp only [h_abort₁, h_abort₂, or_self, not_false_eq_true])]
    rw [inj_left, if_neg (by simp only [reduceCtorEq, not_false_eq_true])]
    simp only [↓reduceIte, ite_mul, zero_mul, ite_eq_right_iff, zero_eq_mul]
    obtain ⟨⟨⟨c,s⟩,h⟩,h'⟩ := cs
    intro h_abort
    exfalso
    simp only at h_abort
    simp only [ne_eq, Set.mem_setOf_eq] at h
    exact h h_abort

theorem step_concurrent_cont_only_left (s : State Var) (inner : Program Var → StateRV Var)
    (h_term : c₁ ≠ [Prog| ↓]) (h_abort : c₁ ≠ [Prog| ↯]) :
    step [Prog| [[c₁]] || ↓] inner s
    = step c₁ (fun c => inner [Prog| [[c]] || ↓]) s:= by
  unfold step
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    apply sInf_le
    use a.concurrentLeft
    have : ¬(c₁ = [Prog| ↓] ∨ c₁ = [Prog| ↯]) := by simp only [h_term, h_abort, or_self,
      not_false_eq_true]
    simp only [enabledAction, and_true, reduceCtorEq, or_false, ne_eq, not_true_eq_false,
      Set.mem_empty_iff_false, and_self, and_false, exists_false, Set.setOf_false, Set.union_empty,
      if_neg this, Set.mem_setOf_eq, concurrentLeft.injEq, exists_eq_left', h_a, Set.coe_setOf,
      reachState.prog, reachState.state]
    use h_term
    apply tsum_concurrent_cont_left s inner h_term h_abort
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    have : ¬(c₁ = [Prog| ↓] ∨ c₁ = [Prog| ↯]) := by simp only [h_term, h_abort, or_self,
      not_false_eq_true]
    simp only [enabledAction, and_true, reduceCtorEq, or_false, ne_eq, not_true_eq_false,
      Set.mem_empty_iff_false, and_self, and_false, exists_false, Set.setOf_false, Set.union_empty,
      if_neg this, Set.mem_setOf_eq] at h_a
    obtain ⟨a', rfl, h_term, h_a'⟩ := h_a
    apply sInf_le
    use a', h_a'
    simp only [Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state]
    exact (tsum_concurrent_cont_left s inner h_term h_abort
      (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])).symm

end cont_left

section cont_right

private def inj_right (c₁ c₂ : Program Var) (s : State Var) (a : Action) (inner : Program Var → StateRV Var) :
  ↑(support (fun cs : reachState Var => programSmallStepSemantics c₂ s a cs.prog cs.state
                      * inner ([Prog| [[c₁]] || [[cs.prog]]]) cs.state))
  → @reachState Var :=
  fun cs => match cs with
  | ⟨⟨⟨c, s⟩,_⟩, _⟩ => ⟨⟨[Prog| [[c₁]] || [[c]]], s⟩, by simp⟩

private theorem inj_right_injective (c₁ c₂ : Program Var) (s : State Var) (a : Action) (inner : Program Var → StateRV Var) :
    Injective (@inj_right Var c₁ c₂ s a inner) := by
  intro cs₁ cs₂ h
  unfold inj_right at h
  simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Subtype.mk.injEq, Prod.mk.injEq,
    Program.concurrent.injEq, true_and] at h
  apply Subtype.ext_val; apply Subtype.ext_val
  exact Prod.ext_iff.mpr h

theorem tsum_concurrent_cont_right (s : State Var) (inner : Program Var → StateRV Var)
    (h_term : c₂ ≠ [Prog| ↓]) (h_abort₁ : c₁ ≠ [Prog| ↯]) (h_abort₂ : c₂ ≠ [Prog| ↯]) :
    (∑' cs : reachState Var,
    (programSmallStepSemantics [Prog| [[c₁]] || [[c₂]]] s a.concurrentRight cs.prog cs.state)
      * inner cs.prog cs.state)
    = (∑' cs : reachState Var,
    (programSmallStepSemantics c₂ s a cs.prog cs.state) * inner [Prog| [[c₁]] || [[cs.prog]]] cs.state) := by
  apply tsum_eq_tsum_of_ne_zero_bij (inj_right c₁ c₂ s a inner) (inj_right_injective c₁ c₂ s a inner)
  · apply subset_trans (tsum_concurrent_cont_right_support_superset s inner h_abort₁ h_abort₂)
    rintro ⟨⟨c, s⟩,h⟩ ⟨c₂', _, ⟨rfl, rfl⟩, h_sem, h_inner⟩
    simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Set.range, reachState.prog, reachState.state,
      inj_right, Subtype.exists, support_mul, Set.mem_inter_iff, mem_support, Prod.exists,
      Subtype.mk.injEq, Prod.mk.injEq, Program.concurrent.injEq, true_and, exists_and_left,
      exists_prop, exists_eq_right_right, exists_eq_left]
    unfold programSmallStepSemantics at h_sem
    simp only [reduceCtorEq, false_and, and_self, iteOneZero_false, and_false, ↓reduceIte, ne_eq,
      ite_eq_left_iff, not_and, not_or, and_imp, Classical.not_imp] at h_sem
    obtain ⟨_, _, _, h_abort, h_sem⟩ := h_sem
    exact ⟨⟨h_sem, h_inner⟩, h_abort⟩
  · intro cs
    conv => left; unfold programSmallStepSemantics
    simp only [reachState.prog, ne_eq, Set.mem_setOf_eq, reachState.state, false_and, and_false,
      iteOneZero_false, ite_mul, zero_mul, Set.coe_setOf]
    rw [if_neg (by simp only [h_term, and_false, not_false_eq_true])]
    rw [if_neg (by simp only [h_abort₁, h_abort₂, or_self, not_false_eq_true])]
    rw [inj_right, if_neg (by simp only [reduceCtorEq, not_false_eq_true])]
    simp only [↓reduceIte, ite_mul, zero_mul, ite_eq_right_iff, zero_eq_mul]
    obtain ⟨⟨⟨c,s⟩,h⟩,h'⟩ := cs
    intro h_abort
    exfalso
    simp only at h_abort
    simp only [ne_eq, Set.mem_setOf_eq] at h
    exact h h_abort

theorem step_concurrent_cont_only_right (s : State Var) (inner : Program Var → StateRV Var)
    (h_term : c₂ ≠ [Prog| ↓]) (h_abort : c₂ ≠ [Prog| ↯]) :
    step [Prog| ↓ || [[c₂]]] inner s
    = step c₂ (fun c => inner [Prog| ↓ || [[c]]]) s:= by
  unfold step
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    apply sInf_le
    use a.concurrentRight
    have : ¬(c₂ = [Prog| ↓] ∨ c₂ = [Prog| ↯]) := by simp only [h_term, h_abort, or_self,
      not_false_eq_true]
    simp only [enabledAction, true_and, reduceCtorEq, false_or, ne_eq, not_true_eq_false,
      Set.mem_empty_iff_false, and_self, and_false, exists_false, Set.setOf_false, Set.empty_union,
      if_neg this, Set.mem_setOf_eq, concurrentRight.injEq, exists_eq_left', h_a, and_true,
      Set.coe_setOf, reachState.prog, reachState.state]
    use h_term
    refine tsum_concurrent_cont_right s inner h_term ?_ h_abort
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    have : ¬(c₂ = [Prog| ↓] ∨ c₂ = [Prog| ↯]) := by simp only [h_term, h_abort, or_self,
      not_false_eq_true]
    simp only [enabledAction, true_and, reduceCtorEq, false_or, ne_eq, not_true_eq_false,
      Set.mem_empty_iff_false, and_self, and_false, exists_false, Set.setOf_false, Set.empty_union,
      if_neg this, Set.mem_setOf_eq] at h_a
    obtain ⟨a', rfl, h_term, h_a'⟩ := h_a
    apply sInf_le
    use a', h_a'
    simp only [Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state]
    exact (tsum_concurrent_cont_right s inner h_term
      (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) h_abort).symm

end cont_right

theorem step_concurrent_cont (s : State Var) (inner : Program Var → StateRV Var)
    (h_term₁ : c₁ ≠ [Prog| ↓]) (h_term₂ : c₂ ≠ [Prog| ↓])
    (h_abort₁ : c₁ ≠ [Prog| ↯]) (h_abort₂ : c₂ ≠ [Prog| ↯]) :
    step [Prog| [[c₁]] || [[c₂]]] inner s
    = min (step c₁ (fun c => inner [Prog| [[c]] || [[c₂]]]) s)
          (step c₂ (fun c => inner [Prog| [[c₁]] || [[c]]]) s) := by
  unfold step
  apply le_antisymm
  · apply le_min
    · apply le_sInf
      rintro _ ⟨a, h_a, rfl⟩
      apply sInf_le
      use a.concurrentLeft
      apply And.intro
      · simp only [enabledAction, h_term₁, h_term₂, and_self, h_abort₁, h_abort₂, or_self,
        ↓reduceIte, ne_eq, not_false_eq_true, true_and, Set.mem_union, Set.mem_setOf_eq,
        concurrentLeft.injEq, exists_eq_left', reduceCtorEq, false_and, exists_false, or_false]
        exact h_a
      · exact tsum_concurrent_cont_left s _ h_term₁ h_abort₁ h_abort₂
    · apply le_sInf
      rintro _ ⟨a, h_a, rfl⟩
      apply sInf_le
      use a.concurrentRight
      apply And.intro
      · simp only [enabledAction, h_term₁, h_term₂, and_self, h_abort₁, h_abort₂, or_self,
        ↓reduceIte, ne_eq, not_false_eq_true, true_and, Set.mem_union, Set.mem_setOf_eq,
        reduceCtorEq, false_and, exists_false, concurrentRight.injEq, exists_eq_left', false_or]
        exact h_a
      · exact tsum_concurrent_cont_right s _ h_term₂ h_abort₁ h_abort₂
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, h_term₁, h_term₂, and_self, h_abort₁, h_abort₂, or_self, ↓reduceIte,
      Set.mem_union, Set.mem_setOf_eq] at h_a
    cases h_a with
    | inl h_a_left =>
      obtain ⟨a', h_eq, _, h_a'⟩ := h_a_left
      rw [h_eq]
      apply le_trans (min_le_left _ _)
      apply sInf_le
      use a', h_a'
      exact (tsum_concurrent_cont_left s _ h_term₁ h_abort₁ h_abort₂).symm
    | inr h_a_right =>
      obtain ⟨a', h_eq, _, h_a'⟩ := h_a_right
      rw [h_eq]
      apply le_trans (min_le_right _ _)
      apply sInf_le
      use a', h_a'
      exact (tsum_concurrent_cont_right s _ h_term₂ h_abort₁ h_abort₂).symm




end CFSL
