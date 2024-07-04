import InvLimDiss.CQSL.Step.Basic
import InvLimDiss.Program.Support


namespace CQSL

variable {Var : Type}

open Syntax Semantics QSL unitInterval Action State HeapValue Classical Function

theorem tsum_sequential_term_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : progState,
    (semantics [Prog| ↓ ; [[c]]] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner c s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_sequential_term_support_superset s
  · rw [tsum_singleton (⟨c, s⟩ : progState)
      (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) ]
    unfold programSmallStepSemantics
    simp only [↓reduceIte, and_self, iteOneZero_true, one_mul]

theorem step_sequential_term (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| ↓ ; [[c]]] inner s
    = inner c s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, ↓reduceIte, Set.mem_singleton_iff, true_and]
    exact tsum_sequential_term_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_sequential_term_of_deterministic s inner]

private def inj (c₁ c₂ : Program Var) (s : State Var) (a : Action) (inner : Program Var → StateRV Var) :
  ↑(support (fun cs : progState => semantics c₁ s a cs.1 cs.2 *
    if cs.1 = [Prog| ↯ ] then inner [Prog| ↯ ] cs.2 else inner ([Prog| [[cs.1]] ; [[c₂]]]) cs.2))
  → @progState Var :=
  fun cs => match cs with
  | ⟨⟨[Prog| ↯], s⟩, _⟩ => ⟨[Prog| ↯], s⟩
  | ⟨⟨c, s⟩, _⟩ => ⟨[Prog| [[c]] ; [[c₂]]], s⟩

private theorem inj_injective (c₁ c₂ : Program Var) (s : State Var) (a : Action) (inner : Program Var → StateRV Var) :
    Injective (@inj Var c₁ c₂ s a inner) := by
  intro cs₁ cs₂ h
  unfold inj at h
  split at h
  case h_1 =>
    split at h
    case h_1 =>
      rw [Subtype.mk_eq_mk]
      simp only [Prod.mk.injEq, true_and] at h
      rw [h]
    case h_2 h_ne => simp only [Prod.mk.injEq, false_and] at h
  case h_2 =>
    split at h
    case h_1 => simp only [Prod.mk.injEq, false_and] at h
    case h_2 =>
      rw [Subtype.mk_eq_mk]
      simp only [Prod.mk.injEq, Program.sequential.injEq, and_true] at h
      rw[h.left, h.right]


theorem tsum_sequential_cont (s : State Var) (inner : Program Var → StateRV Var)
    (h : c₁ ≠ [Prog| ↓]) (h_abort : inner [Prog| ↯] = `[qsl| qFalse]) :
    (∑' cs : progState, (semantics [Prog| [[c₁]] ; [[c₂]]] s a cs.1 cs.2) * inner cs.1 cs.2)
    = (∑' cs : progState, (semantics c₁ s a cs.1 cs.2) *
      if cs.1 = [Prog| ↯] then inner [Prog| ↯] cs.2 else inner [Prog| [[cs.1]] ; [[c₂]]] cs.2) := by
    apply tsum_eq_tsum_of_ne_zero_bij (inj c₁ c₂ s a inner) (inj_injective c₁ c₂ s a inner)
    · sorry
    · sorry

theorem step_sequential_cont (s : State Var) (inner : Program Var → StateRV Var)
    (h : c₁ ≠ [Prog| ↓]) (h_abort : inner [Prog| ↯] = `[qsl| qFalse]) :
    step [Prog| [[c₁]] ; [[c₂]]] inner s
    = step [Prog| [[c₁]]] (fun c => if c = [Prog| ↯] then inner [Prog| ↯] else inner [Prog| [[c]] ; [[c₂]]]) s := by
  unfold step
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    apply sInf_le
    use a
    simp only [enabledAction, if_neg h]
    use h_a
    conv => right; right; intro cs; rw [ite_apply]
    exact tsum_sequential_cont s inner h h_abort
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff, if_neg h] at h_a
    apply sInf_le
    use a, h_a
    simp only
    rw [tsum_sequential_cont s inner h h_abort]
    conv => left; right; intro cs; rw [ite_apply]

end CQSL
