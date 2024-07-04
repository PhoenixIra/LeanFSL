import InvLimDiss.CQSL.Step.Basic
import InvLimDiss.Program.Support
import InvLimDiss.Analysis.Tsum

namespace CQSL

variable {Var : Type}

open Syntax Semantics QSL unitInterval Action State HeapValue

theorem tsum_probChoice_of_deterministic (s : State Var) (inner : Program Var → StateRV Var) :
    (∑' cs : progState,
    (semantics [Prog| pif e then [[c₁]] else [[c₂]] fi] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = (e s.stack) * inner c₁ s + σ (e s.stack) * inner c₂ s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_probChoice_support_superset s
  · cases eq_or_ne c₂ c₁ with
    | inl h_eq =>
      rw [h_eq, Set.pair_eq_singleton]
      rw [tsum_singleton (⟨c₁, s⟩ : progState)
        (fun cs : progState => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2)]
      unfold programSmallStepSemantics probabilisticChoiceSmallStepSemantics
      simp only [and_self, ↓reduceIte, one_mul, truncatedAdd_symm_eq]
    | inr h_ne =>
      have : (⟨c₁, s⟩ : progState) ≠ ⟨c₂, s⟩ := by simp [Prod.mk.inj_iff, Ne.symm h_ne]
      rw [tsum_pair (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) this]
      unfold programSmallStepSemantics probabilisticChoiceSmallStepSemantics
      simp only [and_self, ↓reduceIte, true_and, ite_mul, one_mul, and_true]
      rw [if_neg (by simp only [h_ne, and_false, not_false_eq_true])]
      rw [if_neg (by simp only [Ne.symm h_ne, and_true, not_false_eq_true])]
      rw [if_neg (Ne.symm h_ne)]

theorem step_probChoice (s : State Var) (inner : Program Var → StateRV Var) :
    step [Prog| pif e then [[c₁]] else [[c₂]] fi] inner s
    = (e s.stack) * inner c₁ s + σ (e s.stack) * inner c₂ s := by
  unfold step
  apply le_antisymm
  · apply sInf_le
    use deterministic
    simp only [enabledAction, Set.mem_singleton_iff, true_and]
    exact tsum_probChoice_of_deterministic s inner
  · apply le_sInf
    rintro _ ⟨a, h_a, rfl⟩
    simp only [enabledAction, Set.mem_singleton_iff] at h_a
    rw [h_a, tsum_probChoice_of_deterministic s inner]

theorem tsum_condChoice_left_of_deterministic (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = true) :
    (∑' cs : progState,
    (semantics [Prog| if e then [[c₁]] else [[c₂]] fi] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner c₁ s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_condChoice_left_support_superset s h
  · rw [tsum_singleton (⟨c₁, s⟩ : progState)
      (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) ]
    unfold programSmallStepSemantics conditionalChoiceSmallStepSemantics
    simp only [h, and_self, not_true_eq_false, false_and, or_false, iteOneZero_true, one_mul]

theorem step_condChoice_left (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = true):
    step [Prog| if e then [[c₁]] else [[c₂]] fi] inner s
    = inner c₁ s := by
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
    (∑' cs : progState,
    (semantics [Prog| if e then [[c₁]] else [[c₂]] fi] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner c₂ s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_condChoice_right_support_superset s h
  · rw [tsum_singleton (⟨c₂, s⟩ : progState)
      (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) ]
    unfold programSmallStepSemantics conditionalChoiceSmallStepSemantics
    simp only [h, Bool.false_eq_true, false_and, not_false_eq_true, and_self, or_true,
      iteOneZero_true, one_mul]

theorem step_condChoice_right (s : State Var) (inner : Program Var → StateRV Var)
    (h : (e s.stack) = false):
    step [Prog| if e then [[c₁]] else [[c₂]] fi] inner s
    = inner c₂ s := by
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
    (∑' cs : progState,
    (semantics [Prog| while e begin [[c]] fi] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| [[c]] ; while e begin [[c]] fi] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_loop_cont_support_superset s h
  · rw [tsum_singleton (⟨[Prog| [[c]] ; while e begin [[c]] fi], s⟩ : progState)
      (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) ]
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
    (∑' cs : progState,
    (semantics [Prog| while e begin [[c]] fi] s deterministic cs.1 cs.2) * inner cs.1 cs.2)
    = inner [Prog| ↓] s := by
  rw[← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_loop_term_support_superset s h
  · rw [tsum_singleton (⟨[Prog| ↓], s⟩ : progState)
      (fun cs => semantics _ s deterministic cs.1 cs.2 * inner cs.1 cs.2) ]
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
