import InvLimDiss.CFSL.Step.Defs
import InvLimDiss.Program.Support
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace CFSL


open Syntax Semantics FSL unitInterval

variable {Var : Type}

theorem step_mono (c : Program Var) : Monotone (step c) := by
  intro X X' h_X
  intro s
  apply le_sInf
  rintro _ ⟨a, h_a, rfl⟩
  have : ∑' cs : reachState Var, (semantics c s a cs.prog cs.state) * X cs.prog cs.state
    ∈ { x | ∃ a ∈ enabledAction c s,
      ∑' cs : reachState Var, (semantics c s a cs.prog cs.state) * X cs.prog cs.state = x} := by {
        use a
      }
  apply sInf_le_of_le this; clear this
  apply tsum_mono (isSummable _) (isSummable _)
  intro cs
  simp only [Set.coe_setOf, ne_eq, reachState.prog, Set.mem_setOf_eq, reachState.state]
  cases eq_or_ne (semantics c s a cs.prog cs.state) 0 with
  | inl h_eq =>
    rw [h_eq, zero_mul, zero_mul]
  | inr h_ne =>
    rw [Subtype.mk_le_mk, Set.Icc.coe_mul, Set.Icc.coe_mul]
    rw[mul_le_mul_left]
    · apply h_X
    · apply lt_of_le_of_ne nonneg'
      exact Ne.symm h_ne

theorem step_mono_of_state_of_semantics_support {c : Program Var} {s : State Var}
    {P Q : Program Var → StateRV Var}
    (h : ∀ a ∈ enabledAction c s, ∀ c' s',
      programSmallStepSemantics c s a c' s' ≠ 0 → P c' s' ≤ Q c' s') :
    step c P s ≤ step c Q s := by
  apply le_sInf
  rintro _ ⟨a, h_a, rfl⟩
  have : ∑' cs : reachState Var, (semantics c s a cs.prog cs.state) * P cs.prog cs.state
    ∈ { x | ∃ a ∈ enabledAction c s,
      ∑' cs : reachState Var, (semantics c s a cs.prog cs.state) * P cs.prog cs.state = x} := by {
        use a
      }
  apply sInf_le_of_le this
  rw [← tsum_subtype_eq_of_support_subset]
  pick_goal 2
  · apply mul_support_superset_left
    exact tsum_semantics_support_superset
  · nth_rw 2 [← tsum_subtype_eq_of_support_subset]
    pick_goal 2
    · apply mul_support_superset_left
      exact tsum_semantics_support_superset
    apply tsum_mono (isSummable _) (isSummable _)
    rintro ⟨⟨⟨c', s'⟩, h_abort⟩, h_semantics⟩
    simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, reachState.prog, reachState.state]
    simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq] at h_semantics
    refine mul_le_mul le_rfl ?_ (nonneg') (nonneg')
    exact h a h_a c' s' h_semantics

theorem step_mono_of_semantics_support {c : Program Var} {P Q : Program Var → StateRV Var}
    (h : ∀ s, ∀ a ∈ enabledAction c s, ∀ c' s',
      programSmallStepSemantics c s a c' s' ≠ 0 → P c' s' ≤ Q c' s') :
    step c P ≤ step c Q := by
  intro s
  exact step_mono_of_state_of_semantics_support (h s)

theorem step_terminated (inner : Program Var → StateRV Var) :
    step [Prog| ↓] inner s = 1 := by
  unfold step
  apply le_antisymm le_one'
  apply le_sInf
  rintro _ ⟨a, h_a, _⟩
  exfalso
  rw [enabledAction, Set.mem_empty_iff_false] at h_a
  exact h_a

theorem step_terminated' (inner : Program Var → StateRV Var) :
    step [Prog| ↓] inner = fun _ => 1 := by
  funext s
  exact step_terminated _

theorem step_error (inner : Program Var → StateRV Var) :
    step [Prog| ↯] inner s = 1 := by
  unfold step
  apply le_antisymm le_one'
  apply le_sInf
  rintro _ ⟨a, h_a, _⟩
  exfalso
  rw [enabledAction, Set.mem_empty_iff_false] at h_a
  exact h_a

theorem step_error' (inner : Program Var → StateRV Var) :
    step [Prog| ↯] inner = fun _ => 1 := by
  funext s
  exact step_error _

end CFSL
