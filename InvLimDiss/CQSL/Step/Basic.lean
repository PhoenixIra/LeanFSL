import InvLimDiss.CQSL.Step.Defs
import InvLimDiss.Program.Support
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace CQSL


open Syntax Semantics QSL unitInterval

variable {Var : Type}

theorem monotone_step (c : Program Var) : Monotone (step c) := by
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
    · rw [Pi.le_def] at h_X
      specialize h_X cs.prog
      rw [Pi.le_def] at h_X
      exact h_X cs.state
    · apply lt_of_le_of_ne nonneg'
      apply Ne.symm
      exact h_ne

theorem monotone_step_of_semantics_support {c : Program Var} {P Q : Program Var → StateRV Var}
    (h : ∀ s, ∀ a ∈ enabledAction c s, ∀ c' s',
      programSmallStepSemantics c s a c' s' ≠ 0 → P c' s' ≤ Q c' s') :
    step c P ≤ step c Q := by
  intro s
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
    exact h s a h_a c' s' h_semantics




theorem step_terminated (inner : Program Var → StateRV Var) :
    step [Prog| ↓] inner s = 1 := by
  unfold step
  apply le_antisymm le_one'
  apply le_sInf
  rintro _ ⟨a, h_a, _⟩
  exfalso
  rw [enabledAction, Set.mem_empty_iff_false] at h_a
  exact h_a

theorem step_error (inner : Program Var → StateRV Var) :
    step [Prog| ↯] inner s = 1 := by
  unfold step
  apply le_antisymm le_one'
  apply le_sInf
  rintro _ ⟨a, h_a, _⟩
  exfalso
  rw [enabledAction, Set.mem_empty_iff_false] at h_a
  exact h_a

end CQSL
