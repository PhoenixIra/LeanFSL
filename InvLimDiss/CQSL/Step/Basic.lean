import InvLimDiss.CQSL.Step.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace CQSL


open Syntax Semantics QSL unitInterval

variable {Var : Type}

theorem monotone_step (c : Program Var) : Monotone (step c) := by
  intro X X' h_X
  rw [Pi.le_def]
  intro s
  apply le_sInf
  rintro _ ⟨a, h_a, rfl⟩
  have : ∑' cs : progState, (semantics c s a cs.1 cs.2) * X cs.1 cs.2 ∈
    { x | ∃ a ∈ enabledAction c s,
      ∑' cs : progState, (semantics c s a cs.1 cs.2) * X cs.1 cs.2 = x} := by {
        use a
      }
  apply sInf_le_of_le this
  · apply tsum_mono (isSummable _) (isSummable _)
    rw [Pi.le_def]
    intro cs
    cases eq_or_ne (semantics c s a cs.1 cs.2) 0 with
    | inl h_eq =>
      rw [h_eq, zero_mul, zero_mul]
    | inr h_ne =>
      rw [Subtype.mk_le_mk, Set.Icc.coe_mul, Set.Icc.coe_mul]
      rw[mul_le_mul_left]
      · rw [Pi.le_def] at h_X
        specialize h_X cs.1
        rw [Pi.le_def] at h_X
        exact h_X cs.2
      · apply lt_of_le_of_ne nonneg'
        apply Ne.symm
        exact h_ne

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
