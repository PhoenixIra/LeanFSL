import InvLimDiss.CQSL.Step
import InvLimDiss.SL.Quantitative
import InvLimDiss.SL.QuantitativeProofrules
import Mathlib.Order.FixedPoints


namespace CQSL

open QSL Syntax OrderHom unitInterval

variable {Var : Type}

noncomputable def wrlp_step (post : StateRV Var) (resource : StateRV Var) :
    (Program Var → StateRV Var) → (Program Var → StateRV Var)
  | _, [Prog| ↓ ] => post
  | _, [Prog| ↯ ] => `[qsl| qFalse]
  | X, program => `[qsl| [[resource]] -⋆ [[step program (fun c => `[qsl| [[X c]] ⋆ [[resource]] ]) ]] ]

theorem wrlp_monotone (post : StateRV Var) (resource : StateRV Var) : Monotone (wrlp_step post resource) := by
  intro X X' h_X
  rw [Pi.le_def]
  intro c
  unfold wrlp_step
  split
  case h_1 => exact le_rfl
  case h_2 => exact le_rfl
  case h_3 =>
    apply monotone_qslSepImp le_rfl
    apply monotone_step
    rw [Pi.le_def]
    intro c
    rw [Pi.le_def]
    intro s
    rw [qslSepMul, qslSepMul]
    simp only [sSup_le_iff, Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro i heap₁ heap₂ h_disjoint h_union rfl
    have : X' c ⟨s.stack, heap₁⟩ * resource ⟨s.stack, heap₂⟩ ∈
      { x | ∃ heap₁ heap₂, State.disjoint heap₁ heap₂ ∧ heap₁ ∪ heap₂ = s.heap
        ∧ x = X' c ⟨s.stack, heap₁⟩ * resource ⟨s.stack, heap₂⟩} := by {
      use heap₁, heap₂
    }
    apply le_sSup_of_le this
    rw [Subtype.mk_le_mk, Set.Icc.coe_mul, Set.Icc.coe_mul]
    cases eq_or_ne (resource ⟨s.stack, heap₂⟩) 0 with
    | inl h_eq =>
      rw [h_eq, Set.Icc.coe_zero, mul_zero, mul_zero]
    | inr h_ne =>
      rw [mul_le_mul_right]
      · rw [Pi.le_def] at h_X
        specialize h_X c
        rw [Pi.le_def] at h_X
        exact h_X ⟨s.stack, heap₁⟩
      · apply lt_of_le_of_ne nonneg'
        exact Ne.symm h_ne

noncomputable def wrlp (program : Program Var) (post : StateRV Var) (resource : StateRV Var) :=
  gfp ⟨wrlp_step post resource, wrlp_monotone post resource⟩ program

theorem wrlp_unroll (program : Program Var) (post : StateRV Var) (resource : StateRV Var) :
    wrlp program post resource = match program with
  | [Prog| ↓ ] => post
  | [Prog| ↯ ] => `[qsl| qFalse]
  | program => `[qsl| [[resource]] -⋆ [[step program
    (fun c => `[qsl| [[wrlp c post resource]] ⋆ [[resource]] ]) ]] ] := by sorry

theorem wrlp_skip : P ⊢ wrlp [Prog| skip] P RI := by
  rw [wrlp_unroll]
  split
  case h_1 h_eq => cases h_eq
  case h_2 h_eq => cases h_eq
  case h_3 h_ne_abt h_ne_term =>
    sorry



end CQSL
