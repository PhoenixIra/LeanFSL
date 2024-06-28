import InvLimDiss.CQSL.Step
import InvLimDiss.SL.Quantitative
import InvLimDiss.SL.QuantitativeProofrules
import Mathlib.Order.FixedPoints


namespace CQSL

open QSL Syntax OrderHom

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

noncomputable def wrlp (program : Program Var) (post : StateRV Var) (resource : StateRV Var) := gfp wrlp_step



end CQSL
