import InvLimDiss.CFSL.WeakExpectation
import InvLimDiss.Mathlib.FixedPoints
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder

namespace CFSL

open OmegaCompletePartialOrder FSL Syntax Semantics

theorem wrleStep_cocontinous (post : StateRV Var) (resource : StateRV Var) :
    ωScottContinuous (OrderHom.dual <| wrleStepHom post resource) := by
  rw [dual_continuous_iff_co_continuous]
  intro chain h_chain
  apply le_antisymm
  · apply le_iInf
    intro n
    apply (wrleStepHom post resource).monotone
    exact iInf_le _ _
  · rw [iInf_le_iff]
    intro F h c
    induction c with
    | terminated => sorry
    | _ => sorry







end CFSL
