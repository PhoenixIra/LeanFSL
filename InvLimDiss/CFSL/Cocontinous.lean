import InvLimDiss.CFSL.WeakExpectation
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder

namespace CFSL

open OmegaCompletePartialOrder FSL Syntax Semantics

theorem wrleStep_cocontinous (post : StateRV Var) (resource : StateRV Var) :
    Continuous (OrderHom.dual <| wrleStepHom post resource) := sorry

end CFSL
