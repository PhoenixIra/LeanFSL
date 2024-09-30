import InvLimDiss.CFSL.WeakExpectation
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder

namespace CFSL

open OmegaCompletePartialOrder FSL Syntax Semantics

theorem wrle_step_cocontinous (post : StateRV Var) (resource : StateRV Var) :
    Continuous (OrderHom.dual <| wrle_step_hom post resource) := sorry

end CFSL
