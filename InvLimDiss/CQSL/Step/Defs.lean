import InvLimDiss.Program.Semantics
import InvLimDiss.Program.Enabled
import InvLimDiss.SL.Quantitative
import InvLimDiss.CQSL.Step.ReachState

namespace CQSL

open Syntax Semantics QSL

variable {Var : Type}

/-- We introduce the abbreviation `semantics` for the probability transition function. -/
noncomputable abbrev semantics := @programSmallStepSemantics Var

/-- One step in the probability transition function -- essentially the bellman-operator. -/
noncomputable def step (c : Program Var) (inner : Program Var → StateRV Var) : StateRV Var :=
    fun s => sInf { x | ∃ a ∈ enabledAction c s,
      ∑' cs : reachState Var, (semantics c s a cs.prog cs.state) * inner cs.prog cs.state = x}

end CQSL
