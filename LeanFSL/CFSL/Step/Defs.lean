import LeanFSL.Program.Semantics
import LeanFSL.Program.Enabled
import LeanFSL.SL.Fuzzy
import LeanFSL.CFSL.Step.ReachState

namespace CFSL

open Syntax Semantics FSL

variable {Var : Type}

/-- One step in the probability transition function -- essentially the bellman-operator. -/
noncomputable def step (c : Program Var) (inner : Program Var → StateRV Var) : StateRV Var :=
    fun s => sInf { x | ∃ a ∈ enabledAction c s,
      ∑' cs : reachState Var, (programSmallStepSemantics c s a cs.prog cs.state) * inner cs.prog cs.state = x}

end CFSL
