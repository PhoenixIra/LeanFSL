import InvLimDiss.Program.Semantics
import InvLimDiss.Program.Enabled
import InvLimDiss.SL.Quantitative

namespace CQSL

open Syntax Semantics QSL

variable {Var : Type}

/-- We introduce the abbreviation `progState` for the tuple consisting of programs and states.-/
abbrev progState := (Program Var) × (State Var)

/-- We introduce the abbreviation `semantics` for the probability transition function. -/
noncomputable abbrev semantics := @programSmallStepSemantics Var

/-- One step in the probability transition function -- essentially the bellman-operator. -/
noncomputable def step (c : Program Var) (inner : Program Var → StateRV Var) : StateRV Var :=
    fun s => sInf { x | ∃ a ∈ enabledAction c s,
      ∑' cs : progState, (semantics c s a cs.1 cs.2) * inner cs.1 cs.2 = x}

end CQSL
