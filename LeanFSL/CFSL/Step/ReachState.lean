import LeanFSL.Program.Syntax
import LeanFSL.Program.State.Defs

variable (Var : Type)

open Syntax

/-- We introduce the abbreviation `reachState` for the tuple consisting of programs and states
that do not evaluate to abort.-/
abbrev reachState : Type := ↑{ ⟨c,_⟩ : (Program Var) × (State Var) | c ≠ [Prog| ↯]}

namespace reachState

  @[simp, reducible]
  def prog (cs : reachState Var) : Program Var := cs.1.1

  @[simp, reducible]
  def state (cs : reachState Var) : State Var := cs.1.2

end reachState
