import CQSL4.Program.State
import Mathlib.Topology.UnitInterval

namespace Syntax

open State unitInterval

variable (Variable : Type)

def ValueExp := (Stack Variable) → ℕ

def BoolExp := (Stack Variable) → Bool

def ProbExp := (Stack Variable) → I

end Syntax
