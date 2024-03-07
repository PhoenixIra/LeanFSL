import CQSL4.Program.State
import Mathlib.Topology.UnitInterval

namespace Syntax

open State unitInterval

variable (Variable : Type)

def ValueExp := (Stack Variable) → Option ℕ

def BoolExp := (Stack Variable) → Option Bool

def ProbExp := (Stack Variable) → Option I

end Syntax
