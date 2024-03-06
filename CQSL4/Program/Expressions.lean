import CQSL4.Program.State
import Mathlib.Topology.UnitInterval

namespace Syntax

open State unitInterval

variable {Variable : Type}

def LocationExpression := (State Variable) → Option ℕ

def ValueExpression := (State Variable) → Option ℚ

def BooleanExpression := (State Variable) → Option Bool

def ProbabilisticExpression := (State Variable) → Option I

end Syntax
