import CQSL4.Program.Expressions
import Mathlib.Topology.UnitInterval

namespace Syntax

open unitInterval

variable (Variable : Type)

inductive Program where
  | skip : Program
  | val_assign : Variable → ValueExpression → Program
  | loc_assign : Variable → LocationExpression → Program
  | manipulate : LocationExpression → ValueExpression → Program
  | lookup : Variable → LocationExpression → Program
  | catch_and_set: LocationExpression → ValueExpression → ValueExpression → Program
  | allocate: Variable → ℕ → Program
  | free: LocationExpression → Program
  | sequential: Program → Program → Program
  | probabilistic_choice: ProbabilisticExpression → Program → Program → Program
  | conditional_choice: BooleanExpression → Program → Program → Program
  | loop: BooleanExpression → Program → Program

end Syntax
