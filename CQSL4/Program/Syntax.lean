import CQSL4.Program.Expressions
import Mathlib.Topology.UnitInterval

namespace Syntax

open unitInterval

variable (Vars : Type)

inductive Program where
  | skip : Program
  | terminated : Program
  | error : Program
  | valAssign : Vars → (ValueExp Vars) → Program
  | manipulate : (ValueExp Vars) → (ValueExp Vars) → Program
  | lookup : Vars → (ValueExp Vars) → Program
  | compareAndSet:
    Vars → (ValueExp Vars) → (ValueExp Vars) → (ValueExp Vars) → Program
  | allocate: Vars → ℕ → Program
  | free: (ValueExp Vars) → ℕ → Program
  | sequential: Program → Program → Program
  | probabilisticChoice:
    (ProbExp Vars) → Program → Program → Program
  | conditionalChoice: (BoolExp Vars) → Program → Program → Program
  | loop: (BoolExp Vars) → Program → Program
  | concurrent: Program → Program → Program

end Syntax
