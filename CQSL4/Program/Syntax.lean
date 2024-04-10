import CQSL4.Program.Expressions
import Mathlib.Topology.UnitInterval
import Lean.PrettyPrinter.Delaborator

namespace Syntax

open unitInterval

variable (Vars : Type)

inductive Program where
  | skip' : Program
  | terminated : Program
  | error : Program
  | assign : Vars → (ValueExp Vars) → Program
  | manipulate : (ValueExp Vars) → (ValueExp Vars) → Program
  | lookup : Vars → (ValueExp Vars) → Program
  | compareAndSet :
    Vars → (ValueExp Vars) → (ValueExp Vars) → (ValueExp Vars) → Program
  | allocate: Vars → ℕ → Program
  | free' : (ValueExp Vars) → ℕ → Program
  | sequential : Program → Program → Program
  | probabilisticChoice :
    (ProbExp Vars) → Program → Program → Program
  | conditionalChoice : (BoolExp Vars) → Program → Program → Program
  | loop : (BoolExp Vars) → Program → Program
  | concurrent : Program → Program → Program

end Syntax

namespace Notation

open Syntax Program

declare_syntax_cat program

syntax " skip " : program
syntax " ↓ " : program
syntax " ↯ " : program
syntax term " ≔ " term : program
syntax  term " *≔ " term : program
syntax term " ≔* " term : program
syntax term " ≔ " "cas" "(" term " , " term " , " term ")" : program
syntax term " ≔ alloc " term : program
syntax "free" "(" term " , " term ")": program
syntax program ";" program : program
syntax program " [ " term " ] " program : program
syntax " if " term " then " program " else " program : program
syntax " while " term " begin " program " end " : program
syntax program "||" program : program
syntax "(" program ")" : program

syntax "`[Program| " program "]" : term

macro_rules
  | `(`[Program| skip])   => `(Program.skip')
  | `(`[Program| ↓])      => `(Program.terminated)
  | `(`[Program| ↯])      => `(Program.error)
  | `(`[Program| $l:term ≔ $r:term]) => `(Program.assign $l $r)
  | `(`[Program| $l:term *≔ $r:term]) => `(Program.manipulate $l $r)
  | `(`[Program| $l:term ≔* $r:term]) => `(Program.lookup $l $r)
  | `(`[Program| $l:term ≔ cas ( $a:term , $b:term , $c:term )]) => `(Program.compareAndSet $l $a $b $c)
  | `(`[Program| $l:term ≔ alloc $r:term]) => `(Program.allocate $l $r)
  | `(`[Program| free ( $a:term , $b:term )]) => `(Program.free' $a $b)
  | `(`[Program| $l ; $r]) => `(Program.sequential `[Program| $l] `[Program| $r])
  | `(`[Program| $l [$p:term] $r]) => `(Program.probabilisticChoice $p `[Program| $l] `[Program| $r])
  | `(`[Program| if $b:term then $l:program else $r:program]) =>
    `(Program.conditionalChoice $b `[Program| $l] `[Program| $r])
  | `(`[Program| while $b:term begin $c end]) => `(Program.loop $b `[Program| $c])
  | `(`[Program| $l || $r]) => `(Program.concurrent `[Program| $l] `[Program| $r])
  | `(`[Program| ($a:program)]) => `(`[Program| $a])



end Notation
