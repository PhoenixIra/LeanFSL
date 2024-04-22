import CQSL4.Program.Expressions
import Mathlib.Topology.UnitInterval
import Lean.PrettyPrinter.Delaborator

namespace Syntax

open unitInterval

variable (Vars : Type)

inductive Program where
  | terminated : Program
  | error : Program
  | skip' : Program
  | assign : Vars → (ValueExp Vars) → Program
  | manipulate : (ValueExp Vars) → (ValueExp Vars) → Program
  | lookup : Vars → (ValueExp Vars) → Program
  | compareAndSet :
    Vars → (ValueExp Vars) → (ValueExp Vars) → (ValueExp Vars) → Program
  | allocate: Vars → ℕ → Program
  | free' : (ValueExp Vars) → ℕ → Program
  | probabilisticChoice : (ProbExp Vars) → Program → Program → Program
  | conditionalChoice : (BoolExp Vars) → Program → Program → Program
  | loop : (BoolExp Vars) → Program → Program
  | sequential : Program → Program → Program
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
syntax " pif " term " then " program " else " program " end " : program
syntax " if " term " then " program " else " program " end ": program
syntax " while " term " begin " program " end " : program
syntax program "||" program : program
syntax "(" program ")" : program
syntax "[[" term "]]" : program

syntax "`[Prog| " program "]" : term

macro_rules
  | `(`[Prog| ↓])      => `(Program.terminated)
  | `(`[Prog| ↯])      => `(Program.error)
  | `(`[Prog| skip])   => `(Program.skip')
  | `(`[Prog| $l:term ≔ $r:term]) => `(Program.assign $l $r)
  | `(`[Prog| $l:term *≔ $r:term]) => `(Program.manipulate $l $r)
  | `(`[Prog| $l:term ≔* $r:term]) => `(Program.lookup $l $r)
  | `(`[Prog| $l:term ≔ cas ( $a:term , $b:term , $c:term )]) => `(Program.compareAndSet $l $a $b $c)
  | `(`[Prog| $l:term ≔ alloc $r:term]) => `(Program.allocate $l $r)
  | `(`[Prog| free ( $a:term , $b:term )]) => `(Program.free' $a $b)
  | `(`[Prog| pif $p:term then $l else $r end]) => `(Program.probabilisticChoice $p `[Prog| $l] `[Prog| $r])
  | `(`[Prog| if $b:term then $l:program else $r:program end]) =>
    `(Program.conditionalChoice $b `[Prog| $l] `[Prog| $r])
  | `(`[Prog| while $b:term begin $c end]) => `(Program.loop $b `[Prog| $c])
  | `(`[Prog| $l ; $r]) => `(Program.sequential `[Prog| $l] `[Prog| $r])
  | `(`[Prog| $l || $r]) => `(Program.concurrent `[Prog| $l] `[Prog| $r])
  | `(`[Prog| ($a:program)]) => `(`[Prog| $a])
  | `(`[Prog| [[$a:term]]]) => `($a)

example := `[Prog| skip ; skip ; if λ _ => true then "x" ≔ λ _ => 5 else skip end ; skip ]
example (e : ProbExp Variable) (c₁ c₂ : Program Variable) := `[Prog| pif e then [[c₁]] else [[c₂]] end]
example (c₁ c₂ : Program Variable) := `[Prog| [[c₁]] || [[c₂]] ]

end Notation
