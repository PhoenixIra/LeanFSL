import InvLimDiss.Program.Expressions
import Mathlib.Topology.UnitInterval
import Lean.PrettyPrinter

/-!
This file contains definitions and notation for program syntax.
We introduce the syntax [Prog| ... ] for nicer code.
-/

namespace Syntax

open unitInterval

variable (Vars : Type)

inductive Program where
  | terminated : Program
  | abort : Program
  | skip' : Program
  | assign : Vars → (ValueExp Vars) → Program
  | mutate : (ValueExp Vars) → (ValueExp Vars) → Program
  | lookup : Vars → (ValueExp Vars) → Program
  | compareAndSet :
    Vars → (ValueExp Vars) → (ValueExp Vars) → (ValueExp Vars) → Program
  | allocate : Vars → (ValueExp Vars) → Program
  | free' : (ValueExp Vars) → (ValueExp Vars) → Program
  | probabilisticBranching : (ProbExp Vars) → Program → Program → Program
  | conditionalBranching : (BoolExp Vars) → Program → Program → Program
  | loop : (BoolExp Vars) → Program → Program
  | sequential : Program → Program → Program
  | concurrent : Program → Program → Program

end Syntax

namespace ProgNotation

open Syntax Program

declare_syntax_cat program

syntax " skip " : program
syntax " ↓ " : program
syntax " ↯ " : program
syntax term " ≔ " term : program
syntax  term " *≔ " term : program
syntax term " ≔* " term : program
syntax term " ≔ " "cas" "(" term ", " term ", " term ")" : program
syntax term " ≔ " "alloc" "(" term ")" : program
syntax "free" "(" term ", " term ")": program
syntax program " ; " program : program
syntax " pif " term " then " program " else " program " fi " : program
syntax " if " term " then " program " else " program " fi ": program
syntax " while " term " begin " program " fi " : program
syntax program " || " program : program
syntax "(" program ")" : program
syntax "[[" term "]]" : program

syntax "[Prog| " program "]" : term

macro_rules
  | `(term| [Prog| ↓])      => `(Program.terminated)
  | `(term| [Prog| ↯])      => `(Program.abort)
  | `(term| [Prog| skip])   => `(Program.skip')
  | `(term| [Prog| $l:term ≔ $r:term]) => `(Program.assign $l $r)
  | `(term| [Prog| $l:term *≔ $r:term]) => `(Program.mutate $l $r)
  | `(term| [Prog| $l:term ≔* $r:term]) => `(Program.lookup $l $r)
  | `(term| [Prog| $l:term ≔ cas ( $a:term , $b:term , $c:term )]) => `(Program.compareAndSet $l $a $b $c)
  | `(term| [Prog| $l:term ≔ alloc ( $r:term )]) => `(Program.allocate $l $r)
  | `(term| [Prog| free ( $a:term , $b:term )]) => `(Program.free' $a $b)
  | `(term| [Prog| pif $p:term then $l else $r fi]) =>
      `(Program.probabilisticBranching $p [Prog| $l] [Prog| $r])
  | `(term| [Prog| if $b:term then $l:program else $r:program fi]) =>
      `(Program.conditionalBranching $b [Prog| $l] [Prog| $r])
  | `(term| [Prog| while $b:term begin $c fi]) => `(Program.loop $b [Prog| $c])
  | `(term| [Prog| $l ; $r]) => `(Program.sequential [Prog| $l] [Prog| $r])
  | `(term| [Prog| $l || $r]) => `(Program.concurrent [Prog| $l] [Prog| $r])
  | `(term| [Prog| ($a:program)]) => `([Prog| $a])
  | `(term| [Prog| [[$a:term]]]) => `($a)

open Lean PrettyPrinter Delaborator

@[app_unexpander Program.terminated]
def unexpandTerminated : Unexpander
  | `($_) => `([Prog| ↓])

@[app_unexpander Program.abort]
def unexpandError : Unexpander
  | `($_) => `([Prog| ↯])

@[app_unexpander Program.skip']
def unexpandSkip : Unexpander
  | `($_) => `([Prog| skip])

@[app_unexpander Program.assign]
def unexpandAssign : Unexpander
  | `($_ $l $r) => `([Prog| $l:term ≔ $r:term])
  | _ => throw ()

@[app_unexpander Program.mutate]
def unexpandMutate: Unexpander
  | `($_ $l $r) => `([Prog| $l:term *≔ $r:term])
  | _ => throw ()

@[app_unexpander Program.lookup]
def unexpandLookup : Unexpander
  | `($_ $l $r) => `([Prog| $l:term ≔* $r:term])
  | _ => throw ()

@[app_unexpander Program.compareAndSet]
def unexpandCAS : Unexpander
  | `($_ $l $a $b $c) => `([Prog| $l:term ≔ cas($a:term, $b:term, $c:term)])
  | _ => throw ()

@[app_unexpander Program.allocate]
def unexpandAlloc : Unexpander
  | `($_ $l $r) => `([Prog| $l:term ≔ alloc($r:term)])
  | _ => throw ()

@[app_unexpander Program.free']
def unexpandFree : Unexpander
  | `($_ $l $r) => `([Prog| free($l:term, $r:term)])
  | _ => throw ()

@[app_unexpander Program.probabilisticBranching]
def unexpandProbChoice : Unexpander
  | `($_ $p [Prog| $l] [Prog| $r]) => `([Prog| pif $p:term then $l else $r fi])
  | `($_ $p $l [Prog| $r]) => `([Prog| pif $p:term then [[$l]] else $r fi])
  | `($_ $p [Prog| $l] $r) => `([Prog| pif $p:term then $l else [[$r]] fi])
  | `($_ $p $l $r) => `([Prog| pif $p:term then [[$l]] else [[$r]] fi])
  | _ => throw ()

@[app_unexpander Program.conditionalBranching]
def unexpandConChoice : Unexpander
  | `($_ $p [Prog| $l] [Prog| $r]) => `([Prog| if $p:term then $l else $r fi])
  | `($_ $p $l [Prog| $r]) => `([Prog| if $p:term then [[$l]] else $r fi])
  | `($_ $p [Prog| $l] $r) => `([Prog| if $p:term then $l else [[$r]] fi])
  | `($_ $p $l $r) => `([Prog| if $p:term then [[$l]] else [[$r]] fi])
  | _ => throw ()

@[app_unexpander Program.loop]
def unexpandLoop : Unexpander
  | `($_ $b [Prog| $l]) => `([Prog| while $b:term begin $l fi])
  | `($_ $b $l) => `([Prog| while $b:term begin [[$l]] fi])
  | _ => throw ()

@[app_unexpander Program.sequential]
def unexpandSeq : Unexpander
  | `($_ [Prog| $l] [Prog| $r]) => `([Prog| $l ; $r])
  | `($_ $l [Prog| $r]) => `([Prog| [[$l]] ; $r])
  | `($_ [Prog| $l] $r) => `([Prog| $l ; [[$r]]])
  | `($_ $l $r) => `([Prog| [[$l]] ; [[$r]]])
  | _ => throw ()

@[app_unexpander Program.concurrent]
def unexpandConcur : Unexpander
  | `($_ [Prog| $l] [Prog| $r]) => `([Prog| $l || $r])
  | `($_ $l [Prog| $r]) => `([Prog| [[$l]] || $r])
  | `($_ [Prog| $l] $r) => `([Prog| $l || [[$r]]])
  | `($_ $l $r) => `([Prog| [[$l]] || [[$r]]])
  | _ => throw ()

example := [Prog| skip ; skip ; if λ _ => true then "x" ≔ λ _ => 5 else skip fi ; skip ]
example (e : ProbExp Variable) (c₁ c₂ : Program Variable) := [Prog| pif e then [[c₁]] else [[c₂]] fi]
example (c₁ c₂ : Program Variable) := [Prog| [[c₁]] || [[c₂]] ]

end ProgNotation
