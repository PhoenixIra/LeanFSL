import InvLimDiss.Program.State
import InvLimDiss.Program.Expressions
import InvLimDiss.SL.Entailment
import Lean.PrettyPrinter

/-!
This file contains definitions and syntax about classical (i.e. Prop) separation logic.
-/

namespace SL

open State Syntax BigOperators


def StateProp (Var : Type) : Type := State Var → Prop

noncomputable instance : CompleteLattice (StateProp Var) := Pi.instCompleteLattice

instance : Entailment (StateProp Var) := ⟨fun P Q => P ≤ Q⟩

variable {Var : Type}

def slTrue : StateProp Var := λ _ => true

def slFalse : StateProp Var := λ _ => false

def slEmp : StateProp Var := λ ⟨_,h⟩ => h = ∅

def slPointsTo (loc val : ValueExp Var) : StateProp Var :=
    λ ⟨s,h⟩ => ∃ l : ℕ+, l = (loc s) ∧ h = State.singleton l (val s)

def slEquals (e e' : ValueExp Var) : StateProp Var :=
    λ ⟨s,_⟩ => e s = e' s

def slSubst (P : StateProp Var) (v : Var) (e : ValueExp Var) : StateProp Var :=
  fun s => P (s.substituteStack v (e s.stack))

def slNot (P : StateProp Var) : StateProp Var := λ s => ¬ P s

def slAnd (P Q : StateProp Var) : StateProp Var := P ⊓ Q

def slOr (P Q : StateProp Var) : StateProp Var := P ⊔ Q

def slExists {α : Type} (P : α → StateProp Var) : StateProp Var := ⨆ (x : α), P x

def slAll {α : Type} (P : α → StateProp Var) : StateProp Var := ⨅ (x : α), P x

def slSepCon (P Q : StateProp Var) : StateProp Var :=
  λ ⟨s,h⟩ => ∃ h₁ h₂, P ⟨s, h₁⟩ ∧ Q ⟨s, h₂⟩ ∧ disjoint h₁ h₂ ∧ h₁ ∪ h₂ = h

def slBigSepCon (n : Nat) (P : ℕ → StateProp Var) : StateProp Var :=
  match n with
  | 0 => slEmp
  | n+1 => slSepCon (P (n)) (slBigSepCon n P)

def slSepImp (P Q : StateProp Var) : StateProp Var :=
  λ ⟨s,h⟩ => ∀ h', disjoint h h' → P ⟨s,h'⟩ → Q ⟨s,(h ∪ h')⟩


open Lean

declare_syntax_cat sl

syntax "sTrue" : sl
syntax "sFalse" : sl
syntax "emp" : sl
syntax term " ↦ " term : sl
syntax term:51 " = " term:51 : sl
syntax "[[" term "]]" : sl
syntax sl:min "( " term " ↦ " term " )" : sl
syntax:40 "¬" sl:41 : sl
syntax:35 sl:36 " ∧ " sl:35 : sl
syntax:30 sl:31 " ∨ " sl:30 : sl
syntax:max "∃ " explicitBinders ". " sl : sl
syntax:max "∀ " explicitBinders ". " sl : sl
syntax:35 sl:36 " ∗ " sl:35 : sl
syntax:36 "[∗] " binderIdent  " ∈ " " { " " ... " term " }. " sl:36 : sl
syntax:25 sl:26 " -∗ " sl:25 : sl
syntax "("sl")" : sl

syntax "`[sl| " sl " ]" : term
syntax "`[sl| " sl " ⊢ " sl " ]" : term

syntax "`[sl " term " | " sl " ]" : term
syntax "`[sl " term  " | " sl " ⊢ " sl " ]" : term

macro_rules
  | `(term| `[sl| sTrue]) => `(slTrue)
  | `(term| `[sl| sFalse]) => `(slFalse)
  | `(term| `[sl| emp]) => `(slEmp)
  | `(term| `[sl| $l:term ↦ $r:term]) => `(slPointsTo $l $r)
  | `(term| `[sl| $l:term = $r:term]) => `(slEquals $l $r)
  | `(term| `[sl| [[$t:term]]]) => `($t)
  | `(term| `[sl| $f( $x:term ↦ $e ) ]) => `(slSubst `[sl|$f] $x $e)
  | `(term| `[sl| ¬ $f:sl]) => `(slNot `[sl|$f])
  | `(term| `[sl| $l:sl ∧ $r:sl]) => `(slAnd `[sl|$l] `[sl|$r])
  | `(term| `[sl| $l:sl ∨ $r:sl]) => `(slOr `[sl|$l] `[sl|$r])
  | `(term| `[sl| ∃ $xs. $f:sl]) => do expandExplicitBinders ``slExists xs (← `(`[sl|$f]))
  | `(term| `[sl| ∀ $xs. $f:sl]) => do expandExplicitBinders ``slAll xs (← `(`[sl|$f]))
  | `(term| `[sl| $l:sl ∗ $r:sl]) => `(slSepCon `[sl|$l] `[sl|$r])
  | `(term| `[sl| [∗] $x:ident ∈ { ... $m}. $f:sl]) =>
      `(slBigSepCon $m (fun $x ↦ `[sl| $f]))
  | `(term| `[sl| [∗] $_:hole ∈ { ... $m}. $f:sl]) =>
      `(slBigSepCon $m (fun _ ↦ `[sl| $f]))
  | `(term| `[sl| $l:sl -∗ $r:sl]) => `(slSepImp `[sl|$l] `[sl|$r])
  | `(term| `[sl| ($f:sl)]) => `(`[sl|$f])
  | `(term| `[sl| $l:sl ⊢ $r:sl]) => `(`[sl|$l] ≤ `[sl|$r])

  | `(term| `[sl $v:term| sTrue]) => `(@slTrue $v)
  | `(term| `[sl $v:term| sFalse]) => `(@slFalse $v)
  | `(term| `[sl $v:term| emp]) => `(@slEmp $v)
  | `(term| `[sl $v:term| $l:term ↦ $r:term]) => `(@slPointsTo $v $l $r)
  | `(term| `[sl $v:term| $l:term = $r:term]) => `(@slEquals $v $l $r)
  | `(term| `[sl $_| [[$t:term]]]) => `($t)
  | `(term| `[sl $v:term| $f( $x:term ↦ $e ) ]) => `(@slSubst $v `[sl $v|$f] $x $e)
  | `(term| `[sl $v:term| ¬ $f:sl]) => `(slNot `[sl $v|$f])
  | `(term| `[sl $v:term| $l:sl ∧ $r:sl]) => `(slAnd `[sl $v|$l] `[sl $v|$r])
  | `(term| `[sl $v:term| $l:sl ∨ $r:sl]) => `(slOr `[sl $v|$l] `[sl $v|$r])
  | `(term| `[sl $v:term| ∃ $xs. $f:sl]) => do expandExplicitBinders ``slExists xs (← `(`[sl $v|$f]))
  | `(term| `[sl $v:term| ∀ $xs. $f:sl]) => do expandExplicitBinders ``slAll xs (← `(`[sl $v|$f]))
  | `(term| `[sl $v:term| $l:sl ∗ $r:sl]) => `(slSepCon `[sl $v|$l] `[sl $v|$r])
  | `(term| `[sl $v:term| [∗] $x:ident ∈ { ... $m}. $f:sl]) =>
      `(slBigSepCon $m (fun $x ↦ `[sl $v| $f]))
  | `(term| `[sl $v:term| [∗] $_:hole ∈ { ... $m}. $f:sl]) =>
      `(slBigSepCon $m (fun _ ↦ `[sl $v| $f]))
  | `(term| `[sl $v:term| $l:sl -∗ $r:sl]) => `(slSepImp `[sl $v|$l] `[sl $v|$r])
  | `(term| `[sl $v:term| ($f:sl)]) => `(`[sl $v|$f])
  | `(term| `[sl $v:term | $l:sl ⊢ $r:sl]) => `(`[sl $v|$l] ≤ `[sl $v|$r])

open Syntax

open Lean PrettyPrinter Delaborator

@[app_unexpander slTrue]
def unexpandSlTrue : Unexpander
  | `($_) => `(`[sl| sTrue])

@[app_unexpander slFalse]
def unexpandSlFalse : Unexpander
  | `($_) => `(`[sl| sFalse])

@[app_unexpander slEmp]
def unexpandSlEmp : Unexpander
  | `($_) => `(`[sl| emp])

@[app_unexpander slPointsTo]
def unexpandSlPointsTo : Unexpander
  | `($_ $l $r) => `(`[sl| $l:term ↦ $r:term])
  | _ => throw ()

@[app_unexpander slEquals]
def unexpandSlEquals : Unexpander
  | `($_ $l $r) => `(`[sl| $l:term = $r:term])
  | _ => throw ()


def isAtom : TSyntax `sl → Bool
  | `(sl| emp) => true
  | `(sl| $_:term ↦ $_:term) => true
  | `(sl| $_:term = $_:term) => true
  | `(sl| $_ ) => false

@[app_unexpander slNot]
def unexpandSlNot : Unexpander
  | `($_ `[sl|$t]) =>
    if isAtom t then `(`[sl| ¬ $t]) else `(`[sl| ¬ ($t)])
  | `($_ $t) => `(`[sl| ¬ [[$t]]])
  | _ => throw ()

@[app_unexpander slSubst]
def unexpandSlSubst : Unexpander
  | `($_ `[sl|$f] $v:term $e:term) =>
    if isAtom f then `(`[sl| $f( $v ↦ $e) ]) else `(`[sl| ($f)( $v:term ↦ $e:term) ])
  | `($_ $f $v $e) => `(`[sl| [[$f]]( $v ↦ $e) ])
  | _ => throw ()

def requireBracketsAnd : TSyntax `sl → Bool
  | `(sl| ¬ $_:sl) => false
  | `(sl| $_:sl ∗ $_:sl) => false
  | `(sl| [∗] $_ ∈ { ... $_}. $_) => false
  | `(sl| $_:sl ∧ $_:sl) => false
  | `(sl| $f:sl) => !isAtom f

def bracketsAnd [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `sl)
  | `(term| `[sl|$f:sl]) => if requireBracketsAnd f then `(sl| ( $f ) ) else `(sl| $f )
  | `(term| $t:term) => `(sl|[[$t]])

@[app_unexpander slAnd]
def unexpandSlAnd : Unexpander
  | `($_ $l $r) => do `(`[sl| $(← bracketsAnd l) ∧ $(← bracketsAnd r)])
  | _ => throw ()

def requireBracketsOr : TSyntax `sl → Bool
  | `(sl| ¬ $_:sl) => false
  | `(sl| $f:sl) => !isAtom f

def bracketsOr [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `sl)
  | `(term| `[sl|$f:sl]) => if requireBracketsAnd f then `(sl| ( $f ) ) else `(sl| $f )
  | `(term| $t:term) => `(sl|[[$t]])

@[app_unexpander slOr]
def unexpandSlOr : Unexpander
  | `($_ $l $r) => do `(`[sl| $(← bracketsOr l) ∨ $(← bracketsOr r)])
  | _ => throw ()

@[app_unexpander slExists]
def unexpandSlExists : Unexpander
  | `($_ fun $x:ident => `[sl| ∃ $y:ident $[$z:ident]*. $f]) =>
    `(`[sl| ∃ $x:ident $y:ident $[$z:ident]*. $f])
  | `($_ fun $x:ident => `[sl|$f:sl]) => `(`[sl| ∃ $x:ident. $f])
  | _ => throw ()

@[app_unexpander slAll]
def unexpandSlAll : Unexpander
  | `($_ fun $x:ident => `[sl| ∀ $y:ident $[$z:ident]*. $f]) =>
    `(`[sl| ∀ $x:ident $y:ident $[$z:ident]*. $f])
  | `($_ fun $x:ident => `[sl|$f:sl]) => `(`[sl| ∀ $x:ident. $f])
  | _ => throw ()

@[app_unexpander slSepCon]
def unexpandSlSepCon : Unexpander
  | `($_ $l $r) => do `(`[sl| $(← bracketsAnd l) ∗ $(← bracketsAnd r)])
  | _ => throw ()

@[app_unexpander slBigSepCon]
def unexpandBigSepCon : Unexpander
  | `($_ $n fun $x:ident => $f) => do
      `(`[sl| [∗] $x:ident ∈ { ... $n}. $(← bracketsAnd f)])
  | _ => throw ()

def requireBracketsSepImp : TSyntax `sl → Bool
  | `(sl| ¬ $_:sl) => false
  | `(sl| $_:sl -∗ $_:sl) => false
  | `(sl| $_:sl ∧ $_:sl) => false
  | `(sl| $_:sl ∗ $_:sl) => false
  | `(sl| [∗] $_ ∈ { ... $_}. $_) => false
  | `(sl| $_:sl ∨ $_:sl) => false
  | `(sl| $f:sl) => !isAtom f

def bracketsSepImp [Monad m] [MonadRef m] [MonadQuotation m] : TSyntax `term → m (TSyntax `sl)
  | `(term| `[sl|$f:sl]) => if requireBracketsSepImp f then `(sl| ( $f ) ) else `(sl| $f )
  | `(term| $t:term) => `(sl|[[$t]])

@[app_unexpander slSepImp]
def unexpandSlSepImp : Unexpander
  | `($_ `[sl| $l -∗ $r] $f) => do `(`[sl| ($l -∗ $r) -∗ $(← bracketsSepImp f)])
  | `($_ $l $r) => do `(`[sl| $(← bracketsSepImp l) -∗ $(← bracketsSepImp r)])
  | _ => throw ()

end SL
