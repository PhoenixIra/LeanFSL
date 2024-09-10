import InvLimDiss.Program.State
import InvLimDiss.Program.Expressions
import InvLimDiss.SL.Entailment
import InvLimDiss.Mathlib.Probabilities
import InvLimDiss.SL.Classical

/-@
This file contains definitions and syntax about unit valued quantitative separation logic
-/

namespace FSL

open State unitInterval Syntax

def StateRV (Var : Type) : Type := State Var → I

noncomputable instance {Var : Type} : CompleteLattice (StateRV Var) := Pi.instCompleteLattice

instance : Entailment (StateRV Var) := ⟨fun P Q => P ≤ Q⟩

variable {Var : Type}

noncomputable def fslTrue : StateRV Var := λ _ => 1

noncomputable def fslFalse : StateRV Var := λ _ => 0

noncomputable def fslEmp : StateRV Var := λ ⟨_,h⟩ => iteOneZero (h = ∅)

noncomputable def fslPointsTo (loc val : ValueExp Var) : StateRV Var :=
    λ ⟨s,h⟩ => iteOneZero (∃ l : ℕ+, l = (loc s) ∧ h = State.singleton l (val s))

noncomputable def fslEquals (e e' : ValueExp Var) : StateRV Var :=
    λ ⟨s,_⟩ => iteOneZero (e s = e' s)

noncomputable def fslReal (e : ProbExp Var) : StateRV Var :=
    λ ⟨s,_⟩ => e s

noncomputable def fslIverson (P : State Var → Prop) : StateRV Var := λ s => iteOneZero (P s)

noncomputable def fslSubst (P : StateRV Var) (v : Var) (e : ValueExp Var) : StateRV Var :=
  fun s => P (s.substituteStack v (e s.stack))

noncomputable def fslNot (P : StateRV Var) : StateRV Var := λ s => σ (P s)

noncomputable def fslMin (P Q : StateRV Var) : StateRV Var := P ⊓ Q

noncomputable def fslMax (P Q : StateRV Var) : StateRV Var := P ⊔ Q

noncomputable def fslAdd (P Q : StateRV Var) : StateRV Var := λ s => truncatedAdd (P s) (Q s)

noncomputable def fslMul (P Q : StateRV Var) : StateRV Var := λ s => P s * Q s

noncomputable def fslSup {α : Type} (P : α → StateRV Var) : StateRV Var := ⨆ (x : α), P x

noncomputable def fslInf {α : Type} (P : α → StateRV Var) : StateRV Var := ⨅ (x : α), P x

noncomputable def fslSepMul (P Q : StateRV Var) : StateRV Var :=
  fun s => sSup { x | ∃ h₁ h₂, disjoint h₁ h₂ ∧ h₁ ∪ h₂ = s.heap ∧ x = P ⟨s.stack, h₁⟩ * Q ⟨s.stack, h₂⟩}

noncomputable def fslBigSepMul (n : Nat) (P : ℕ → StateRV Var) : StateRV Var :=
  match n with
  | 0 => fslEmp
  | n+1 => fslSepMul (P n) (fslBigSepMul n P)

noncomputable def fslSepDiv (P Q : StateRV Var) : StateRV Var :=
  fun s => sInf { x | ∃ h', disjoint s.heap h' ∧ x = Q ⟨s.stack,s.heap ∪ h'⟩ / P ⟨s.stack,h'⟩ }

open Lean

declare_syntax_cat fsl

syntax "qTrue" : fsl
syntax "qFalse" : fsl
syntax "emp" : fsl
syntax term " ↦ " term : fsl
syntax term:51 " = " term:51 : fsl
syntax "<" term:51 ">" : fsl
syntax "[[" term "]]" : fsl
syntax "⁅" term "⁆" : fsl
syntax "⁅" sl "⁆" : fsl
syntax:41 fsl:42 "( " term " ↦ " term " )" : fsl
syntax:40 "~" fsl:41 : fsl
syntax:35 fsl:36 " ⊓ " fsl:35 : fsl
syntax:30 fsl:31 " ⊔ " fsl:30 : fsl
syntax:30 fsl:31 " + " fsl:30 : fsl
syntax:35 fsl:36 " ⬝ " fsl:35 : fsl
syntax:max "S " explicitBinders ". " fsl : fsl
syntax:max "I " explicitBinders ". " fsl : fsl
syntax:35 fsl:36 " ⋆ " fsl:35 : fsl
syntax:36 "[⋆] " binderIdent " ∈ " " { " " ... " term " }. " fsl:36 : fsl
syntax:25 fsl:26 " -⋆ " fsl:25 : fsl
syntax "("fsl")" : fsl

syntax "`[fsl| " fsl " ]" : term
syntax "`[fsl| " fsl " ⊢ " fsl " ]" : term

syntax "`[fsl " term " | " fsl " ]" : term
syntax "`[fsl " term " | " fsl " ⊢ " fsl " ]" : term

macro_rules
  | `(term| `[fsl| qTrue]) => `(fslTrue)
  | `(term| `[fsl| qFalse]) => `(fslFalse)
  | `(term| `[fsl| emp]) => `(fslEmp)
  | `(term| `[fsl| $l:term ↦ $r:term]) => `(fslPointsTo $l $r)
  | `(term| `[fsl| $l:term = $r:term]) => `(fslEquals $l $r)
  | `(term| `[fsl| [[$t:term]]]) => `($t)
  | `(term| `[fsl| < $t:term >]) => `(fslReal $t)
  | `(term| `[fsl| ⁅$t:term⁆]) => `(fslIverson $t)
  | `(term| `[fsl| ⁅$l:sl⁆]) => `(fslIverson `[sl| $l])
  | `(term| `[fsl| $f( $x:term ↦ $e ) ]) => `(fslSubst `[fsl|$f] $x $e)
  | `(term| `[fsl| ~ $f:fsl]) => `(fslNot `[fsl|$f])
  | `(term| `[fsl| $l:fsl ⊓ $r:fsl]) => `(fslMin `[fsl|$l] `[fsl|$r])
  | `(term| `[fsl| $l:fsl ⊔ $r:fsl]) => `(fslMax `[fsl|$l] `[fsl|$r])
  | `(term| `[fsl| $l:fsl + $r:fsl]) => `(fslAdd `[fsl|$l] `[fsl|$r])
  | `(term| `[fsl| $l:fsl ⬝ $r:fsl]) => `(fslMul `[fsl|$l] `[fsl|$r])
  | `(term| `[fsl| S $xs. $f:fsl]) => do expandExplicitBinders ``fslSup xs (← `(`[fsl|$f]))
  | `(term| `[fsl| I $xs. $f:fsl]) => do expandExplicitBinders ``fslInf xs (← `(`[fsl|$f]))
  | `(term| `[fsl| $l:fsl ⋆ $r:fsl]) => `(fslSepMul `[fsl|$l] `[fsl|$r])
  | `(term| `[fsl| [⋆] $x:ident ∈ { ... $m }. $f:fsl]) =>
      `(fslBigSepMul $m (fun $x ↦ `[fsl| $f]))
  | `(term| `[fsl| [⋆] $_:hole ∈ { ... $m }. $f:fsl]) =>
      `(fslBigSepMul $m (fun _ ↦ `[fsl| $f]))
  | `(term| `[fsl| $l:fsl -⋆ $r:fsl]) => `(fslSepDiv `[fsl|$l] `[fsl|$r])
  | `(term| `[fsl| ($f:fsl)]) => `(`[fsl|$f])
  | `(term| `[fsl| $l:fsl ⊢ $r:fsl]) => `(`[fsl|$l] ≤ `[fsl|$r])

  | `(term| `[fsl $v:term | qTrue]) => `(@fslTrue $v)
  | `(term| `[fsl $v:term | qFalse]) => `(@fslFalse $v)
  | `(term| `[fsl $v:term| emp]) => `(@fslEmp $v)
  | `(term| `[fsl $v:term| $l:term ↦ $r:term]) => `(@fslPointsTo $v $l $r)
  | `(term| `[fsl $v:term| $l:term = $r:term]) => `(@fslEquals $v $l $r)
  | `(term| `[fsl $_| [[$t:term]]]) => `($t)
  | `(term| `[fsl $v:term| <$t:term>]) => `(@fslReal $v $t)
  | `(term| `[fsl $v:term| ⁅$t:term⁆]) => `(@fslIverson $v $t)
  | `(term| `[fsl $v:term| ⁅$l:sl⁆]) => `(@fslIverson $v `[sl $v| $l])
  | `(term| `[fsl $v:term| $f( $x:term ↦ $e ) ]) => `(@fslSubst $v `[fsl $v|$f] $x $e)
  | `(term| `[fsl $v:term| ~ $f:fsl]) => `(fslNot `[fsl $v|$f])
  | `(term| `[fsl $v:term| $l:fsl ⊓ $r:fsl]) => `(fslMin `[fsl $v|$l] `[fsl $v|$r])
  | `(term| `[fsl $v:term| $l:fsl ⊔ $r:fsl]) => `(fslMax `[fsl $v|$l] `[fsl $v|$r])
  | `(term| `[fsl $v:term| $l:fsl + $r:fsl]) => `(fslAdd `[fsl $v|$l] `[fsl $v|$r])
  | `(term| `[fsl $v:term| $l:fsl ⬝ $r:fsl]) => `(fslMul `[fsl $v|$l] `[fsl $v|$r])
  | `(term| `[fsl $v:term| S $xs. $f:fsl]) => do expandExplicitBinders ``fslSup xs (← `(`[fsl $v|$f]))
  | `(term| `[fsl $v:term| I $xs. $f:fsl]) => do expandExplicitBinders ``fslInf xs (← `(`[fsl $v|$f]))
  | `(term| `[fsl $v:term| $l:fsl ⋆ $r:fsl]) => `(fslSepMul `[fsl $v|$l] `[fsl $v|$r])
  | `(term| `[fsl $v:term| [⋆] $x:ident ∈ { ... $m }. $f:fsl]) =>
      `(fslBigSepMul $m (fun $x ↦ `[fsl $v| $f]))
  | `(term| `[fsl $v:term| [⋆] $_:hole ∈ { ... $m }. $f:fsl]) =>
      `(fslBigSepMul $m (fun _ ↦ `[fsl $v| $f]))
  | `(term| `[fsl $v:term| $l:fsl -⋆ $r:fsl]) => `(fslSepDiv `[fsl $v|$l] `[fsl $v|$r])
  | `(term| `[fsl $v:term| ($f:fsl)]) => `(`[fsl $v|$f])
  | `(term| `[fsl $v:term | $l:fsl ⊢ $r:fsl]) => `(`[fsl $v|$l] ≤ `[fsl $v|$r])


open Lean PrettyPrinter Delaborator

@[app_unexpander fslTrue]
def unexpandQslTrue : Unexpander
  | `($_) => `(`[fsl| qTrue])

@[app_unexpander fslFalse]
def unexpandQslFalse : Unexpander
  | `($_) => `(`[fsl| qFalse])

@[app_unexpander fslEmp]
def unexpandQslEmp : Unexpander
  | `($_) => `(`[fsl| emp])

@[app_unexpander fslPointsTo]
def unexpandQslPointsTo : Unexpander
  | `($_ $l $r) => `(`[fsl| $l:term ↦ $r:term])
  | _ => throw ()

@[app_unexpander fslEquals]
def unexpandQslEquals : Unexpander
  | `($_ $l $r) => `(`[fsl| $l:term = $r:term])
  | _ => throw ()

@[app_unexpander fslReal]
def unexpandQslReal : Unexpander
  | `($_ $t) => `(`[fsl| < $t:term >])
  | _ => throw ()

@[app_unexpander fslIverson]
def unexpandQslIverson : Unexpander
  | `($_ `[sl| $l:sl]) => `(`[fsl| ⁅$l:sl⁆])
  | `($_ $t:term) => `(`[fsl| ⁅$t:term⁆])
  | _ => throw ()

def isAtom : TSyntax `fsl → Bool
  | `(fsl| emp) => true
  | `(fsl| $_:term ↦ $_:term) => true
  | `(fsl| $_:term = $_:term) => true
  | `(fsl| <$_:term>) => true
  | `(fsl| ⁅$_:term⁆) => true
  | `(fsl| ~$_:fsl) => true
  | `(fsl| $_:fsl( $_ ↦ $_)) => true
  | `(fsl| $_ ) => false

@[app_unexpander fslNot]
def unexpandQslNot : Unexpander
  | `($_ `[fsl|$t]) =>
    if isAtom t then `(`[fsl| ~ $t]) else `(`[fsl| ~ ($t)])
  | `($_ $t) => `(`[fsl| ~ [[$t]]])
  | _ => throw ()

@[app_unexpander fslSubst]
def unexpandQslSubst : Unexpander
  | `($_ `[fsl|$f] $v:term $e:term) =>
    if isAtom f then `(`[fsl| $f( $v ↦ $e) ]) else `(`[fsl| ($f)( $v:term ↦ $e:term) ])
  | `($_ $f $v $e) => `(`[fsl| [[$f]]( $v ↦ $e) ])
  | _ => throw ()

def requireBracketsMin : TSyntax `fsl → Bool
  | `(fsl| ~ $_:fsl) => false
  | `(fsl| $_:fsl ⋆ $_:fsl) => false
  | `(fsl| $_:fsl ⊓ $_:fsl) => false
  | `(fsl| $_:fsl ⬝ $_:fsl) => false
  | `(fsl| [⋆] $_ ∈ { ... $_ }. $_) => false
  | `(fsl| $f:fsl) => !isAtom f

def requireBracketsMin_left : TSyntax `fsl → Bool
  | `(fsl| ~ $_:fsl) => false
  | `(fsl| [⋆] $_ ∈ { ... $_ }. $_) => false
  | `(fsl| $f:fsl) => !isAtom f

def bracketsMin [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `fsl)
  | `(term| `[fsl|$f:fsl]) => if requireBracketsMin f then `(fsl| ( $f ) ) else `(fsl| $f )
  | `(term| $t:term) => `(fsl|[[$t]])

def bracketsMin_left [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `fsl)
  | `(term| `[fsl|$f:fsl]) => if requireBracketsMin_left f then `(fsl| ( $f ) ) else `(fsl| $f )
  | `(term| $t:term) => `(fsl|[[$t]])

@[app_unexpander fslMin]
def unexpandQslMin : Unexpander
  | `($_ $l $r) => do `(`[fsl| $(← bracketsMin_left l) ⊓ $(← bracketsMin r)])
  | _ => throw ()

def requireBracketsMax : TSyntax `fsl → Bool
  | `(fsl| ~ $_:fsl) => false
  | `(fsl| $_:fsl ⊔ $_:fsl) => false
  | `(fsl| $f:fsl) => !isAtom f

def requireBracketsMax_left : TSyntax `fsl → Bool
  | `(fsl| ~ $_:fsl) => false
  | `(fsl| $_:fsl ⊔ $_:fsl) => false
  | `(fsl| $f:fsl) => !isAtom f

def bracketsMax [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `fsl)
  | `(term| `[fsl|$f:fsl]) => if requireBracketsMax f then `(fsl| ( $f ) ) else `(fsl| $f )
  | `(term| $t:term) => `(fsl|[[$t]])

def bracketsMax_left [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `fsl)
  | `(term| `[fsl|$f:fsl]) => if requireBracketsMax f then `(fsl| ( $f ) ) else `(fsl| $f )
  | `(term| $t:term) => `(fsl|[[$t]])

@[app_unexpander fslMax]
def unexpandQslMax : Unexpander
  | `($_ $l $r) => do `(`[fsl| $(← bracketsMax_left l) ⊔ $(← bracketsMax r)])
  | _ => throw ()

@[app_unexpander fslAdd]
def unexpandQslAdd : Unexpander
  | `($_ $l $r) => do `(`[fsl| $(← bracketsMax_left l) + $(← bracketsMax r)])
  | _ => throw ()

@[app_unexpander fslMul]
def unexpandQslMul : Unexpander
  | `($_ $l $r) => do `(`[fsl| $(← bracketsMin_left l) ⬝ $(← bracketsMin r)])
  | _ => throw ()

@[app_unexpander fslSup]
def unexpandQslSup : Unexpander
  | `($_ fun $x:ident => `[fsl| S $y:ident $[$z:ident]*. $f]) =>
    `(`[fsl| S $x:ident $y:ident $[$z:ident]*. $f])
  | `($_ fun $x:ident => `[fsl|$f:fsl]) => `(`[fsl| S $x:ident. $f])
  | _ => throw ()

@[app_unexpander fslInf]
def unexpandQslInf : Unexpander
  | `($_ fun $x:ident => `[fsl| I $y:ident $[$z:ident]*. $f]) =>
    `(`[fsl| I $x:ident $y:ident $[$z:ident]*. $f])
  | `($_ fun $x:ident => `[fsl|$f:fsl]) => `(`[fsl| I $x:ident. $f])
  | _ => throw ()

@[app_unexpander fslSepMul]
def unexpandQslSepMul : Unexpander
  | `($_ $l $r) => do `(`[fsl| $(← bracketsMin_left l) ⋆ $(← bracketsMin r)])
  | _ => throw ()

@[app_unexpander fslBigSepMul]
def unexpandBigSepCon : Unexpander
  | `($_ $n fun $x:ident => $f) => do
      `(`[fsl| [⋆] $x:ident ∈ { ... $n}. $(← bracketsMin f)])
  | _ => throw ()

def requireBracketsSepDiv : TSyntax `fsl → Bool
  | `(fsl| ~ $_:fsl) => false
  | `(fsl| $_:fsl -⋆ $_:fsl) => false
  | `(fsl| $_:fsl ⊓ $_:fsl) => false
  | `(fsl| $_:fsl ⋆ $_:fsl) => false
  | `(fsl| $_:fsl ⬝ $_:fsl) => false
  | `(fsl| $_:fsl ⊔ $_:fsl) => false
  | `(fsl| $_:fsl + $_:fsl) => false
  | `(fsl| $f:fsl) => !isAtom f

def bracketsSepDiv [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `fsl)
  | `(term| `[fsl|$f:fsl]) => if requireBracketsSepDiv f then `(fsl| ( $f ) ) else `(fsl| $f )
  | `(term| $t:term) => `(fsl|[[$t]])

def requireBracketsSepDiv_left : TSyntax `fsl → Bool
  | `(fsl| ~ $_:fsl) => false
  | `(fsl| $_:fsl ⊓ $_:fsl) => false
  | `(fsl| $_:fsl ⋆ $_:fsl) => false
  | `(fsl| $_:fsl ⬝ $_:fsl) => false
  | `(fsl| $_:fsl ⊔ $_:fsl) => false
  | `(fsl| $_:fsl + $_:fsl) => false
  | `(fsl| $f:fsl) => !isAtom f

def bracketsSepDiv_left [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `fsl)
  | `(term| `[fsl|$f:fsl]) => if requireBracketsSepDiv_left f then `(fsl| ( $f ) ) else `(fsl| $f )
  | `(term| $t:term) => `(fsl|[[$t]])

@[app_unexpander fslSepDiv]
def unexpandQslSepDiv : Unexpander
  | `($_ `[fsl|$l -⋆ $r] $f) => do `(`[fsl| ($l -⋆ $r) -⋆ $(← bracketsSepDiv f)])
  | `($_ $l $r) => do `(`[fsl| $(← bracketsSepDiv_left l) -⋆ $(← bracketsSepDiv r)])
  | _ => throw ()


def precise (P : StateRV Var) : Prop :=
  ∀ s : State Var, ∃ heap',
    heap' ⊆ s.heap ∧ ∀ heap'', heap'' ⊆ s.heap → heap' ≠ heap''
    → P ⟨s.stack, heap''⟩ = 0


end FSL
