import InvLimDiss.Program.State
import InvLimDiss.Program.Expressions
import InvLimDiss.SL.Entailment
import InvLimDiss.Mathlib.Ennreal
import InvLimDiss.SL.Classical
import InvLimDiss.SL.Fuzzy

/-@
This file contains definitions and syntax about unit valued quantitative separation logic
-/

namespace QSL

open State Syntax ENNReal

def StateRVInf (Var : Type) : Type := State Var → ENNReal

noncomputable instance {Var : Type} : CompleteLattice (StateRVInf Var) := Pi.instCompleteLattice

instance : Entailment (StateRVInf Var) := ⟨fun P Q => P ≤ Q⟩

variable {Var : Type}

noncomputable def qslTrue : StateRVInf Var := λ _ => 1

noncomputable def qslInfty : StateRVInf Var := λ _ => ∞

noncomputable def qslFalse : StateRVInf Var := λ _ => 0

noncomputable def qslEmp : StateRVInf Var := λ ⟨_,h⟩ => iteOneZero (h = ∅)

noncomputable def qslPointsTo (loc val : ValueExp Var) : StateRVInf Var :=
    λ ⟨s,h⟩ => iteOneZero (∃ l : ℕ+, l = (loc s) ∧ h = State.singleton l (val s))

noncomputable def qslEquals (e e' : ValueExp Var) : StateRVInf Var :=
    λ ⟨s,_⟩ => iteOneZero (e s = e' s)

noncomputable def qslReal (e : QuantExp Var) : StateRVInf Var :=
    λ ⟨s,_⟩ => e s

noncomputable def qslIverson (P : State Var → Prop) : StateRVInf Var := λ s => iteOneZero (P s)

noncomputable def qslUnitToENNReal (f : FSL.StateRV Var) : StateRVInf Var :=
    λ s => ofNNReal ⟨(f s).val, unitInterval.nonneg'⟩

noncomputable def qslSubst (P : StateRVInf Var) (v : Var) (e : ValueExp Var) : StateRVInf Var :=
  fun s => P (s.substituteStack v (e s.stack))

noncomputable def qslMin (P Q : StateRVInf Var) : StateRVInf Var := P ⊓ Q

noncomputable def qslMax (P Q : StateRVInf Var) : StateRVInf Var := P ⊔ Q

noncomputable def qslAdd (P Q : StateRVInf Var) : StateRVInf Var := λ s => (P s) + (Q s)

noncomputable def qslMul (P Q : StateRVInf Var) : StateRVInf Var := λ s => P s * Q s

noncomputable def qslSup {α : Type} (P : α → StateRVInf Var) : StateRVInf Var := ⨆ (x : α), P x

noncomputable def qslInf {α : Type} (P : α → StateRVInf Var) : StateRVInf Var := ⨅ (x : α), P x

noncomputable def qslSepMul (P Q : StateRVInf Var) : StateRVInf Var :=
  fun s => sSup { x | ∃ h₁ h₂, disjoint h₁ h₂ ∧ h₁ ∪ h₂ = s.heap ∧ x = P ⟨s.stack, h₁⟩ * Q ⟨s.stack, h₂⟩}

noncomputable def qslBigSepMul (n : Nat) (P : ℕ → StateRVInf Var) : StateRVInf Var :=
  match n with
  | 0 => qslEmp
  | n+1 => qslSepMul (P n) (qslBigSepMul n P)

noncomputable def qslSepDiv (P Q : StateRVInf Var) : StateRVInf Var :=
  fun s => sInf { x | ∃ h', disjoint s.heap h' ∧ x = div' (Q ⟨s.stack,s.heap ∪ h'⟩) (P ⟨s.stack,h'⟩) }

open Lean

declare_syntax_cat qsl

syntax "qTrue" : qsl
syntax "qFalse" : qsl
syntax "∞" : qsl
syntax "emp" : qsl
syntax term " ↦ " term : qsl
syntax term:51 " = " term:51 : qsl
syntax "<" term:51 ">" : qsl
syntax "[[" term "]]" : qsl
syntax "⁅" term "⁆" : qsl
syntax "⁅" sl "⁆" : qsl
syntax "⁅" fsl "⁆" : qsl
syntax:41 qsl:42 "( " term " ↦ " term " )" : qsl
syntax:35 qsl:36 " ⊓ " qsl:35 : qsl
syntax:30 qsl:31 " ⊔ " qsl:30 : qsl
syntax:30 qsl:31 " + " qsl:30 : qsl
syntax:35 qsl:36 " ⬝ " qsl:35 : qsl
syntax:max "S " explicitBinders ". " qsl : qsl
syntax:max "I " explicitBinders ". " qsl : qsl
syntax:35 qsl:36 " ⋆ " qsl:35 : qsl
syntax:36 "[⋆] " binderIdent " ∈ " " { " " ... " term " }. " qsl:36 : qsl
syntax:25 qsl:26 " -⋆ " qsl:25 : qsl
syntax "("qsl")" : qsl

syntax "`[qsl| " qsl " ]" : term
syntax "`[qsl| " qsl " ⊢ " qsl " ]" : term

syntax "`[qsl " term " | " qsl " ]" : term
syntax "`[qsl " term " | " qsl " ⊢ " qsl " ]" : term

macro_rules
  | `(term| `[qsl| qTrue]) => `(qslTrue)
  | `(term| `[qsl| qFalse]) => `(qslFalse)
  | `(term| `[qsl| ∞]) => `(qslInfty)
  | `(term| `[qsl| emp]) => `(qslEmp)
  | `(term| `[qsl| $l:term ↦ $r:term]) => `(qslPointsTo $l $r)
  | `(term| `[qsl| $l:term = $r:term]) => `(qslEquals $l $r)
  | `(term| `[qsl| [[$t:term]]]) => `($t)
  | `(term| `[qsl| < $t:term >]) => `(qslReal $t)
  | `(term| `[qsl| ⁅$t:term⁆]) => `(qslIverson $t)
  | `(term| `[qsl| ⁅$l:sl⁆]) => `(qslIverson `[sl| $l])
  | `(term| `[qsl| ⁅$l:fsl⁆]) => `(qslUnitToReal `[fsl| $l])
  | `(term| `[qsl| $f( $x:term ↦ $e ) ]) => `(qslSubst `[qsl|$f] $x $e)
  | `(term| `[qsl| $l:qsl ⊓ $r:qsl]) => `(qslMin `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| $l:qsl ⊔ $r:qsl]) => `(qslMax `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| $l:qsl + $r:qsl]) => `(qslAdd `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| $l:qsl ⬝ $r:qsl]) => `(qslMul `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| S $xs. $f:qsl]) => do expandExplicitBinders ``qslSup xs (← `(`[qsl|$f]))
  | `(term| `[qsl| I $xs. $f:qsl]) => do expandExplicitBinders ``qslInf xs (← `(`[qsl|$f]))
  | `(term| `[qsl| $l:qsl ⋆ $r:qsl]) => `(qslSepMul `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| [⋆] $x:ident ∈ { ... $m }. $f:qsl]) =>
      `(qslBigSepMul $m (fun $x ↦ `[qsl| $f]))
  | `(term| `[qsl| [⋆] $_:hole ∈ { ... $m }. $f:qsl]) =>
      `(qslBigSepMul $m (fun _ ↦ `[qsl| $f]))
  | `(term| `[qsl| $l:qsl -⋆ $r:qsl]) => `(qslSepDiv `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| ($f:qsl)]) => `(`[qsl|$f])
  | `(term| `[qsl| $l:qsl ⊢ $r:qsl]) => `(`[qsl|$l] ≤ `[qsl|$r])
  | `(term| `[qsl $v:term | qTrue]) => `(@qslTrue $v)
  | `(term| `[qsl $v:term | qFalse]) => `(@qslFalse $v)
  | `(term| `[qsl $v:term | ∞]) => `(@qslInfty $v)
  | `(term| `[qsl $v:term| emp]) => `(@qslEmp $v)
  | `(term| `[qsl $v:term| $l:term ↦ $r:term]) => `(@qslPointsTo $v $l $r)
  | `(term| `[qsl $v:term| $l:term = $r:term]) => `(@qslEquals $v $l $r)
  | `(term| `[qsl $_| [[$t:term]]]) => `($t)
  | `(term| `[qsl $v:term| <$t:term>]) => `(@qslReal $v $t)
  | `(term| `[qsl $v:term| ⁅$t:term⁆]) => `(@qslIverson $v $t)
  | `(term| `[qsl $v:term| ⁅$l:sl⁆]) => `(@qslIverson $v `[sl $v| $l])
  | `(term| `[qsl $v:term| $f( $x:term ↦ $e ) ]) => `(@qslSubst $v `[qsl $v|$f] $x $e)
  | `(term| `[qsl $v:term| $l:qsl ⊓ $r:qsl]) => `(qslMin `[qsl $v|$l] `[qsl $v|$r])
  | `(term| `[qsl $v:term| $l:qsl ⊔ $r:qsl]) => `(fslMax `[qsl $v|$l] `[qsl $v|$r])
  | `(term| `[qsl $v:term| $l:qsl + $r:qsl]) => `(fslAdd `[qsl $v|$l] `[qsl $v|$r])
  | `(term| `[qsl $v:term| $l:qsl ⬝ $r:qsl]) => `(fslMul `[qsl $v|$l] `[qsl $v|$r])
  | `(term| `[qsl $v:term| S $xs. $f:qsl]) => do expandExplicitBinders ``qslSup xs (← `(`[qsl $v|$f]))
  | `(term| `[qsl $v:term| I $xs. $f:qsl]) => do expandExplicitBinders ``qslInf xs (← `(`[qsl $v|$f]))
  | `(term| `[qsl $v:term| $l:qsl ⋆ $r:qsl]) => `(qslSepMul `[qsl $v|$l] `[qsl $v|$r])
  | `(term| `[qsl $v:term| [⋆] $x:ident ∈ { ... $m }. $f:qsl]) =>
      `(qslBigqepMul $m (fun $x ↦ `[qsl $v| $f]))
  | `(term| `[qsl $v:term| [⋆] $_:hole ∈ { ... $m }. $f:qsl]) =>
      `(qslBigqepMul $m (fun _ ↦ `[qsl $v| $f]))
  | `(term| `[qsl $v:term| $l:qsl -⋆ $r:qsl]) => `(qslSepDiv `[qsl $v|$l] `[qsl $v|$r])
  | `(term| `[qsl $v:term| ($f:qsl)]) => `(`[qsl $v|$f])
  | `(term| `[qsl $v:term | $l:qsl ⊢ $r:qsl]) => `(`[qsl $v|$l] ≤ `[qsl $v|$r])


open Lean PrettyPrinter Delaborator

@[app_unexpander qslTrue]
def unexpandQslTrue : Unexpander
  | `($_) => `(`[qsl| qTrue])

@[app_unexpander qslFalse]
def unexpandQslFalse : Unexpander
  | `($_) => `(`[qsl| qFalse])

@[app_unexpander qslInfty]
def unexpandQslInfty : Unexpander
  | `($_) => `(`[qsl| ∞])

@[app_unexpander qslEmp]
def unexpandQslEmp : Unexpander
  | `($_) => `(`[qsl| emp])

@[app_unexpander qslPointsTo]
def unexpandQslPointsTo : Unexpander
  | `($_ $l $r) => `(`[qsl| $l:term ↦ $r:term])
  | _ => throw ()

@[app_unexpander qslEquals]
def unexpandQslEquals : Unexpander
  | `($_ $l $r) => `(`[qsl| $l:term = $r:term])
  | _ => throw ()

@[app_unexpander qslReal]
def unexpandQslReal : Unexpander
  | `($_ $t) => `(`[qsl| < $t:term >])
  | _ => throw ()

@[app_unexpander qslIverson]
def unexpandQslIverson : Unexpander
  | `($_ `[sl| $l:sl]) => `(`[qsl| ⁅$l:sl⁆])
  | `($_ $t:term) => `(`[qsl| ⁅$t:term⁆])
  | _ => throw ()

@[app_unexpander qslUnitToENNReal]
def unexpandQslUnitToENNReal : Unexpander
  | `($_ `[fsl| $l:fsl]) => `(`[qsl| ⁅$l:fsl⁆])
  | _ => throw ()

def isAtom : TSyntax `qsl → Bool
  | `(qsl| emp) => true
  | `(qsl| $_:term ↦ $_:term) => true
  | `(qsl| $_:term = $_:term) => true
  | `(qsl| <$_:term>) => true
  | `(qsl| ⁅$_:term⁆) => true
  | `(qsl| $_:qsl( $_ ↦ $_)) => true
  | `(qsl| $_ ) => false

@[app_unexpander qslSubst]
def unexpandQslSubst : Unexpander
  | `($_ `[qsl|$f] $v:term $e:term) =>
    if isAtom f then `(`[qsl| $f( $v ↦ $e) ]) else `(`[qsl| ($f)( $v:term ↦ $e:term) ])
  | `($_ $f $v $e) => `(`[qsl| [[$f]]( $v ↦ $e) ])
  | _ => throw ()

def requireBracketsMin : TSyntax `qsl → Bool
  | `(qsl| $_:qsl ⋆ $_:qsl) => false
  | `(qsl| $_:qsl ⊓ $_:qsl) => false
  | `(qsl| $_:qsl ⬝ $_:qsl) => false
  | `(qsl| [⋆] $_ ∈ { ... $_ }. $_) => false
  | `(qsl| $f:qsl) => !isAtom f

def requireBracketsMin_left : TSyntax `qsl → Bool
  | `(qsl| [⋆] $_ ∈ { ... $_ }. $_) => false
  | `(qsl| $f:qsl) => !isAtom f

def bracketsMin [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => if requireBracketsMin f then `(qsl| ( $f ) ) else `(qsl| $f )
  | `(term| $t:term) => `(qsl|[[$t]])

def bracketsMin_left [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => if requireBracketsMin_left f then `(qsl| ( $f ) ) else `(qsl| $f )
  | `(term| $t:term) => `(qsl|[[$t]])

@[app_unexpander qslMin]
def unexpandQslMin : Unexpander
  | `($_ $l $r) => do `(`[qsl| $(← bracketsMin_left l) ⊓ $(← bracketsMin r)])
  | _ => throw ()

def requireBracketsMax : TSyntax `qsl → Bool
  | `(qsl| $_:qsl ⊔ $_:qsl) => false
  | `(qsl| $f:qsl) => !isAtom f

def requireBracketsMax_left : TSyntax `qsl → Bool
  | `(qsl| $_:qsl ⊔ $_:qsl) => false
  | `(qsl| $f:qsl) => !isAtom f

def bracketsMax [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => if requireBracketsMax f then `(qsl| ( $f ) ) else `(qsl| $f )
  | `(term| $t:term) => `(qsl|[[$t]])

def bracketsMax_left [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => if requireBracketsMax f then `(qsl| ( $f ) ) else `(qsl| $f )
  | `(term| $t:term) => `(qsl|[[$t]])

@[app_unexpander qslMax]
def unexpandQslMax : Unexpander
  | `($_ $l $r) => do `(`[qsl| $(← bracketsMax_left l) ⊔ $(← bracketsMax r)])
  | _ => throw ()

@[app_unexpander qslAdd]
def unexpandQslAdd : Unexpander
  | `($_ $l $r) => do `(`[qsl| $(← bracketsMax_left l) + $(← bracketsMax r)])
  | _ => throw ()

@[app_unexpander qslMul]
def unexpandQslMul : Unexpander
  | `($_ $l $r) => do `(`[qsl| $(← bracketsMin_left l) ⬝ $(← bracketsMin r)])
  | _ => throw ()

@[app_unexpander qslSup]
def unexpandQslSup : Unexpander
  | `($_ fun $x:ident => `[qsl| S $y:ident $[$z:ident]*. $f]) =>
    `(`[qsl| S $x:ident $y:ident $[$z:ident]*. $f])
  | `($_ fun $x:ident => `[qsl|$f:qsl]) => `(`[qsl| S $x:ident. $f])
  | _ => throw ()

@[app_unexpander qslInf]
def unexpandQslInf : Unexpander
  | `($_ fun $x:ident => `[qsl| I $y:ident $[$z:ident]*. $f]) =>
    `(`[qsl| I $x:ident $y:ident $[$z:ident]*. $f])
  | `($_ fun $x:ident => `[qsl|$f:qsl]) => `(`[qsl| I $x:ident. $f])
  | _ => throw ()

@[app_unexpander qslSepMul]
def unexpandQslSepMul : Unexpander
  | `($_ $l $r) => do `(`[qsl| $(← bracketsMin_left l) ⋆ $(← bracketsMin r)])
  | _ => throw ()

@[app_unexpander qslBigSepMul]
def unexpandBigSepCon : Unexpander
  | `($_ $n fun $x:ident => $f) => do
      `(`[qsl| [⋆] $x:ident ∈ { ... $n}. $(← bracketsMin f)])
  | _ => throw ()

def requireBracketsSepDiv : TSyntax `qsl → Bool
  | `(qsl| $_:qsl -⋆ $_:qsl) => false
  | `(qsl| $_:qsl ⊓ $_:qsl) => false
  | `(qsl| $_:qsl ⋆ $_:qsl) => false
  | `(qsl| $_:qsl ⬝ $_:qsl) => false
  | `(qsl| $_:qsl ⊔ $_:qsl) => false
  | `(qsl| $_:qsl + $_:qsl) => false
  | `(qsl| $f:qsl) => !isAtom f

def bracketsSepDiv [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => if requireBracketsSepDiv f then `(qsl| ( $f ) ) else `(qsl| $f )
  | `(term| $t:term) => `(qsl|[[$t]])

def requireBracketsSepDiv_left : TSyntax `qsl → Bool
  | `(qsl| $_:qsl ⊓ $_:qsl) => false
  | `(qsl| $_:qsl ⋆ $_:qsl) => false
  | `(qsl| $_:qsl ⬝ $_:qsl) => false
  | `(qsl| $_:qsl ⊔ $_:qsl) => false
  | `(qsl| $_:qsl + $_:qsl) => false
  | `(qsl| $f:qsl) => !isAtom f

def bracketsSepDiv_left [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => if requireBracketsSepDiv_left f then `(qsl| ( $f ) ) else `(qsl| $f )
  | `(term| $t:term) => `(qsl|[[$t]])

@[app_unexpander qslSepDiv]
def unexpandQslSepDiv : Unexpander
  | `($_ `[qsl|$l -⋆ $r] $f) => do `(`[qsl| ($l -⋆ $r) -⋆ $(← bracketsSepDiv f)])
  | `($_ $l $r) => do `(`[qsl| $(← bracketsSepDiv_left l) -⋆ $(← bracketsSepDiv r)])
  | _ => throw ()


def precise (P : StateRVInf Var) : Prop :=
  ∀ s : State Var, ∃ heap',
    heap' ⊆ s.heap ∧ ∀ heap'', heap'' ⊆ s.heap → heap' ≠ heap''
    → P ⟨s.stack, heap''⟩ = 0


end QSL
