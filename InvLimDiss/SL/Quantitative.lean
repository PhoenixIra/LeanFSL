import InvLimDiss.Program.State
import InvLimDiss.Program.Expressions
import InvLimDiss.Analysis.Probabilities

/-
This file contains definitions and lemmas about unit valued quantitative separation logic
-/

namespace QSL

open State unitInterval Syntax

def StateRV (Var : Type) : Type := State Var → I

variable {Var : Type}

noncomputable def qslEmp : StateRV Var := λ ⟨_,h⟩ => iteOneZero (h = emptyHeap)

noncomputable def qslPointsTo (loc val : ValueExp Var) : StateRV Var :=
    λ ⟨s,h⟩ => iteOneZero (∃ n : ℕ, n = loc s ∧ h n = some (val s))

noncomputable def qslEquals (e e' : ValueExp Var) : StateRV Var :=
    λ ⟨s,_⟩ => iteOneZero (e s = e' s)

noncomputable def qslPure (P : Prop) : StateRV Var := λ _ => iteOneZero P

noncomputable def qslIverson (P : State Var → Prop) : StateRV Var := λ s => iteOneZero (P s)

noncomputable def qslNot (P : StateRV Var) : StateRV Var := λ s => σ (P s)

noncomputable def qslMin (P Q : StateRV Var) : StateRV Var := λ s => min (P s) (Q s)

noncomputable def qslMax (P Q : StateRV Var) : StateRV Var := λ s => max (P s) (Q s)

noncomputable def qslAdd (P Q : StateRV Var) : StateRV Var := λ s => truncatedAdd (P s) (Q s)

noncomputable def qslSup {α : Type} (P : α → StateRV Var) : StateRV Var := λ s => sSup {P x s | x : α}

noncomputable def qslInf {α : Type} (P : α → StateRV Var) : StateRV Var := λ s => sInf {P x s | x : α}

noncomputable def qslSepMul (P Q : StateRV Var) : StateRV Var :=
  λ ⟨s,h⟩ => sSup { x | ∃ h₁ h₂, disjoint h₁ h₂ ∧ h₁ ∪ h₂ = h ∧ x = P ⟨s, h₁⟩ * Q ⟨s, h₂⟩}

noncomputable def qslSepDiv (P Q : StateRV Var) : StateRV Var :=
  λ ⟨s,h⟩ => sInf { x | ∃ h', disjoint h h' ∧ x = Q ⟨s,(h ∪ h')⟩ / P ⟨s,h'⟩ }

noncomputable def qslEntailment (P Q : StateRV Var) : Prop :=
  ∀ s, P s ≤ Q s

open Lean

declare_syntax_cat qsl

syntax "emp" : qsl
syntax term " ↦ " term : qsl
syntax term:51 " = " term:51 : qsl
syntax "[[" term "]]" : qsl
syntax "⌜" term "⌝" : qsl
syntax "⁅" term "⁆" : qsl
syntax:max "~" qsl : qsl
syntax:35 qsl:36 " ⊓ " qsl:35 : qsl
syntax:30 qsl:31 " ⊔ " qsl:30 : qsl
syntax:max "S " explicitBinders ". " qsl : qsl
syntax:max "I " explicitBinders ". " qsl : qsl
syntax:35 qsl:36 " ⋆ " qsl:35 : qsl
syntax:25 qsl:26 " -⋆ " qsl:25 : qsl
syntax "("qsl")" : qsl

syntax "[qsl| " qsl " ]" : term
syntax "[qsl| " qsl " ⊢ " qsl " ]" : term

syntax "[qsl " term " | " qsl " ]" : term
syntax "[qsl " term " | " qsl " ⊢ " qsl " ]" : term

macro_rules
  | `(term| [qsl| emp]) => `(qslEmp)
  | `(term| [qsl| $l:term ↦ $r:term]) => `(qslPointsTo $l $r)
  | `(term| [qsl| $l:term = $r:term]) => `(qslEquals $l $r)
  | `(term| [qsl| [[$t:term]]]) => `($t)
  | `(term| [qsl| ⌜$t:term⌝]) => `(qslPure $t)
  | `(term| [qsl| ⁅$t:term⁆]) => `(qslIverson $t)
  | `(term| [qsl| ~ $f:qsl]) => `(qslNot [qsl|$f])
  | `(term| [qsl| $l:qsl ⊓ $r:qsl]) => `(qslMin [qsl|$l] [qsl|$r])
  | `(term| [qsl| $l:qsl ⊔ $r:qsl]) => `(qslMax [qsl|$l] [qsl|$r])
  | `(term| [qsl| S $xs. $f:qsl]) => do expandExplicitBinders ``qslSup xs (← `([qsl|$f]))
  | `(term| [qsl| I $xs. $f:qsl]) => do expandExplicitBinders ``qslInf xs (← `([qsl|$f]))
  | `(term| [qsl| $l:qsl ⋆ $r:qsl]) => `(qslSepMul [qsl|$l] [qsl|$r])
  | `(term| [qsl| $l:qsl -⋆ $r:qsl]) => `(qslSepDiv [qsl|$l] [qsl|$r])
  | `(term| [qsl| $l:qsl ⊢ $r:qsl]) => `(qslEntailment [qsl|$l] [qsl|$r])

  | `(term| [qsl $v:term| emp]) => `(@qslEmp $v)
  | `(term| [qsl $v:term| $l:term ↦ $r:term]) => `(@qslPointsTo $v $l $r)
  | `(term| [qsl $v:term| $l:term = $r:term]) => `(@qslEquals $v $l $r)
  | `(term| [qsl $_| [[$t:term]]]) => `($t)
  | `(term| [qsl $v:term| ⌜$t:term⌝]) => `(@qslPure $v $t)
  | `(term| [qsl $v:term| ⁅$t:term⁆]) => `(@qslIverson $v $t)
  | `(term| [qsl $v:term| ~ $f:qsl]) => `(qslNot [qsl $v|$f])
  | `(term| [qsl $v:term| $l:qsl ⊓ $r:qsl]) => `(qslAnd [qsl $v|$l] [qsl $v|$r])
  | `(term| [qsl $v:term| $l:qsl ⊔ $r:qsl]) => `(qslOr [qsl $v|$l] [qsl $v|$r])
  | `(term| [qsl $v:term| S $xs. $f:qsl]) => do expandExplicitBinders ``qslSup xs (← `([qsl $v|$f]))
  | `(term| [qsl $v:term| I $xs. $f:qsl]) => do expandExplicitBinders ``qslInf xs (← `([qsl $v|$f]))
  | `(term| [qsl $v:term| $l:qsl ⋆ $r:qsl]) => `(qslSepCon [qsl $v|$l] [qsl $v|$r])
  | `(term| [qsl $v:term| $l:qsl -⋆ $r:qsl]) => `(qslSepImp [qsl $v|$l] [qsl $v|$r])
  | `(term| [qsl $v:term| ($f:qsl)]) => `([qsl $v|$f])
  | `(term| [qsl $v:term | $l:qsl ⊢ $r:qsl]) => `(@qslEntailment $v [qsl|$l] [qsl|$r])


open Lean PrettyPrinter Delaborator

@[app_unexpander qslEmp]
def unexpandQslEmp : Unexpander
  | `($_) => `([qsl| emp])

@[app_unexpander qslPointsTo]
def unexpandQslPointsTo : Unexpander
  | `($_ $l $r) => `([qsl| $l:term ↦ $r:term])
  | _ => throw ()

@[app_unexpander qslEquals]
def unexpandQslEquals : Unexpander
  | `($_ $l $r) => `([qsl| $l:term = $r:term])
  | _ => throw ()

@[app_unexpander qslPure]
def unexpandQslPure : Unexpander
  | `($_ $t) => `([qsl| ⌜$t:term⌝])
  | _ => throw ()

@[app_unexpander qslIverson]
def unexpandQslIverson : Unexpander
  | `($_ $t) => `([qsl| ⁅$t:term⁆])
  | _ => throw ()

def isAtom : TSyntax `qsl → Bool
  | `(qsl| emp) => true
  | `(qsl| $_:term ↦ $_:term) => true
  | `(qsl| $_:term = $_:term) => true
  | `(qsl| ⌜$_:term⌝) => true
  | `(qsl| ⁅$_:term⁆) => true
  | `(qsl| $_ ) => false

@[app_unexpander qslNot]
def unexpandQslNot : Unexpander
  | `($_ [qsl|$t]) =>
    if isAtom t then `([qsl| ~ $t]) else `([qsl| ~ ($t)])
  | `($_ $t) => `([qsl| ~ [[$t]]])
  | _ => throw ()

@[app_unexpander qslMin]
def unexpandQslMin : Unexpander
  | `($_ [qsl|$l] [qsl|$r]) => `([qsl| $l ⊓ $r])
  | `($_ $l [qsl|$r]) => `([qsl| [[$l]] ⊓ $r])
  | `($_ [qsl|$l] $r) => `([qsl| $l ⊓ [[$r]]])
  | `($_ $l $r) => `([qsl| [[$l]] ⊓ [[$r]]])
  | _ => throw ()

@[app_unexpander qslMax]
def unexpandQslMax : Unexpander
  | `($_ [qsl|$l] [qsl|$r]) => `([qsl| $l ⊔ $r])
  | `($_ $l [qsl|$r]) => `([qsl| [[$l]] ⊔ $r])
  | `($_ [qsl|$l] $r) => `([qsl| $l ⊔ [[$r]]])
  | `($_ $l $r) => `([qsl| [[$l]] ⊔ [[$r]]])
  | _ => throw ()

@[app_unexpander qslSup]
def unexpandQslSup : Unexpander
  | `($_ fun $x:ident => [qsl| S $y:ident $[$z:ident]*. $f]) =>
    `([qsl| S $x:ident $y:ident $[$z:ident]*. $f])
  | `($_ fun $x:ident => [qsl|$f:qsl]) => `([qsl| S $x:ident. $f])
  | _ => throw ()

@[app_unexpander qslInf]
def unexpandQslInf : Unexpander
  | `($_ fun $x:ident => [qsl| I $y:ident $[$z:ident]*. $f]) =>
    `([qsl| I $x:ident $y:ident $[$z:ident]*. $f])
  | `($_ fun $x:ident => [qsl|$f:qsl]) => `([qsl| I $x:ident. $f])
  | _ => throw ()

@[app_unexpander qslSepMul]
def unexpandQslSepMul : Unexpander
  | `($_ [qsl|$l] [qsl|$r]) => `([qsl| $l ⋆ $r])
  | `($_ $l [qsl|$r]) => `([qsl| [[$l]] ⋆ $r])
  | `($_ [qsl|$l] $r) => `([qsl| $l ⋆ [[$r]]])
  | `($_ $l $r) => `([qsl| [[$l]] ⋆ [[$r]]])
  | _ => throw ()

@[app_unexpander qslSepDiv]
def unexpandQslSepDiv : Unexpander
  | `($_ [qsl|$l1 -⋆ $l2] [qsl|$r]) => `([qsl| ($l1 -⋆ $l2) -⋆ $r])
  | `($_ [qsl|$l1 -⋆ $l2] $r) => `([qsl| ($l1 -⋆ $l2) -⋆ [[$r]]])
  | `($_ [qsl|$l] [qsl|$r]) => `([qsl| $l -⋆ $r])
  | `($_ $l [qsl|$r]) => `([qsl| [[$l]] -⋆ $r])
  | `($_ [qsl|$l] $r) => `([qsl| $l -⋆ [[$r]]])
  | `($_ $l $r) => `([qsl| [[$l]] -⋆ [[$r]]])
  | _ => throw ()

@[app_unexpander qslEntailment]
def unexpandQslEntail : Unexpander
  | `($_ [qsl|$l] [qsl|$r]) => `([qsl| $l ⊢ $r])
  | _ => throw ()


example := [qsl Var| I (x:ℚ). ~ emp ⋆ emp ⊢ S (x:ℚ). emp -⋆ emp -⋆ emp]

end QSL
