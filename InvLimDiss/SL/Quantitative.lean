import InvLimDiss.Program.State
import InvLimDiss.Program.Expressions
import InvLimDiss.SL.Entailment
import InvLimDiss.Analysis.Probabilities

/-
This file contains definitions and lemmas about unit valued quantitative separation logic
-/

namespace QSL

open State unitInterval Syntax

def StateRV (Var : Type) : Type := State Var → I

noncomputable instance {Var : Type} : CompleteLattice (StateRV Var) := Pi.instCompleteLattice

instance : Entailment (StateRV Var) := ⟨fun P Q => P ≤ Q⟩

variable {Var : Type}

noncomputable def qslTrue : StateRV Var := λ _ => 1

noncomputable def qslFalse : StateRV Var := λ _ => 0

noncomputable def qslEmp : StateRV Var := λ ⟨_,h⟩ => iteOneZero (h = ∅)

noncomputable def qslPointsTo (loc val : ValueExp Var) : StateRV Var :=
    λ s => iteOneZero (∃ n : ℕ+, n = loc s.stack ∧ s.heap n = HeapValue.val (val s.stack))

noncomputable def qslEquals (e e' : ValueExp Var) : StateRV Var :=
    λ s => iteOneZero (e s.stack = e' s.stack)

noncomputable def qslReal (e : ProbExp Var) : StateRV Var := λ ⟨s,_⟩ => e s

noncomputable def qslIverson (P : State Var → Prop) : StateRV Var := λ s => iteOneZero (P s)

noncomputable def qslSubst (P : StateRV Var) (v : Var) (e : ValueExp Var) : StateRV Var :=
  fun s => P (s.substituteStack v (e s.stack))

noncomputable def qslNot (P : StateRV Var) : StateRV Var := λ s => σ (P s)

noncomputable def qslMin (P Q : StateRV Var) : StateRV Var := P ⊓ Q

noncomputable def qslMax (P Q : StateRV Var) : StateRV Var := P ⊔ Q

noncomputable def qslAdd (P Q : StateRV Var) : StateRV Var := λ s => truncatedAdd (P s) (Q s)

noncomputable def qslMul (P Q : StateRV Var) : StateRV Var := λ s => P s * Q s

noncomputable def qslSup {α : Type} (P : α → StateRV Var) : StateRV Var := sSup {P x | x : α}

noncomputable def qslInf {α : Type} (P : α → StateRV Var) : StateRV Var := sInf {P x | x : α}

noncomputable def qslSepMul (P Q : StateRV Var) : StateRV Var :=
  fun s => sSup { x | ∃ h₁ h₂, disjoint h₁ h₂ ∧ h₁ ∪ h₂ = s.heap ∧ x = P ⟨s.stack, h₁⟩ * Q ⟨s.stack, h₂⟩}

noncomputable def qslBigSepMul (n : Nat) (P : ℕ → StateRV Var) : StateRV Var :=
  match n with
  | 0 => (P 0)
  | n+1 => qslSepMul (P (n+1)) (qslBigSepMul n P)

noncomputable def qslSepDiv (P Q : StateRV Var) : StateRV Var :=
  fun s => sInf { x | ∃ h', disjoint s.heap h' ∧ x = Q ⟨s.stack,s.heap ∪ h'⟩ / P ⟨s.stack,h'⟩ }

open Lean

declare_syntax_cat qsl

syntax "qTrue" : qsl
syntax "qFalse" : qsl
syntax "emp" : qsl
syntax term " ↦ " term : qsl
syntax term:51 " = " term:51 : qsl
syntax "<" term:51 ">" : qsl
syntax "[[" term "]]" : qsl
syntax "⁅" term "⁆" : qsl
syntax qsl:min "[ " term " ↦ " term " ]" : qsl
syntax "~" qsl:min : qsl
syntax:35 qsl:36 " ⊓ " qsl:35 : qsl
syntax:30 qsl:31 " ⊔ " qsl:30 : qsl
syntax:30 qsl:31 " + " qsl:30 : qsl
syntax:35 qsl:36 " · " qsl:35 : qsl
syntax:max "S " explicitBinders ". " qsl : qsl
syntax:max "I " explicitBinders ". " qsl : qsl
syntax:35 qsl:36 " ⋆ " qsl:35 : qsl
syntax:36 "[⋆] " binderIdent "∈ {0 ... "term" }. " qsl:36 : qsl
syntax:25 qsl:26 " -⋆ " qsl:25 : qsl
syntax "("qsl")" : qsl

syntax "`[qsl| " qsl " ]" : term
syntax "`[qsl| " qsl " ⊢ " qsl " ]" : term

syntax "`[qsl " term " | " qsl " ]" : term
syntax "`[qsl " term " | " qsl " ⊢ " qsl " ]" : term

macro_rules
  | `(term| `[qsl| qTrue]) => `(qslTrue)
  | `(term| `[qsl| qFalse]) => `(qslFalse)
  | `(term| `[qsl| emp]) => `(qslEmp)
  | `(term| `[qsl| $l:term ↦ $r:term]) => `(qslPointsTo $l $r)
  | `(term| `[qsl| $l:term = $r:term]) => `(qslEquals $l $r)
  | `(term| `[qsl| [[$t:term]]]) => `($t)
  | `(term| `[qsl| < $t:term >]) => `(qslReal $t)
  | `(term| `[qsl| ⁅$t:term⁆]) => `(qslIverson $t)
  | `(term| `[qsl| $f[ $x:term ↦ $e ] ]) => `(qslSubst `[qsl|$f] $x $e)
  | `(term| `[qsl| ~ $f:qsl]) => `(qslNot `[qsl|$f])
  | `(term| `[qsl| $l:qsl ⊓ $r:qsl]) => `(qslMin `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| $l:qsl ⊔ $r:qsl]) => `(qslMax `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| $l:qsl + $r:qsl]) => `(qslAdd `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| $l:qsl · $r:qsl]) => `(qslMul `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| S $xs. $f:qsl]) => do expandExplicitBinders ``qslSup xs (← `(`[qsl|$f]))
  | `(term| `[qsl| I $xs. $f:qsl]) => do expandExplicitBinders ``qslInf xs (← `(`[qsl|$f]))
  | `(term| `[qsl| $l:qsl ⋆ $r:qsl]) => `(qslSepMul `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| [⋆] $x:ident ∈ {0 ... $m}. $f:qsl]) =>
      `(qslBigSepMul $m (fun $x ↦ `[qsl| $f]))
  | `(term| `[qsl| [⋆] $_:hole ∈ {0 ... $m}. $f:qsl]) =>
      `(qslBigSepMul $m (fun _ ↦ `[qsl| $f]))
  | `(term| `[qsl| $l:qsl -⋆ $r:qsl]) => `(qslSepDiv `[qsl|$l] `[qsl|$r])
  | `(term| `[qsl| ($f:qsl)]) => `(`[qsl|$f])
  | `(term| `[qsl| $l:qsl ⊢ $r:qsl]) => `(`[qsl|$l] ≤ `[qsl|$r])

  | `(term| `[qsl $v:term | qTrue]) => `(@qslTrue $v)
  | `(term| `[qsl $v:term | qFalse]) => `(@qslFalse $v)
  | `(term| `[qsl $v:term| emp]) => `(@qslEmp $v)
  | `(term| `[qsl $v:term| $l:term ↦ $r:term]) => `(@qslPointsTo $v $l $r)
  | `(term| `[qsl $v:term| $l:term = $r:term]) => `(@qslEquals $v $l $r)
  | `(term| `[qsl $_| [[$t:term]]]) => `($t)
  | `(term| `[qsl $v:term| <$t:term>]) => `(@qslReal $v $t)
  | `(term| `[qsl $v:term| ⁅$t:term⁆]) => `(@qslIverson $v $t)
  | `(term| `[qsl $v:term| $f[ $x:term ↦ $e ] ]) => `(@qslSubst $v `[qsl $v|$f] $x $e)
  | `(term| `[qsl $v:term| ~ $f:qsl]) => `(qslNot `[qsl $v|$f])
  | `(term| `[qsl $v:term| $l:qsl ⊓ $r:qsl]) => `(qslMin `[qsl $v|$l] `[qsl $v|$r])
  | `(term| `[qsl $v:term| $l:qsl ⊔ $r:qsl]) => `(qslMax `[qsl $v|$l] `[qsl $v|$r])
  | `(term| `[qsl $v:term| $l:qsl + $r:qsl]) => `(qslAdd `[qsl $v|$l] `[qsl $v|$r])
  | `(term| `[qsl $v:term| $l:qsl · $r:qsl]) => `(qslMul `[qsl $v|$l] `[qsl $v|$r])
  | `(term| `[qsl $v:term| S $xs. $f:qsl]) => do expandExplicitBinders ``qslSup xs (← `(`[qsl $v|$f]))
  | `(term| `[qsl $v:term| I $xs. $f:qsl]) => do expandExplicitBinders ``qslInf xs (← `(`[qsl $v|$f]))
  | `(term| `[qsl $v:term| $l:qsl ⋆ $r:qsl]) => `(qslSepMul `[qsl $v|$l] `[qsl $v|$r])
  | `(term| `[qsl $v:term| [⋆] $x:ident ∈ {0 ... $m}. $f:qsl]) =>
      `(qslBigSepMul $m (fun $x ↦ `[qsl $v| $f]))
  | `(term| `[qsl $v:term| [⋆] $_:hole ∈ {0 ... $m}. $f:qsl]) =>
      `(qslBigSepMul $m (fun _ ↦ `[qsl $v| $f]))
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
  | `($_ $t) => `(`[qsl| ⁅$t:term⁆])
  | _ => throw ()

def isAtom : TSyntax `qsl → Bool
  | `(qsl| emp) => true
  | `(qsl| $_:term ↦ $_:term) => true
  | `(qsl| $_:term = $_:term) => true
  | `(qsl| <$_:term>) => true
  | `(qsl| ⁅$_:term⁆) => true
  | `(qsl| ~$_:qsl) => true
  | `(qsl| $_:qsl[ $_ ↦ $_]) => true
  | `(qsl| $_ ) => false

@[app_unexpander qslNot]
def unexpandQslNot : Unexpander
  | `($_ `[qsl|$t]) =>
    if isAtom t then `(`[qsl| ~ $t]) else `(`[qsl| ~ ($t)])
  | `($_ $t) => `(`[qsl| ~ [[$t]]])
  | _ => throw ()

@[app_unexpander qslSubst]
def unexpandQslSubst : Unexpander
  | `($_ `[qsl|$f] $v:term $e:term) =>
    if isAtom f then `(`[qsl| $f[ $v ↦ $e] ]) else `(`[qsl| ($f) [ $v:term ↦ $e:term] ])
  | `($_ $f $v $e) => `(`[qsl| [[$f]][ $v ↦ $e] ])
  | _ => throw ()

def requireBracketsMin : TSyntax `qsl → Bool
  | `(qsl| ~ $_:qsl) => false
  | `(qsl| $_:qsl ⋆ $_:qsl) => false
  | `(qsl| $_:qsl ⊓ $_:qsl) => false
  | `(qsl| $_:qsl · $_:qsl) => false
  | `(qsl| [⋆] $_ ∈ {0 ... $_}. $_) => false
  | `(qsl| $f:qsl) => !isAtom f

def bracketsMin [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => if requireBracketsMin f then `(qsl| ( $f ) ) else `(qsl| $f )
  | `(term| $t:term) => `(qsl|[[$t]])

@[app_unexpander qslMin]
def unexpandQslMin : Unexpander
  | `($_ $l $r) => do `(`[qsl| $(← bracketsMin l) ⊓ $(← bracketsMin r)])
  | _ => throw ()

def requireBracketsMax : TSyntax `qsl → Bool
  | `(qsl| ~ $_:qsl) => false
  | `(qsl| $f:qsl) => !isAtom f

def bracketsMax [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => if requireBracketsMax f then `(qsl| ( $f ) ) else `(qsl| $f )
  | `(term| $t:term) => `(qsl|[[$t]])

@[app_unexpander qslMax]
def unexpandQslMax : Unexpander
  | `($_ $l $r) => do `(`[qsl| $(← bracketsMax l) ⊔ $(← bracketsMax r)])
  | _ => throw ()

@[app_unexpander qslAdd]
def unexpandQslAdd : Unexpander
  | `($_ $l $r) => do `(`[qsl| $(← bracketsMax l) + $(← bracketsMax r)])
  | _ => throw ()

@[app_unexpander qslMul]
def unexpandQslMul : Unexpander
  | `($_ $l $r) => do `(`[qsl| $(← bracketsMin l) · $(← bracketsMin r)])
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
  | `($_ $l $r) => do `(`[qsl| $(← bracketsMin l) ⋆ $(← bracketsMin r)])
  | _ => throw ()

@[app_unexpander qslBigSepMul]
def unexpandBigSepCon : Unexpander
  | `($_ $n fun $x:ident => $f) => do
      `(`[qsl| [⋆] $x:ident ∈ {0 ... $n}. $(← bracketsMin f)])
  | _ => throw ()

def requireBracketsSepDiv : TSyntax `qsl → Bool
  | `(qsl| ~ $_:qsl) => false
  | `(qsl| $_:qsl -⋆ $_:qsl) => false
  | `(qsl| $_:qsl ⊓ $_:qsl) => false
  | `(qsl| $_:qsl ⋆ $_:qsl) => false
  | `(qsl| $_:qsl · $_:qsl) => false
  | `(qsl| $_:qsl ⊔ $_:qsl) => false
  | `(qsl| $_:qsl + $_:qsl) => false
  | `(qsl| $f:qsl) => !isAtom f

def bracketsSepDiv [Monad m] [MonadRef m] [MonadQuotation m]: TSyntax `term → m (TSyntax `qsl)
  | `(term| `[qsl|$f:qsl]) => if requireBracketsSepDiv f then `(qsl| ( $f ) ) else `(qsl| $f )
  | `(term| $t:term) => `(qsl|[[$t]])

@[app_unexpander qslSepDiv]
def unexpandQslSepDiv : Unexpander
  | `($_ `[qsl|$l -⋆ $r] $f) => do `(`[qsl| ($l -⋆ $r) -⋆ $(← bracketsSepDiv f)])
  | `($_ $l $r) => do `(`[qsl| $(← bracketsSepDiv l) -⋆ $(← bracketsSepDiv r)])
  | _ => throw ()

-- @[app_unexpander LE.le]
-- def unexpandSlEntail : Unexpander
--   | `($_ `[qsl|$l:qsl] `[qsl|$r:qsl]) => do `(`[qsl| $l ⊢ $r])
--   | _ => throw ()


-- example : `[qsl Var| emp ⊔ I (x:ℚ). ~ (emp ⊔ (emp ⊔ emp) ⋆ emp) ⊢ (S (x:ℚ). emp -⋆ emp + emp -⋆ emp) ⊓ emp] := sorry


example : `[qsl Var| qFalse ⊢ (emp ⋆ emp)[x ↦ e] ] := sorry

end QSL
