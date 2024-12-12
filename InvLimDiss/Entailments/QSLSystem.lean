import InvLimDiss.SL.QuantitativeProofrules

namespace QSL

variable (Var : Type) (Symbols : Type) (Length : Symbols → ℕ)

inductive QSLFormula : Type
  | emp : QSLFormula
  | pointsTo (x y : Var) : QSLFormula
  | equals (x y : Var) : QSLFormula
  | disEquals (x y : Var) : QSLFormula
  | rat (r : Rat) : QSLFormula
  | max (f g : QSLFormula) : QSLFormula
  | add (f g : QSLFormula) : QSLFormula
  | mul (f g : QSLFormula) : QSLFormula
  | sup (f : Var → QSLFormula) : QSLFormula
  | sepmul (f g : QSLFormula) : QSLFormula
  | predicate (p : Symbols) (l : List Var) (h : l.length = Length p) : QSLFormula

inductive Sequent : Type
  | intro (f g : QSLFormula Var Symbols Length) : Sequent

namespace QSLFormula

open Lean

declare_syntax_cat qslf

syntax "emp" : qslf
syntax term " ↦ " term : qslf
syntax term:51 " = " term:51 : qslf
syntax term:51 " ≠ " term:51 : qslf
syntax "<" term:51 ">" : qslf
syntax:30 qslf:31 " ⊔ " qslf:30 : qslf
syntax:30 qslf:31 " + " qslf:30 : qslf
syntax:35 qslf:36 " ⬝ " qslf:35 : qslf
syntax:max "S " explicitBinders ". " qslf : qslf
syntax:35 qslf:36 " ⋆ " qslf:35 : qslf
syntax "("qslf")" : qslf

syntax "`[qslf| " qslf " ]" : term
syntax "`[qslf| " qslf " ⊢ " qslf " ]" : term

macro_rules
  | `(term| `[qslf| emp]) => `(QSLFormula.emp)
  | `(term| `[qslf| $l:term ↦ $r:term]) => `(QSLFormula.pointsTo $l $r)
  | `(term| `[qslf| $l:term = $r:term]) => `(QSLFormula.equals $l $r)
  | `(term| `[qslf| $l:term ≠ $r:term]) => `(QSLFormula.disEquals $l $r)
  | `(term| `[qslf| < $t:term >]) => `(QSLFormula.rat $t)
  | `(term| `[qslf| $l:qslf ⊔ $r:qslf]) => `(QSLFormula.max `[qslf|$l] `[qslf|$r])
  | `(term| `[qslf| $l:qslf + $r:qslf]) => `(QSLFormula.add `[qslf|$l] `[qslf|$r])
  | `(term| `[qslf| $l:qslf ⬝ $r:qslf]) => `(QSLFormula.mul `[qslf|$l] `[qslf|$r])
  | `(term| `[qslf| S $xs. $f:qslf]) => do expandExplicitBinders ``QSLFormula.sup xs (← `(`[qslf|$f]))
  | `(term| `[qslf| $l:qslf ⋆ $r:qslf]) => `(QSLFormula.sepmul `[qslf|$l] `[qslf|$r])
  | `(term| `[qslf| ($f:qslf)]) => `(`[qslf|$f])
  | `(term| `[qslf| $l:qslf ⊢ $r:qslf]) => `(Sequent.intro `[qslf|$l] `[qslf|$r])

open PrettyPrinter Delaborator

@[app_unexpander QSLFormula.emp]
def unexpandQslfEmp : Unexpander
  | `($_ ) => do `(`[qslf| emp])

@[app_unexpander QSLFormula.pointsTo]
def unexpandQslfPointsTo : Unexpander
  | `($_ $l $r) => `(`[qslf| $l:term ↦ $r:term])
  | _ => throw ()

@[app_unexpander QSLFormula.equals]
def unexpandQslfEquals : Unexpander
  | `($_ $l $r) => `(`[qslf| $l:term = $r:term])
  | _ => throw ()

@[app_unexpander QSLFormula.disEquals]
def unexpandQslfDisEquals : Unexpander
  | `($_ $l $r) => `(`[qslf| $l:term ≠ $r:term])
  | _ => throw ()

@[app_unexpander QSLFormula.rat]
def unexpandQslReal : Unexpander
  | `($_ $t) => `(`[qsl| < $t:term >])
  | _ => throw ()

@[app_unexpander QSLFormula.max]
def unexpandQslfMax : Unexpander
  | `($_ `[qslf| $l] `[qslf| $r]) => do `(`[qslf| $l:qslf ⊔ $r:qslf])
  | _ => throw ()

@[app_unexpander QSLFormula.add]
def unexpandQslfAdd : Unexpander
  | `($_ `[qslf| $l] `[qslf| $r]) => do `(`[qslf| $l:qslf + $r:qslf])
  | _ => throw ()

@[app_unexpander QSLFormula.mul]
def unexpandQslfMul : Unexpander
  | `($_ `[qslf| $l] `[qslf| $r]) => do `(`[qslf| $l:qslf ⬝ $r:qslf])
  | _ => throw ()

@[app_unexpander QSLFormula.sup]
def unexpandQslfSup : Unexpander
  | `($_ fun $x:ident => `[qslf| S $y:ident $[$z:ident]*. $f]) =>
    `(`[qslf| S $x:ident $y:ident $[$z:ident]*. $f])
  | `($_ fun $x:ident => `[qslf|$f:qsl]) => `(`[qslf| S $x:ident. $f])
  | _ => throw ()

@[app_unexpander QSLFormula.sepmul]
def unexpandQslfSepmul : Unexpander
  | `($_ `[qslf| $l] `[qslf| $r]) => do `(`[qslf| $l:qslf ⋆ $r:qslf])
  | _ => throw ()

@[app_unexpander Sequent]
def unexpandQslfSequent : Unexpander
  | `($_ `[qslf| $l] `[qslf| $r]) => do `(`[qslf| $l:qslf ⊢ $r:qslf])
  | _ => throw ()

@[category_parenthesizer qslf]
def qslf_parenthesizer : CategoryParenthesizer | prec => do
  Parenthesizer.maybeParenthesize `qslf false (fun stx => Unhygienic.run `(qslf|($(⟨stx⟩)))) prec $
    Parenthesizer.parenthesizeCategoryCore `qslf prec

def semanticsNonRec (q : QSLFormula Var Symbols Length)
    (predicate_semantics : (p : Symbols) → (l : List Var) → (l.length = Length p) → StateRVInf Var) :
    StateRVInf Var :=
  match q with
  | QSLFormula.emp => `[qsl| emp]
  | _ => sorry

end QSLFormula

end QSL
