import InvLimDiss.SL.QuantitativeProofrules
import InvLimDiss.Mathlib.FixedPoints

namespace QSL

variable (Var : Type) (Symbols : Type) (Length : Symbols → ℕ)

inductive QSLFormula : Type
  | emp' : QSLFormula
  | pointsTo (x y : Var) : QSLFormula
  | equals (x y : Var) : QSLFormula
  | disEquals (x y : Var) : QSLFormula
  | rat (r : NNRat) : QSLFormula
  | max (f g : QSLFormula) : QSLFormula
  | add (f g : QSLFormula) : QSLFormula
  | mul (f g : QSLFormula) : QSLFormula
  | sup (f : Var → QSLFormula) : QSLFormula
  | sepmul (f g : QSLFormula) : QSLFormula
  | predicate (p : Symbols) (l : {l : List Var | l.length = Length p}) : QSLFormula


variable {Var : Type} {Symbols : Type} {Length : Symbols → ℕ}

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
syntax "{" term:51 "}" term : qslf
syntax:30 qslf:31 " ⊔ " qslf:30 : qslf
syntax:30 qslf:31 " + " qslf:30 : qslf
syntax:35 qslf:36 " ⬝ " qslf:35 : qslf
syntax:max "S " explicitBinders ". " qslf : qslf
syntax:35 qslf:36 " ⋆ " qslf:35 : qslf
syntax "("qslf")" : qslf

syntax "`[qslf| " qslf " ]" : term
syntax "`[qslf| " qslf " ⊢ " qslf " ]" : term

macro_rules
  | `(term| `[qslf| emp]) => `(QSLFormula.emp')
  | `(term| `[qslf| $l:term ↦ $r:term]) => `(QSLFormula.pointsTo $l $r)
  | `(term| `[qslf| $l:term = $r:term]) => `(QSLFormula.equals $l $r)
  | `(term| `[qslf| $l:term ≠ $r:term]) => `(QSLFormula.disEquals $l $r)
  | `(term| `[qslf| < $t:term >]) => `(QSLFormula.rat $t)
  | `(term| `[qslf| { $t:term } $l:term]) => `(QSLFormula.predicate $t $l)
  | `(term| `[qslf| $l:qslf ⊔ $r:qslf]) => `(QSLFormula.max `[qslf|$l] `[qslf|$r])
  | `(term| `[qslf| $l:qslf + $r:qslf]) => `(QSLFormula.add `[qslf|$l] `[qslf|$r])
  | `(term| `[qslf| $l:qslf ⬝ $r:qslf]) => `(QSLFormula.mul `[qslf|$l] `[qslf|$r])
  | `(term| `[qslf| S $xs. $f:qslf]) => do expandExplicitBinders ``QSLFormula.sup xs (← `(`[qslf|$f]))
  | `(term| `[qslf| $l:qslf ⋆ $r:qslf]) => `(QSLFormula.sepmul `[qslf|$l] `[qslf|$r])
  | `(term| `[qslf| ($f:qslf)]) => `(`[qslf|$f])
  | `(term| `[qslf| $l:qslf ⊢ $r:qslf]) => `(Sequent.intro `[qslf|$l] `[qslf|$r])

open PrettyPrinter Delaborator

@[app_unexpander QSLFormula.emp']
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
def unexpandQslfRat : Unexpander
  | `($_ $t) => `(`[qslf| < $t:term >])
  | _ => throw ()

@[app_unexpander QSLFormula.predicate]
def unexpandQslfPredicate : Unexpander
  | `($_ $t $l) => `(`[qslf| { $t:term } $l])
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
  | `($_ fun $x:ident => `[qslf|$f:qslf]) => `(`[qslf| S $x:ident. $f])
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

noncomputable def semanticsNonRec (q : QSLFormula Var Symbols Length)
    (𝕏 : (p : Symbols) → {l : List Var | l.length = Length p} → StateRVInf Var) :
    StateRVInf Var :=
  match q with
  | QSLFormula.emp' => `[qsl| emp]
  | QSLFormula.pointsTo x y => `[qsl| x ↦ y]
  | QSLFormula.equals x y => `[qsl| x = y]
  | QSLFormula.disEquals x y => `[qsl| x ≠ y]
  | QSLFormula.rat r => `[qsl| <r>]
  | QSLFormula.max f g => `[qsl| [[semanticsNonRec f 𝕏]] ⊔ [[semanticsNonRec g 𝕏]]]
  | QSLFormula.add f g => `[qsl| [[semanticsNonRec f 𝕏]] + [[semanticsNonRec g 𝕏]]]
  | QSLFormula.mul f g => `[qsl| [[semanticsNonRec f 𝕏]] ⬝ [[semanticsNonRec g 𝕏]]]
  | QSLFormula.sup f => `[qsl| S x. [[semanticsNonRec (f x) 𝕏]]]
  | QSLFormula.sepmul f g => `[qsl| [[semanticsNonRec f 𝕏]] ⋆ [[semanticsNonRec g 𝕏]]]
  | QSLFormula.predicate p l => 𝕏 p l

open State in
noncomputable def substituteMultipleVar (s : Stack Var) (l₁ : List Var) (l₂ : List Var) :
    Stack Var :=
  match l₁, l₂ with
  | x::xs, y::ys => substituteMultipleVar (substituteVar s x (s y)) xs ys
  | _, _ => s

@[simp]
noncomputable def substitutesMultipleStack (s : State Var) (l₁ : List Var) (l₂ : List Var) :
    State Var := ⟨substituteMultipleVar s.stack l₁ l₂, s.heap⟩

noncomputable def predicate_chara
    (defs : Symbols → QSLFormula Var Symbols Length)
    (vars : (p : Symbols) → {l : List Var | l.length = Length p})
    (𝕏 : (p : Symbols) → {l : List Var | l.length = Length p} → StateRVInf Var)
    (p : Symbols) (l : {l : List Var | l.length = Length p}) : StateRVInf Var :=
  λ s => semanticsNonRec (defs p) 𝕏 (substitutesMultipleStack s (vars p) l)

theorem predicate_chara_mono
    (defs : Symbols → QSLFormula Var Symbols Length)
    (vars : (p : Symbols) → {l : List Var | l.length = Length p}) :
    Monotone (predicate_chara defs vars) := by
  intro 𝕏 𝕐 h p l s
  unfold predicate_chara
  simp only [substitutesMultipleStack, Set.mem_setOf_eq]
  induction (defs p) generalizing s
  <;> simp only [semanticsNonRec, le_refl]
  case max f g ih_f ih_g =>
    simp only [qslMax, Sup.sup,  max_le_iff]
    exact ⟨le_max_of_le_left <| ih_f s, le_max_of_le_right <| ih_g s⟩
  case add f g ih_f ih_g =>
    simp only [qslAdd]
    exact add_le_add (ih_f s) (ih_g s)
  case mul f g ih_f ih_g =>
    simp only [qslMul]
    exact ENNReal.ennreal_mul_le_mul (ih_f s) (ih_g s)
  case sup f ih_f =>
    simp only [qslSup]
    rw [iSup_apply, iSup_apply]
    apply iSup_mono
    intro x
    exact ih_f x s
  case sepmul f g ih_f ih_g =>
    simp only [qslSepMul, sSup_le_iff, Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro _ heap₁ heap₂ h_disjoint h_union rfl
    apply le_sSup_of_le
    use heap₁, heap₂, h_disjoint, h_union
    apply ENNReal.ennreal_mul_le_mul
    · exact ih_f ⟨_, heap₁⟩
    · exact ih_g ⟨_, heap₂⟩
  case predicate p' l' =>
    exact h _ _ _

noncomputable def predicate_chara_hom
    (defs : Symbols → QSLFormula Var Symbols Length)
    (vars : (p : Symbols) → {l : List Var | l.length = Length p}) :
    ((p : Symbols) → {l : List Var | l.length = Length p} → StateRVInf Var)
    →o (p : Symbols) → {l : List Var | l.length = Length p} → StateRVInf Var :=
  ⟨predicate_chara defs vars, predicate_chara_mono defs vars⟩

noncomputable def semantics
    (q : QSLFormula Var Symbols Length)
    (defs : Symbols → QSLFormula Var Symbols Length)
    (vars : (p : Symbols) → {l : List Var | l.length = Length p}) : StateRVInf Var :=
  q.semanticsNonRec (OrderHom.lfp <| predicate_chara_hom defs vars)







end QSLFormula

end QSL
