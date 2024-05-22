import InvLimDiss.Program.State
import InvLimDiss.Program.Expressions

/-
This file contains definitions and lemmas about classical (i.e. Prop) separation logic
-/

namespace SL

open State Syntax

variable (Var : Type)

def StateProp := State Var → Prop

def slEmp : StateProp Var := λ ⟨_,h⟩ => h = empty_heap

def slPointsTo (loc : ValueExp Var) (val : ValueExp Var) : StateProp Var :=
    λ ⟨s,h⟩ => ∃ n : ℕ, n = (loc s) ∧ h n = some (val s)

def slEqual (x y : Var) : StateProp Var := λ ⟨s,_⟩ => s x = s y

def slPure (P : Prop) : StateProp Var := λ _ => P

def slNot (P : StateProp Var) : StateProp Var := λ s => ¬ P s

def slAnd (P Q : StateProp Var) : StateProp Var := λ s => P s ∧ Q s

def slOr (P Q : StateProp Var) : StateProp Var := λ s => P s ∨ Q s

def slExists {α : Type} (P : α → StateProp Var) : StateProp Var := λ s => ∃ x : α, P x s

def slAll {α : Type} (P : α → StateProp Var) : StateProp Var := λ s => ∀ x : α, P x s

def slSepCon (P Q : StateProp Var) : StateProp Var :=
  λ ⟨s,h⟩ => ∃ h₁ h₂, P ⟨s, h₁⟩ ∧ Q ⟨s, h₂⟩ ∧ disjoint h₁ h₂ ∧ h₁ ∪ h₂ = h

def slSepImp (P Q : StateProp Var) : StateProp Var :=
  λ ⟨s,h⟩ => ∀ h', P ⟨s,h'⟩ → disjoint h h' → Q ⟨s,(h ∪ h')⟩

end SL
