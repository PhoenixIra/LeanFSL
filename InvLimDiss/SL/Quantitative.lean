import InvLimDiss.Program.State
import InvLimDiss.Program.Expressions
import InvLimDiss.Analysis.Probabilities

/-
This file contains definitions and lemmas about unit valued quantitative separation logic
-/

namespace QSL

open State unitInterval Syntax

variable (Var : Type)

def StateRV := State Var → I

noncomputable def qslEmp : StateRV Var := λ ⟨_,h⟩ => iteOneZero (h = empty_heap)

noncomputable def qslPointsTo (loc : ValueExp Var) (val : ValueExp Var) : StateRV Var :=
    λ ⟨s,h⟩ => iteOneZero (∃ n : ℕ, n = loc s ∧ h n = some (val s))

noncomputable def qslEqual (x y : Var) : StateRV Var :=
    λ ⟨s,_⟩ => iteOneZero (s x = s y)

noncomputable def qslPure (P : Prop) : StateRV Var := λ _ => iteOneZero P

noncomputable def qslNot (P : StateRV Var) : StateRV Var := λ s => σ (P s)

noncomputable def qslMin (P Q : StateRV Var) : StateRV Var := λ s => min (P s) (Q s)

noncomputable def qslMax (P Q : StateRV Var) : StateRV Var := λ s => max (P s) (Q s)

noncomputable def qslSup {α : Type} (P : α → StateRV Var) : StateRV Var := λ s => sSup {P x s | x : α}

noncomputable def qslAll {α : Type} (P : α → StateRV Var) : StateRV Var := λ s => sInf {P x s | x : α}

noncomputable def qslSepCon (P Q : StateRV Var) : StateRV Var :=
  λ ⟨s,h⟩ => sSup { x | ∃ h₁ h₂, disjoint h₁ h₂ ∧ h₁ ∪ h₂ = h ∧ x = P ⟨s, h₁⟩ * Q ⟨s, h₂⟩}

noncomputable def qslSepImp (P Q : StateRV Var) : StateRV Var :=
  λ ⟨s,h⟩ => sInf { x | ∃ h', disjoint h h' ∧ x = Q ⟨s,(h ∪ h')⟩ / P ⟨s,h'⟩ }

end QSL
