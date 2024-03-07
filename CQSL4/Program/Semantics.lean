import CQSL4.Program.Syntax
import CQSL4.Program.State
import CQSL4.Analysis.Probabilities

namespace Semantics

open unitInterval Syntax Program State

variable (Variable : Type)

noncomputable def smallStepProgramSemantics :
    (Program Variable) → (State Variable) →
    Nat → (Program Variable) → (State Variable) → I

  | skip, _, 0, terminated, _ => 1

  | (valAssign v e), s, 0, terminated, s' =>
    conditionProbability (∃ val, (e s.stack) = some val ∧ substituteStack s v val = s')
  | (valAssign _ e), s, 0, error, _ =>
    conditionProbability ((e s.stack) = none)

  | (manipulate e_loc e_val), s, 0, terminated, s' =>
    conditionProbability (∃ l, e_loc s.stack = some l ∧ s.heap l ≠ none
      ∧ ∃ val, e_val s.stack = some val ∧ substituteHeap s l val = s')
  | (manipulate e_loc e_val), s, 0, error, _ =>
    conditionProbability (e_loc s.stack = none
      ∨ (∃ l, e_loc s.stack = some l ∧ s.heap l = none)
      ∨ e_val s.stack = none)

  | (lookup v e), s, 0, terminated, s' =>
    conditionProbability (∃ l, e s.stack = some l
      ∧ ∃ val, s.heap l = some val ∧ substituteStack s v val = s' )
  | (lookup _ e), s, 0, error, _ =>
    conditionProbability (e s.stack = none
      ∨ ∃ l, e s.stack = some l ∧ s.heap l = none)


  | _, _, _, _, _ => 0

end Semantics
