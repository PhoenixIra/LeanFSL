import CQSL4.Program.Syntax
import CQSL4.Program.State
import CQSL4.Analysis.Probabilities

namespace Semantics

open unitInterval Syntax Program State

variable (Variable : Type)

noncomputable def smallStepProgramSemantics :
    (Program Variable) → (State Variable) →
    Nat → (Program Variable) → (State Variable) → I

  /- Skip always succeeds with the same state. -/
  | skip, s, 0, terminated, s' => conditionProbability (s = s')

  /- valAssign succeeds if the expression is well-defined and the resulting state has changed.
  valAssign fails if the expression is not well-defined and the state remains unchanged. -/
  | (valAssign v e), s, 0, terminated, s' =>
    conditionProbability (∃ val, (e s.stack) = some val ∧ substituteStack s v val = s')
  | (valAssign _ e), s, 0, error, s' =>
    conditionProbability (s = s' ∧ (e s.stack) = none)

  /- manipulate succeeds if the expressions are well-defined and an allocated location. It changes
  a heap position. manipulate fails if one expression is not well-defined or not an allocated location-/
  | (manipulate e_loc e_val), s, 0, terminated, s' =>
    conditionProbability (∃ l, e_loc s.stack = some l ∧ s.heap l ≠ none
      ∧ ∃ val, e_val s.stack = some val ∧ substituteHeap s l val = s')
  | (manipulate e_loc e_val), s, 0, error, s' =>
    conditionProbability (s = s' ∧ (e_loc s.stack = none
      ∨ (∃ l, e_loc s.stack = some l ∧ s.heap l = none)
      ∨ e_val s.stack = none))

  /- lookup succeeds if the expression is well-defined and an allocated location is looked up.
  It changes the stack according to the value in the heap. lookup fails if the expression is not
  well-defined or the location is not allocated.-/
  | (lookup v e), s, 0, terminated, s' =>
    conditionProbability (∃ l, e s.stack = some l
      ∧ ∃ val, s.heap l = some val ∧ substituteStack s v val = s' )
  | (lookup _ e), s, 0, error, s' =>
    conditionProbability (s = s' ∧ (e s.stack = none
      ∨ ∃ l, e s.stack = some l ∧ s.heap l = none))

  /- compareAndSet succeeds if all expressions are well-defined and the location is allocated.
    It changes the variable to 1 and sets the location to the new value if the value in the
    heap matches the compare value. It changes the variable to 0 if the value if the value in
    the heao does not match the compare value. -/
  | (compareAndSet v e_loc e_cmp e_val), s, 0, terminated, s' =>
    conditionProbability (∃ l, e_loc s.stack = some l
      ∧ ∃ cmp, e_cmp s.stack = some cmp ∧ ∃ new_val, e_val s.stack = some new_val
      ∧ ∃ old_val, s.heap l = some old_val
      ∧ ((old_val = cmp ∧ substituteStack (substituteHeap s l new_val) v 1 = s')
        ∨ old_val ≠ cmp ∧ substituteStack s v 0 = s'))
  | (compareAndSet _ e_loc e_cmp e_val), s, 0, error, s' =>
    conditionProbability (s = s' ∧ (e_loc s.stack = none
      ∨ e_cmp s.stack = none ∨ e_val s.stack = none
      ∨ ∃ l, e_loc s.stack = some l ∧ s.heap l = none))

  /- allocate succeeds if the location m and n spaces afterwards are allocated and sets the values
  to the default value 0. -/
  | (allocate v n), s, m, terminated, s' =>
    conditionProbability (isNotAlloc s m n ∧ substituteStack (substituteHeap s m n) v m = s')

  /- free succeeds if the expression is well-defined and the location is up to n positions allocated.
  free fails if an expression is not well-defined or some location between l and l+n is not allocated. -/
  | (free e n), s, 0, terminated, s' =>
    conditionProbability (∃ l, e s.stack = some l ∧ isAlloc s l n ∧ freeHeap s l n = s')
  | (free e n), s, 0, error, s' =>
    conditionProbability (s = s' ∧ (e s.stack = none ∨ ∃ l, e s.stack = some l ∧ ¬isAlloc s l n))

  /- sequential composition goes how the first program in C₁ goes -/
  | (sequential terminated C₂), s, a, C₂', s' => conditionProbability (s=s' ∧ C₂ = C₂')
  | (sequential C₁ C₂), s, a, (sequential C₁' C₂'), s' =>
    min (smallStepProgramSemantics C₁ s a C₁' s') (conditionProbability (C₂ = C₂'))

  /- probabilisticChoice succeeds if the expression is well-defined and picks one program with the given probability.
  probabilisticChoice fails if the expression is not well-defined. -/
  | (probabilisticChoice e C₁ C₂), s, 0, error, s' =>
    sorry
  | (probabilisticChoice e C₁ C₂), s, 0, C, s' =>
    sorry

  /- conditionalChoice succeeds if the expression is well-defined and picks the first if it is true and else the second.
  conditionalChoice fails if the epxression is not well-defined. -/
  | (conditionalChoice e C₁ C₂), s, 0, error, s' =>
    sorry
  | (conditionalChoice e C₁ C₂), s, 0, C, s' =>
    sorry

  /- loop ... -/

  /- All other combinations are ignored. -/
  | _, _, _, _, _ => 0

end Semantics
