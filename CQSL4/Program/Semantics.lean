import CQSL4.Program.Syntax
import CQSL4.Program.State
import CQSL4.Analysis.Probabilities
import CQSL4.Util


namespace Semantics

open unitInterval Syntax Program State Classical

variable {Variable : Type}

noncomputable def smallStepProgramSemantics :
    (Program Variable) → (State Variable) →
    Nat → (Program Variable) → (State Variable) → I

  /- Skip always succeeds with the same state. -/
  | skip, s, 0, terminated, s' => conditionOneProbability (s = s')

  /- valAssign succeeds if the expression is well-defined and the resulting state has changed.
  valAssign fails if the expression is not well-defined and the state remains unchanged. -/
  | (valAssign v e), s, 0, terminated, s' =>
    conditionOneProbability (∃ val, (e s.stack) = some val ∧ s.stack v ≠ none ∧ substituteStack s v val = s')
  | (valAssign v e), s, 0, error, s' =>
    conditionOneProbability (s = s' ∧ ((e s.stack) = none ∨ s.stack v = none))

  /- manipulate succeeds if the expressions are well-defined and an allocated location. It changes
  a heap position. manipulate fails if one expression is not well-defined or not an allocated location-/
  | (manipulate e_loc e_val), s, 0, terminated, s' =>
    conditionOneProbability (∃ l, e_loc s.stack = some l ∧ s.heap l ≠ none ∧
      ∃ val, e_val s.stack = some val ∧ substituteHeap s l val = s')
  | (manipulate e_loc e_val), s, 0, error, s' =>
    conditionOneProbability (s = s' ∧ (e_loc s.stack = none
      ∨ (∃ l, e_loc s.stack = some l ∧ s.heap l = none)
      ∨ e_val s.stack = none))

  /- lookup succeeds if the expression is well-defined and an allocated location is looked up.
  It changes the stack according to the value in the heap. lookup fails if the expression is not
  well-defined or the location is not allocated.-/
  | (lookup v e), s, 0, terminated, s' =>
    conditionOneProbability (∃ l, e s.stack = some l ∧ s.stack v ≠ none ∧
      ∃ val, s.heap l = some val ∧ substituteStack s v val = s' )
  | (lookup v e), s, 0, error, s' =>
    conditionOneProbability (s = s' ∧ (e s.stack = none ∨ s.stack v = none
      ∨ ∃ l, e s.stack = some l ∧ s.heap l = none))

  /- compareAndSet succeeds if all expressions are well-defined and the location is allocated.
    It changes the variable to 1 and sets the location to the new value if the value in the
    heap matches the compare value. It changes the variable to 0 if the value if the value in
    the heao does not match the compare value. -/
  | (compareAndSet v e_loc e_cmp e_val), s, 0, terminated, s' =>
    conditionOneProbability (∃ l, e_loc s.stack = some l
      ∧ ∃ cmp, e_cmp s.stack = some cmp ∧ ∃ new_val, e_val s.stack = some new_val
      ∧ ∃ old_val, s.heap l = some old_val ∧ s.stack v ≠ none
      ∧ ((old_val = cmp ∧ substituteStack (substituteHeap s l new_val) v 1 = s')
        ∨ old_val ≠ cmp ∧ substituteStack s v 0 = s'))
  | (compareAndSet _ e_loc e_cmp e_val), s, 0, error, s' =>
    conditionOneProbability (s = s' ∧ (e_loc s.stack = none
      ∨ e_cmp s.stack = none ∨ e_val s.stack = none
      ∨ ∃ l, e_loc s.stack = some l ∧ s.heap l = none))

  /- allocate succeeds if the location m and n spaces afterwards are allocated and sets the values
  to the default value 0. -/
  | (allocate v n), s, m, terminated, s' =>
    conditionOneProbability (isNotAlloc s m n ∧ substituteStack (substituteHeap s m n) v m = s')

  /- free succeeds if the expression is well-defined and the location is up to n positions allocated.
  free fails if an expression is not well-defined or some location between l and l+n is not allocated. -/
  | (free e n), s, 0, terminated, s' =>
    conditionOneProbability (∃ l, e s.stack = some l ∧ isAlloc s l n ∧ freeHeap s l n = s')
  | (free e n), s, 0, error, s' =>
    conditionOneProbability (s = s' ∧ (e s.stack = none ∨ ∃ l, e s.stack = some l ∧ ¬isAlloc s l n))

  /- sequential composition goes how the first program in C₁ goes -/
  | (sequential terminated C₂), s, 0, C₂', s' => conditionOneProbability (s=s' ∧ C₂ = C₂')
  | (sequential C₁ C₂), s, a, (sequential C₁' C₂'), s' =>
    conditionProbability (C₂ = C₂') (smallStepProgramSemantics C₁ s a C₁' s') 0

  /- probabilisticChoice succeeds if the expression is well-defined and picks one program with the given probability.
  probabilisticChoice fails if the expression is not well-defined. -/
  | (probabilisticChoice e _ _), s, 0, error, s' =>
    if e s.stack = none ∧ s = s' then 1 else 0
  | (probabilisticChoice e C₁ C₂), s, 0, C, s' =>
    if let some i := e s.stack then if C₁ = C ∧ s = s' then i else if C₂ = C ∧ s = s' then σ i else 0 else 0

  /- conditionalChoice succeeds if the expression is well-defined and picks the first if it is true and else the second.
  conditionalChoice fails if the epxression is not well-defined. -/
  | (conditionalChoice e _ _), s, 0, error, s' =>
    conditionOneProbability (e s.stack = none ∧ s = s')
  | (conditionalChoice e C₁ C₂), s, 0, C, s' =>
    conditionOneProbability (s = s' ∧ (e s.stack = some true ∧ C₁ = C ∨ e s.stack = some false ∧ C₂ = C))

  /- loop ... -/
  | (loop e _), s, 0, error, s' =>
    conditionOneProbability (e s.stack = none ∧ s = s')
  | (loop e _), s, 0, terminated, s' =>
    conditionOneProbability (e s.stack = some false ∧ s = s')
  | (loop e C), s, 0, C', s' =>
    conditionOneProbability (e s.stack = some true ∧ C' = sequential C (loop e C) ∧ s = s')

  /- All other combinations are ignored. -/
  | _, _, _, _, _ => 0


lemma smallstep_terminated : smallStepProgramSemantics terminated s a C s' = 0 := by
  unfold smallStepProgramSemantics



def enabledAction : (Program Variable) → (State Variable) → Set ℕ
  | terminated, _                   => ∅
  | error, _                        => ∅
  | skip, _                         => {0}
  | valAssign _ _, _                => {0}
  | manipulate _ _, _               => {0}
  | lookup _ _, _                   => {0}
  | compareAndSet _ _ _ _, _        => {0}
  | allocate _ n, s                 => { m | isNotAlloc s m n}
  | free _ _, _                     => {0}
  | sequential C₁ _, s              => if C₁ = terminated then {0} else enabledAction C₁ s
  | probabilisticChoice _ _ _, _    => {0}
  | conditionalChoice _ _ _, _      => {0}
  | loop _ _, _                     => {0}

theorem zero_probability_of_not_enabledAction (a : ℕ) (h : ¬ a ∈ enabledAction C s):
    ∀ C', ∀ s', smallStepProgramSemantics C s a C' s' = 0 := by
  intro C' s'
  sorry


end Semantics
