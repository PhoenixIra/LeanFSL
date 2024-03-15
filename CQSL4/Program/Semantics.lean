import CQSL4.Program.Syntax
import CQSL4.Program.State
import CQSL4.Analysis.Probabilities
import CQSL4.Util


namespace Semantics

open unitInterval Syntax Program State Classical

variable {Variable : Type}

inductive Action where
  | deterministic : Action
  | allocation : ℕ → Action
  | concurrencyLeft : Action → Action
  | concurrencyRight : Action → Action

/-- Skip always succeeds with the same state. -/
@[simp]
noncomputable def skipSmallStepSemantics :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a C s' => ite_one_zero (C=terminated ∧ a = Action.deterministic ∧ s = s')

/-- valAssign succeeds if the expression is well-defined and the resulting state has changed.
    valAssign fails if the expression is not well-defined and the state remains unchanged. -/
@[simp]
noncomputable def valAssignSmallStepSemantics (v : Variable) (e : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a C s' => match C with
  | terminated => ite_one_zero (a = Action.deterministic ∧
    ∃ val, (e s.stack) = some val ∧ s.stack v ≠ none ∧ substituteStack s v val = s')
  | error => ite_one_zero (a = Action.deterministic ∧ s = s'
    ∧ ((e s.stack) = none ∨ s.stack v = none))
  | _ => 0

/-- manipulate succeeds if the expressions are well-defined and an allocated location. It changes
    a heap position. manipulate fails if one expression is not well-defined or not an allocated location-/
@[simp]
noncomputable def manipulateSmallStepSemantics (e_loc e_val : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a C s' => match C with
  | terminated => ite_one_zero (a = Action.deterministic ∧
      ∃ l, e_loc s.stack = some l ∧ s.heap l ≠ none ∧
      ∃ val, e_val s.stack = some val ∧ substituteHeap s l val = s')
  | error =>ite_one_zero (a = Action.deterministic ∧ s = s'
      ∧ (e_loc s.stack = none
      ∨ (∃ l, e_loc s.stack = some l ∧ s.heap l = none)
      ∨ e_val s.stack = none))
  | _ => 0

/-- lookup succeeds if the expression is well-defined and an allocated location is looked up.
    It changes the stack according to the value in the heap. lookup fails if the expression is not
    well-defined or the location is not allocated.-/
@[simp]
noncomputable def lookupSmallStepSemantics (v : Variable) (e : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a C s' => match C with
  | terminated => ite_one_zero ( a = Action.deterministic ∧
      ∃ l, e s.stack = some l ∧ s.stack v ≠ none ∧
      ∃ val, s.heap l = some val ∧ substituteStack s v val = s' )
  | error => ite_one_zero ( a = Action.deterministic ∧ s = s'
      ∧ (e s.stack = none ∨ s.stack v = none
      ∨ ∃ l, e s.stack = some l ∧ s.heap l = none))
  | _ => 0

/-- compareAndSet succeeds if all expressions are well-defined and the location is allocated.
    It changes the variable to 1 and sets the location to the new value if the value in the
    heap matches the compare value. It changes the variable to 0 if the value if the value in
    the heao does not match the compare value. -/
@[simp]
noncomputable def compareAndSetSmallStepSemantics (v : Variable) (e_loc e_cmp e_val : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a C s' => match C with
  | terminated => ite_one_zero ( a = Action.deterministic ∧
      ∃ l, e_loc s.stack = some l ∧ ∃ cmp, e_cmp s.stack = some cmp
      ∧ ∃ new_val, e_val s.stack = some new_val
      ∧ ∃ old_val, s.heap l = some old_val ∧ s.stack v ≠ none
      ∧ ((old_val = cmp ∧ substituteStack (substituteHeap s l new_val) v 1 = s')
        ∨ old_val ≠ cmp ∧ substituteStack s v 0 = s'))
  | error => ite_one_zero (a = Action.deterministic ∧ s = s'
      ∧ (e_loc s.stack = none
      ∨ e_cmp s.stack = none ∨ e_val s.stack = none
      ∨ ∃ l, e_loc s.stack = some l ∧ s.heap l = none))
  | _ => 0

/-- allocate succeeds if the location m and n spaces afterwards are allocated and sets the values
    to the default value 0. -/
@[simp]
noncomputable def allocateSmallStepSemantics (v : Variable) (n : ℕ) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a C s' =>
    ite_one_zero (∃ m, a = Action.allocation m ∧ C = terminated ∧ isNotAlloc s m n
      ∧ substituteStack (substituteHeap s m n) v m = s')

/-- free succeeds if the expression is well-defined and the location is up to n positions allocated.
    free fails if an expression is not well-defined or some location between l and l+n is not allocated. -/
@[simp]
noncomputable def freeSmallStepSemantics (e : ValueExp Variable) (n : ℕ) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a C s' => match C with
  | terminated => ite_one_zero (a = Action.deterministic ∧
    ∃ l, e s.stack = some l ∧ isAlloc s l n ∧ freeHeap s l n = s')
  | error => ite_one_zero (a = Action.deterministic ∧ s = s'
    ∧ (e s.stack = none ∨ ∃ l, e s.stack = some l ∧ ¬isAlloc s l n))
  | _ => 0

/-- probabilisticChoice succeeds if the expression is well-defined and picks one program with the given probability.
    probabilisticChoice fails if the expression is not well-defined. -/
@[simp]
noncomputable def probabilisticChoiceSmallStepSemantics (e : ProbExp Variable) (C₁ C₂ : Program Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a C s' => match C with
  | error => ite_one_zero (a = Action.deterministic ∧ s = s' ∧ e s.stack = none)
  | C => if a = Action.deterministic ∧ s = s' then if let some i := e s.stack then
      if C₁ = C then i
      else if C₂ = C then
        σ i else 0
    else 0 else 0

/-- conditionalChoice succeeds if the expression is well-defined and picks the first if it is true and else the second.
    conditionalChoice fails if the epxression is not well-defined. -/
@[simp]
noncomputable def conditionalChoiceSmallStepSemantics (e : BoolExp Variable) (C₁ C₂ : Program Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a C s' => match C with
  | error => ite_one_zero (a = Action.deterministic ∧ s = s' ∧ e s.stack = none)
  | C => ite_one_zero (a = Action.deterministic ∧ s = s'
    ∧ (e s.stack = some true ∧ C₁ = C ∨ e s.stack = some false ∧ C₂ = C))

/-- loopy Program that succeeds with terminated program if the loop condition is false,
    loops one more if the loop condition is true and errors if an expression is not well-defined-/
@[simp]
noncomputable def loopSmallStepSemantics (e : BoolExp Variable) (C : Program Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a C' s' => match C' with
  | error => ite_one_zero (a = Action.deterministic ∧ s = s' ∧ e s.stack = none)
  | terminated => ite_one_zero (a = Action.deterministic ∧ s = s' ∧ e s.stack = some false)
  | C' => ite_one_zero (C' = sequential C (loop e C) ∧ s = s' ∧ e s.stack = some true )

noncomputable def programSmallStepSemantics :
    (Program Variable) → (State Variable) →
    Action → (Program Variable) → (State Variable) → I
  | error => 0
  | terminated => 0
  | skip => skipSmallStepSemantics
  | valAssign v e => valAssignSmallStepSemantics v e
  | manipulate e_loc e_val => manipulateSmallStepSemantics e_loc e_val
  | lookup v e => lookupSmallStepSemantics v e
  | compareAndSet v e_loc e_cmp e_val => compareAndSetSmallStepSemantics v e_loc e_cmp e_val
  | allocate v n => allocateSmallStepSemantics v n
  | free e n => freeSmallStepSemantics e n
  | probabilisticChoice e C₁ C₂ => probabilisticChoiceSmallStepSemantics e C₁ C₂
  | conditionalChoice e C₁ C₂ => conditionalChoiceSmallStepSemantics e C₁ C₂
  | loop e C => loopSmallStepSemantics e C
  | sequential terminated C₂ => fun s a C s' => ite_one_zero (a = Action.deterministic ∧ s=s' ∧ C = C₂)
  | sequential C₁ C₂ => fun s a C s' => match C with
    | sequential C₁' C₂' => if C₂ = C₂' then (programSmallStepSemantics C₁ s a C₁' s') else 0
    | _ => 0
  | concurrent terminated terminated => fun s a C s' => ite_one_zero (C = terminated ∧ a = Action.deterministic ∧ s = s')
  | concurrent C₁ C₂ => fun s a C s' => match C with
    | concurrent C₁' C₂' => match a with
      | Action.concurrencyLeft a => if C₂ = C₂' then programSmallStepSemantics C₁ s a C₁' s' else 0
      | Action.concurrencyRight a => if C₁ = C₁' then programSmallStepSemantics C₂ s a C₂' s' else 0
      | _ => 0
    | _ => 0



def enabledAction : (Program Variable) → (State Variable) → Set Action
  | terminated, _                   => ∅
  | error, _                        => ∅
  | skip, _                         => { Action.deterministic }
  | valAssign _ _, _                => { Action.deterministic }
  | manipulate _ _, _               => { Action.deterministic }
  | lookup _ _, _                   => { Action.deterministic }
  | compareAndSet _ _ _ _, _        => { Action.deterministic }
  | allocate _ n, s                 => { a | ∃ m, a = Action.allocation m ∧ isNotAlloc s m n }
  | free _ _, _                     => { Action.deterministic }
  | sequential C₁ _, s              => if C₁ = terminated then { Action.deterministic } else enabledAction C₁ s
  | probabilisticChoice _ _ _, _    => { Action.deterministic }
  | conditionalChoice _ _ _, _      => { Action.deterministic }
  | loop _ _, _                     => { Action.deterministic }
  | concurrent C₁ C₂, s             => { Action.concurrencyLeft a  | a ∈ enabledAction C₁ s }
                                     ∪ { Action.concurrencyRight a | a ∈ enabledAction C₂ s }



theorem zero_probability_of_not_enabledAction (a : Action) (h : ¬ a ∈ enabledAction C s):
    ∀ C', ∀ s', programSmallStepSemantics C s a C' s' = 0 := by
  intro C' s'
  unfold programSmallStepSemantics
  split
  -- terminated
  · simp only [Pi.zero_apply]
  -- error
  · simp only [Pi.zero_apply]
  -- allocation
  pick_goal 6
  · unfold allocateSmallStepSemantics
    rw[ite_one_zero_neg]
    simp only [not_exists, not_and]
    intro n h_a h_terminating h_not_alloc



  --   rw[ite_one_zero_neg]
  --   simp only [not_and_or]
  --   exact Or.inr <| Or.inl h
  -- }
  -- · {

  --   simp only [skipSmallStepSemantics, valAssignSmallStepSemantics, manipulateSmallStepSemantics,
  --     lookupSmallStepSemantics, compareAndSetSmallStepSemantics, allocateSmallStepSemantics,
  --     freeSmallStepSemantics, probabilisticChoiceSmallStepSemantics, conditionalChoiceSmallStepSemantics,
  --     loopSmallStepSemantics]
  --   rw[ite_one_zero_neg]
  --   simp only [not_and_or]
  --   exact Or.inr <| Or.inl h
  -- }
  -- | valAssign _ _ => {
  --   rw[enabledAction, Set.mem_singleton_iff] at h
  --   unfold programSmallStepSemantics valAssignSmallStepSemantics
  --   split
  --   · rw[ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h
  --   · rw[ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h
  --   · rfl
  -- }
  -- | manipulate _ _ => {
  --   rw[enabledAction, Set.mem_singleton_iff] at h
  --   unfold programSmallStepSemantics manipulateSmallStepSemantics
  --   split
  --   · rw[ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h
  --   · rw[ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h
  --   · rfl
  -- | lookup _ _ => {
  --   rw[enabledAction, Set.mem_singleton_iff] at h
  --   unfold programSmallStepSemantics manipulateSmallStepSemantics
  --   split
  --   · rw[ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h
  --   · rw[ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h
  --   · rfl
  -- }

  -- }
  -- | _ => sorry


end Semantics
