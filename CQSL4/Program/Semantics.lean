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
  fun s a c s' => ite_one_zero (c = terminated ∧ a = Action.deterministic ∧ s = s')

/-- valAssign succeeds if the expression is well-defined and the resulting state has changed.
    valAssign fails if the expression is not well-defined and the state remains unchanged. -/
@[simp]
noncomputable def valAssignSmallStepSemantics (v : Variable) (e : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
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
  fun s a c s' => match c with
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
  fun s a c s' => match c with
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
  fun s a c s' => match c with
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
  fun s a c s' =>
    ite_one_zero (∃ m, a = Action.allocation m ∧ c = terminated ∧ isNotAlloc s m n
      ∧ substituteStack (substituteHeap s m n) v m = s')

/-- free succeeds if the expression is well-defined and the location is up to n positions allocated.
    free fails if an expression is not well-defined or some location between l and l+n is not allocated. -/
@[simp]
noncomputable def freeSmallStepSemantics (e : ValueExp Variable) (n : ℕ) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | terminated => ite_one_zero (a = Action.deterministic ∧
    ∃ l, e s.stack = some l ∧ isAlloc s l n ∧ freeHeap s l n = s')
  | error => ite_one_zero (a = Action.deterministic ∧ s = s'
    ∧ (e s.stack = none ∨ ∃ l, e s.stack = some l ∧ ¬isAlloc s l n))
  | _ => 0

/-- probabilisticChoice succeeds if the expression is well-defined and picks one program with the given probability.
    probabilisticChoice fails if the expression is not well-defined. -/
@[simp]
noncomputable def probabilisticChoiceSmallStepSemantics (e : ProbExp Variable) (c₁ c₂ : Program Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | error => ite_one_zero (a = Action.deterministic ∧ s = s' ∧ e s.stack = none)
  | c => if a = Action.deterministic ∧ s = s' then if let some i := e s.stack then
      if c₁ = c then i
      else if c₂ = c then
        σ i else 0
    else 0 else 0

/-- conditionalChoice succeeds if the expression is well-defined and picks the first if it is true and else the second.
    conditionalChoice fails if the epxression is not well-defined. -/
@[simp]
noncomputable def conditionalChoiceSmallStepSemantics (e : BoolExp Variable) (c₁ c₂ : Program Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | error => ite_one_zero (a = Action.deterministic ∧ s = s' ∧ e s.stack = none)
  | c => ite_one_zero (a = Action.deterministic ∧ s = s'
    ∧ (e s.stack = some true ∧ c₁ = c ∨ e s.stack = some false ∧ c₂ = c ))

/-- loopy Program that succeeds with terminated program if the loop condition is false,
    loops one more if the loop condition is true and errors if an expression is not well-defined-/
@[simp]
noncomputable def loopSmallStepSemantics (e : BoolExp Variable) (c : Program Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c' s' => match c' with
  | error => ite_one_zero (a = Action.deterministic ∧ s = s' ∧ e s.stack = none)
  | terminated => ite_one_zero (a = Action.deterministic ∧ s = s' ∧ e s.stack = some false)
  | c' => ite_one_zero (c' = sequential c (loop e c) ∧ s = s' ∧ e s.stack = some true )

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
  | probabilisticChoice e c₁ c₂ => probabilisticChoiceSmallStepSemantics e c₁ c₂
  | conditionalChoice e c₁ c₂ => conditionalChoiceSmallStepSemantics e c₁ c₂
  | loop e c => loopSmallStepSemantics e c
  | sequential terminated c₂ => fun s a c s' => ite_one_zero (a = Action.deterministic ∧ s=s' ∧ c = c₂)
  | sequential c₁ c₂ => fun s a c s' => match c with
    | sequential c₁' c₂' => if c₂ = c₂' then (programSmallStepSemantics c₁ s a c₁' s') else 0
    | _ => 0
  | concurrent terminated terminated => fun s a c s' => ite_one_zero (c = terminated ∧ a = Action.deterministic ∧ s = s')
  | concurrent c₁ c₂ => fun s a c s' => match c with
    | concurrent c₁' c₂' => match a with
      | Action.concurrencyLeft a => if c₂ = c₂' then programSmallStepSemantics c₁ s a c₁' s' else 0
      | Action.concurrencyRight a => if c₁ = c₁' then programSmallStepSemantics c₂ s a c₂' s' else 0
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
  | sequential c₁ _, s              => if c₁ = terminated then { Action.deterministic } else enabledAction c₁ s
  | probabilisticChoice _ _ _, _    => { Action.deterministic }
  | conditionalChoice _ _ _, _      => { Action.deterministic }
  | loop _ _, _                     => { Action.deterministic }
  | concurrent c₁ c₂, s             => { Action.concurrencyLeft a  | a ∈ enabledAction c₁ s }
                                     ∪ { Action.concurrencyRight a | a ∈ enabledAction c₂ s }



theorem zero_probability_of_not_enabledAction (a : Action) (h : ¬ a ∈ enabledAction c s):
    ∀ c', ∀ s', programSmallStepSemantics c s a c' s' = 0 := by
  intro c' s'

  -- split
  induction c with
  | terminated => unfold programSmallStepSemantics; simp only [Pi.zero_apply]
  | error => unfold programSmallStepSemantics; simp only [Pi.zero_apply]
  | skip =>
    unfold programSmallStepSemantics skipSmallStepSemantics
    rw[ite_one_zero_neg]; simp only [not_and_or]; exact Or.inr <| Or.inl h
  | valAssign v e =>
    rw[enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, valAssignSmallStepSemantics]
    split
    pick_goal 3; rfl
    all_goals (rw [ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h)
  | manipulate e e' =>
    rw[enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, manipulateSmallStepSemantics]
    split
    pick_goal 3; rfl
    all_goals (rw [ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h)
  | lookup v e =>
    rw[enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, lookupSmallStepSemantics]
    split
    pick_goal 3; rfl
    all_goals (rw [ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h)
  | compareAndSet v e_l e_v e_n =>
    rw[enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, compareAndSetSmallStepSemantics]
    split
    pick_goal 3; rfl
    all_goals (rw [ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h)
  | allocate v n => sorry
  | free v n =>
    rw[enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, freeSmallStepSemantics]
    split
    pick_goal 3; rfl
    all_goals (rw [ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h)
  | sequential c₁ c₂ ih₁ ih₂ => sorry
  | probabilisticChoice e c₁ c₂ _ _ =>
    rw[enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
    split
    · rw [ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h
    · rw [if_neg]; intro h'; exact h h'.left
  | conditionalChoice e c₁ c₂ _ _ =>
    rw[enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, conditionalChoiceSmallStepSemantics]
    split
    all_goals (rw [ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h)
  | loop e c ih =>
    rw[enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, loopSmallStepSemantics]
    split
    all_goals (rw [ite_one_zero_neg]; simp only [not_and_or]; exact Or.inl h)
  | concurrent c₁ c₂ ih₁ ih₂ => sorry



  -- allocation
  -- pick_goal 6
  -- · unfold allocateSmallStepSemantics
  --   rw[ite_one_zero_neg]
  --   simp only [not_exists, not_and]
  --   intro n h_a h_terminating h_not_alloc
  --   rw [isNotAlloc_def] at h_not_alloc




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
