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
  | concurrentLeft : Action → Action
  | concurrentRight : Action → Action

/-- Skip always succeeds with the same state. -/
@[simp]
noncomputable def skipSmallStepSemantics :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => iteOneZero (c = terminated ∧ a = Action.deterministic ∧ s = s')

/-- valAssign succeeds if the expression is well-defined and the resulting state has changed.
    valAssign fails if the expression is not well-defined and the state remains unchanged. -/
@[simp]
noncomputable def assignSmallStepSemantics (v : Variable) (e : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | terminated => iteOneZero (a = Action.deterministic ∧ substituteStack s v (e s.stack) = s')
  | _ => 0

/-- manipulate succeeds if the expressions are well-defined and an allocated location. It changes
    a heap position. manipulate fails if one expression is not well-defined or not an allocated location-/
@[simp]
noncomputable def manipulateSmallStepSemantics (e_loc e_val : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | terminated => iteOneZero (a = Action.deterministic ∧
      s.heap (e_loc s.stack) ≠ none ∧ substituteHeap s (e_loc s.stack) (e_val s.stack) = s')
  | error =>iteOneZero (a = Action.deterministic ∧ s = s' ∧ s.heap (e_loc s.stack) = none)
  | _ => 0

/-- lookup succeeds if the expression is well-defined and an allocated location is looked up.
    It changes the stack according to the value in the heap. lookup fails if the expression is not
    well-defined or the location is not allocated.-/
@[simp]
noncomputable def lookupSmallStepSemantics (v : Variable) (e : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | terminated => iteOneZero ( a = Action.deterministic ∧
      ∃ val, s.heap (e s.stack) = some val ∧ substituteStack s v val = s' )
  | error => iteOneZero ( a = Action.deterministic ∧ s = s' ∧ s.heap (e s.stack) = none)
  | _ => 0

/-- compareAndSet succeeds if all expressions are well-defined and the location is allocated.
    It changes the variable to 1 and sets the location to the new value if the value in the
    heap matches the compare value. It changes the variable to 0 if the value if the value in
    the heao does not match the compare value. -/
@[simp]
noncomputable def compareAndSetSmallStepSemantics (v : Variable) (e_loc e_cmp e_val : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | terminated => iteOneZero ( a = Action.deterministic
      ∧ ∃ old_val, s.heap (e_loc s.stack) = some old_val
      ∧ ((old_val = e_cmp s.stack ∧ substituteStack (substituteHeap s (e_loc s.stack) (e_val s.stack)) v 1 = s')
        ∨ old_val ≠ e_cmp s.stack ∧ substituteStack s v 0 = s'))
  | error => iteOneZero (a = Action.deterministic ∧ s = s' ∧ s.heap (e_loc s.stack) = none)
  | _ => 0

/-- allocate succeeds if the location m and n spaces afterwards are allocated and sets the values
    to the default value 0. -/
@[simp]
noncomputable def allocateSmallStepSemantics (v : Variable) (n : ℕ) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' =>
    iteOneZero (c = terminated ∧ ∃ m, a = Action.allocation m ∧ isNotAlloc s m n
      ∧ substituteStack (substituteHeap s m n) v m = s')

/-- free succeeds if the expression is well-defined and the location is up to n positions allocated.
    free fails if an expression is not well-defined or some location between l and l+n is not allocated. -/
@[simp]
noncomputable def freeSmallStepSemantics (e : ValueExp Variable) (n : ℕ) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | terminated => iteOneZero (a = Action.deterministic
    ∧ isAlloc s (e s.stack) n ∧ freeHeap s (e s.stack) n = s')
  | error => iteOneZero (a = Action.deterministic ∧ s = s'
    ∧ ¬isAlloc s (e s.stack) n)
  | _ => 0

/-- probabilisticChoice succeeds if the expression is well-defined and picks one program with the given probability.
    probabilisticChoice fails if the expression is not well-defined. -/
@[simp]
noncomputable def probabilisticChoiceSmallStepSemantics (e : ProbExp Variable) (c₁ c₂ : Program Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' =>
    if a = Action.deterministic ∧ s = s' then
      if c₁ = c ∧ c₂ = c then 1
      else if c₁ = c then e s.stack
      else if c₂ = c then σ (e s.stack)
      else 0
    else 0

/-- conditionalChoice succeeds if the expression is well-defined and picks the first if it is true and else the second.
    conditionalChoice fails if the epxression is not well-defined. -/
@[simp]
noncomputable def conditionalChoiceSmallStepSemantics (e : BoolExp Variable) (c₁ c₂ : Program Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' =>
    iteOneZero (a = Action.deterministic ∧ s = s'
      ∧ (e s.stack ∧ c₁ = c ∨ ¬ e s.stack ∧ c₂ = c))

/-- loopy Program that succeeds with terminated program if the loop condition is false,
    loops one more if the loop condition is true and errors if an expression is not well-defined-/
@[simp]
noncomputable def loopSmallStepSemantics (e : BoolExp Variable) (c : Program Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c' s' => match c' with
  | terminated => iteOneZero (a = Action.deterministic
    ∧ s = s' ∧ ¬ e s.stack)
  | c' => iteOneZero (a = Action.deterministic
    ∧ c' = sequential c (loop e c) ∧ s = s' ∧ e s.stack)

noncomputable def programSmallStepSemantics :
    (Program Variable) → (State Variable) →
    Action → (Program Variable) → (State Variable) → I
  | error => 0
  | terminated => 0
  | skip' => skipSmallStepSemantics
  | assign v e => assignSmallStepSemantics v e
  | manipulate e_loc e_val => manipulateSmallStepSemantics e_loc e_val
  | lookup v e => lookupSmallStepSemantics v e
  | compareAndSet v e_loc e_cmp e_val => compareAndSetSmallStepSemantics v e_loc e_cmp e_val
  | allocate v n => allocateSmallStepSemantics v n
  | free' e n => freeSmallStepSemantics e n
  | probabilisticChoice e c₁ c₂ => probabilisticChoiceSmallStepSemantics e c₁ c₂
  | conditionalChoice e c₁ c₂ => conditionalChoiceSmallStepSemantics e c₁ c₂
  | loop e c => loopSmallStepSemantics e c
  | sequential terminated c₂ => fun s a c s' => iteOneZero (a = Action.deterministic ∧ s=s' ∧ c = c₂)
  | sequential c₁ c₂ => fun s a c s' =>
    if let sequential c₁' c₂' := c then
      if c₂ = c₂' then (programSmallStepSemantics c₁ s a c₁' s') else 0
    else 0
  | concurrent terminated terminated => fun s a c s' => iteOneZero (c = terminated ∧ a = Action.deterministic ∧ s = s')
  | concurrent c₁ c₂ => fun s a c s' =>
    if let concurrent c₁' c₂' := c then match a with
      | Action.concurrentLeft a => if c₂ = c₂' then programSmallStepSemantics c₁ s a c₁' s' else 0
      | Action.concurrentRight a => if c₁ = c₁' then programSmallStepSemantics c₂ s a c₂' s' else 0
      | _ => 0
    else 0

def enabledAction : (Program Variable) → (State Variable) → Set Action
  | terminated, _                   => ∅
  | error, _                        => ∅
  | skip', _                        => { Action.deterministic }
  | assign _ _, _                   => { Action.deterministic }
  | manipulate _ _, _               => { Action.deterministic }
  | lookup _ _, _                   => { Action.deterministic }
  | compareAndSet _ _ _ _, _        => { Action.deterministic }
  | allocate _ n, s                 => { a | ∃ m, a = Action.allocation m ∧ isNotAlloc s m n }
  | free' _ _, _                    => { Action.deterministic }
  | sequential c₁ _, s              => if c₁ = terminated then { Action.deterministic } else enabledAction c₁ s
  | probabilisticChoice _ _ _, _    => { Action.deterministic }
  | conditionalChoice _ _ _, _      => { Action.deterministic }
  | loop _ _, _                     => { Action.deterministic }
  | concurrent c₁ c₂, s             => if c₁ = terminated ∧ c₂ = terminated then { Action.deterministic } else
                                       { Action.concurrentLeft a | a ∈ enabledAction c₁ s }
                                     ∪ { Action.concurrentRight a | a ∈ enabledAction c₂ s }

theorem zero_probability_of_not_enabledAction {a : Action} (h : ¬ a ∈ enabledAction c s)
    (c' : Program Variable) (s' : State Variable) :
    programSmallStepSemantics c s a c' s' = 0 := by

  induction c generalizing c' a with
  | terminated => unfold programSmallStepSemantics; simp only [Pi.zero_apply]
  | error => unfold programSmallStepSemantics; simp only [Pi.zero_apply]

  | skip' =>
    unfold programSmallStepSemantics skipSmallStepSemantics
    rw[iteOneZero_neg]; simp only [not_and_or]; exact Or.inr <| Or.inl h

  | assign v e =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, assignSmallStepSemantics]
    split
    pick_goal 2; rfl
    rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h
  | manipulate e e' =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, manipulateSmallStepSemantics]
    split
    pick_goal 3; rfl
    all_goals (rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h)
  | lookup v e =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, lookupSmallStepSemantics]
    split
    pick_goal 3; rfl
    all_goals (rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h)
  | compareAndSet v e_l e_v e_n =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, compareAndSetSmallStepSemantics]
    split
    pick_goal 3; rfl
    all_goals (rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h)
  | free' v n =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, freeSmallStepSemantics]
    split
    pick_goal 3; rfl
    all_goals (rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h)
  | conditionalChoice e c₁ c₂ _ _ =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, conditionalChoiceSmallStepSemantics]
    rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h
  | loop e c _ =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, loopSmallStepSemantics]
    split
    all_goals (rw [iteOneZero_neg]; simp only [not_and_or]; exact Or.inl h)

  | probabilisticChoice e c₁ c₂ _ _ =>
    rw [enabledAction, Set.mem_singleton_iff] at h
    simp only [programSmallStepSemantics, probabilisticChoiceSmallStepSemantics]
    simp only [ite_eq_right_iff, and_imp]
    intro h'; exfalso; exact h h'

  | allocate v n =>
    simp only [enabledAction, Set.mem_setOf_eq, not_exists, not_and] at h
    simp only [programSmallStepSemantics, allocateSmallStepSemantics]
    rw [iteOneZero_neg]
    simp only [not_exists, not_and]
    intro _ x h_act h_nalloc
    exfalso
    exact h x h_act h_nalloc

  | sequential c₁ c₂ ih₁ _ =>
    cases eq_or_ne c₁ terminated with
    | inl h_eq =>
      simp only [h_eq, programSmallStepSemantics]
      rw [iteOneZero_neg]; simp only [not_and]
      intro h_a _
      simp only [enabledAction, if_pos h_eq, Set.mem_singleton_iff] at h
      exfalso
      exact h h_a
    | inr h_ne =>
      simp only [programSmallStepSemantics]
      cases c' with
      | sequential c₁' c₂' =>
        simp only [ite_eq_right_iff]
        intro _
        simp only [enabledAction, if_neg h_ne] at h
        exact ih₁ h c₁'
      | _ => simp only [ite_eq_right_iff]

  | concurrent c₁ c₂ ih₁ ih₂ =>
    by_cases h_term : c₁ = terminated ∧ c₂ = terminated
    · simp only [h_term.left, h_term.right, programSmallStepSemantics]
      rw [iteOneZero_neg]
      simp only [not_and]
      intro _ h_a
      rw [enabledAction, if_pos h_term, Set.mem_singleton_iff] at h
      exfalso
      exact h h_a
    · rw [enabledAction, if_neg h_term] at h
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at h
      let ⟨h_left, h_right⟩ := h; clear h
      rw [programSmallStepSemantics]
      pick_goal 2
      · intro h₁ h₂; exact h_term ⟨h₁, h₂⟩
      · cases c' with
        | concurrent c₁' c₂' =>
          cases a with
          | concurrentLeft a =>
            simp only
            by_cases h_a : a ∈ enabledAction c₁ s
            · exfalso
              exact h_left a h_a rfl
            · cases eq_or_ne c₂ c₂' with
              | inl h_eq₂ =>
                rw [if_pos h_eq₂]
                exact ih₁ h_a c₁'
              | inr h_ne => exact if_neg h_ne
          | concurrentRight a =>
            simp only
            by_cases h_a : a ∈ enabledAction c₂ s
            · exfalso
              exact h_right a h_a rfl
            · cases eq_or_ne c₁ c₁' with
              | inl h_eq₁ =>
                rw [if_pos h_eq₁]
                exact ih₂ h_a c₂'
              |inr h_ne => exact if_neg h_ne
          | _ => simp only
        | _ => simp only




end Semantics
