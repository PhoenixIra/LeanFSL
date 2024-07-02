import InvLimDiss.Program.Syntax
import InvLimDiss.Program.State
import InvLimDiss.Analysis.Probabilities

/-!
This file contains the semantics of the programming language as a probability transition function.
We especially feature definitions for each program constructs, excluding inductively defined ones (sequentation and concurrency).
-/

namespace Semantics

open unitInterval Syntax Program State Classical HeapValue

variable {Variable : Type}

/-- An action is deterministic (or probabilistic), allocation or left/right concurrect.-/
inductive Action where
  | deterministic : Action
  | allocation : ℕ+ → Action
  | concurrentLeft : Action → Action
  | concurrentRight : Action → Action

/-- Skip always succeeds with the same state. -/
@[simp]
noncomputable def skipSmallStepSemantics :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => iteOneZero (c = [Prog| ↓] ∧ a = Action.deterministic ∧ s = s')

/-- valAssign succeeds if the expression is well-defined and the resulting state has changed.
    valAssign fails if the expression is not well-defined and the state remains unchanged. -/
@[simp]
noncomputable def assignSmallStepSemantics (v : Variable) (e : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | [Prog| ↓] => iteOneZero (a = Action.deterministic ∧ substituteStack s v (e s.stack) = s')
  | _ => 0

/-- manipulate succeeds if the expressions are well-defined and an allocated location. It changes
    a heap position. manipulate fails if one expression is not well-defined or not an allocated location-/
@[simp]
noncomputable def manipulateSmallStepSemantics (e_loc e_val : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | [Prog| ↓] => iteOneZero (a = Action.deterministic ∧
      ∃ l : ℕ+, (e_loc s.stack) = l ∧ s.heap l ≠ undef ∧ substituteHeap s l (e_val s.stack) = s')
  | [Prog| ↯] => iteOneZero (a = Action.deterministic ∧ s = s'
      ∧ ((∃ l : ℕ+, (e_loc s.stack) = l ∧ s.heap l = undef) ∨ ¬ (∃ l : ℕ+, (e_loc s.stack) = l)))
  | _ => 0

/-- lookup succeeds if the expression is well-defined and an allocated location is looked up.
    It changes the stack according to the value in the heap. lookup fails if the expression is not
    well-defined or the location is not allocated.-/
@[simp]
noncomputable def lookupSmallStepSemantics (v : Variable) (e : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | [Prog| ↓] => iteOneZero ( a = Action.deterministic ∧
      ∃ l : ℕ+, l = (e s.stack) ∧ ∃ value, s.heap l = val value ∧ substituteStack s v value = s' )
  | [Prog| ↯] => iteOneZero ( a = Action.deterministic ∧ s = s'
      ∧ ((∃ l : ℕ+, (e s.stack) = l ∧ s.heap l = undef) ∨ ¬ (∃ l : ℕ+, (e s.stack) = l)))
  | _ => 0

/-- compareAndSet succeeds if all expressions are well-defined and the location is allocated.
    It changes the variable to 1 and sets the location to the new value if the value in the
    heap matches the compare value. It changes the variable to 0 if the value if the value in
    the heao does not match the compare value. -/
@[simp]
noncomputable def compareAndSetSmallStepSemantics (v : Variable) (e_loc e_cmp e_val : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | [Prog| ↓] => iteOneZero ( a = Action.deterministic
      ∧ ∃ l : ℕ+, l = (e_loc s.stack) ∧ ∃ old_val, s.heap l = val old_val
      ∧ ((old_val = e_cmp s.stack ∧ substituteStack (substituteHeap s l (e_val s.stack)) v 1 = s')
        ∨ old_val ≠ e_cmp s.stack ∧ substituteStack s v 0 = s'))
  | [Prog| ↯] => iteOneZero (a = Action.deterministic ∧ s = s'
      ∧ ((∃ l : ℕ+, (e_loc s.stack) = l ∧ s.heap l = undef) ∨ ¬ (∃ l : ℕ+, (e_loc s.stack) = l)))
  | _ => 0

/-- allocate succeeds if the location m and n spaces afterwards are allocated and sets the values
    to the default value 0. -/
@[simp]
noncomputable def allocateSmallStepSemantics (v : Variable) (e : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | [Prog| ↓] =>
    iteOneZero (∃ m, a = Action.allocation m ∧ ∃ n : ℕ, n = e s.stack
      ∧ isNotAlloc s m n ∧ substituteStack (substituteHeap s m n) v m = s')
  | [Prog| ↯] =>
    iteOneZero (a = Action.deterministic ∧ ¬ ∃ n : ℕ, n = e s.stack)
  | _ => 0


/-- free succeeds if the expression is well-defined and the location is up to n positions allocated.
    free fails if an expression is not well-defined or some location between l and l+n is not allocated. -/
@[simp]
noncomputable def freeSmallStepSemantics (e_loc e_n : ValueExp Variable) :
    (State Variable) → Action → (Program Variable) → (State Variable) → I :=
  fun s a c s' => match c with
  | [Prog| ↓] => iteOneZero (a = Action.deterministic
    ∧ ∃ l : ℕ+, l = (e_loc s.stack) ∧ ∃ n : ℕ, n = (e_n s.stack) ∧ isAlloc s l n ∧ freeHeap s l n = s')
  | [Prog| ↯] => iteOneZero (a = Action.deterministic ∧ s = s'
    ∧ ((∃ l : ℕ+, (e_loc s.stack) = l ∧ ∃ n : ℕ, n = e_n s.stack ∧ ¬isAlloc s l n)
      ∨ (∃ l : ℕ+, (e_loc s.stack) = l ∧ ¬ ∃ n : ℕ, n = e_n s.stack)
      ∨ (¬ ∃ l : ℕ+, (e_loc s.stack) = l)))
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
  | [Prog| ↓] => iteOneZero (a = Action.deterministic
    ∧ s = s' ∧ ¬ e s.stack)
  | c' => iteOneZero (a = Action.deterministic
    ∧ c' = [Prog| [[c]] ; while e begin [[c]] fi] ∧ s = s' ∧ e s.stack)

/-- The transition probability function of programs. -/
noncomputable def programSmallStepSemantics :
    (Program Variable) → (State Variable) →
    Action → (Program Variable) → (State Variable) → I
  | [Prog| ↯] => 0
  | [Prog| ↓] => 0
  | [Prog| skip] => skipSmallStepSemantics
  | [Prog| v ≔ e] => assignSmallStepSemantics v e
  | [Prog| e_loc *≔ e_val] => manipulateSmallStepSemantics e_loc e_val
  | [Prog| v ≔* e] => lookupSmallStepSemantics v e
  | [Prog| v ≔ cas(e_loc, e_cmp, e_val)] => compareAndSetSmallStepSemantics v e_loc e_cmp e_val
  | [Prog| v ≔ alloc(n)] => allocateSmallStepSemantics v n
  | [Prog| free(e_loc,e_n)] => freeSmallStepSemantics e_loc e_n
  | [Prog| pif e then [[c₁]] else [[c₂]] fi] => probabilisticChoiceSmallStepSemantics e c₁ c₂
  | [Prog| if e then [[c₁]] else [[c₂]] fi] => conditionalChoiceSmallStepSemantics e c₁ c₂
  | [Prog| while e begin [[c]] fi] => loopSmallStepSemantics e c
  | [Prog| [[c₁]] ; [[c₂]]] => fun s a c s' =>
    if c₁ = [Prog| ↓ ] then iteOneZero (a = Action.deterministic ∧ s=s' ∧ c = c₂)
    else if c = [Prog| ↯ ] then (programSmallStepSemantics c₁ s a [Prog| ↯] s')
    else if let [Prog| [[c₁']] ; [[c₂']]] := c then
      if c₂ = c₂' then (programSmallStepSemantics c₁ s a c₁' s') else 0
    else 0
  | [Prog| [[c₁]] || [[c₂]]] => fun s a c s' =>
    if c₁ = [Prog| ↓] ∧ c₂ = [Prog| ↓] then iteOneZero (c = [Prog| ↓] ∧ a = Action.deterministic ∧ s = s')
    else match a with
    | Action.concurrentLeft a =>
      if c = [Prog| ↯] then programSmallStepSemantics c₁ s a [Prog| ↯] s'
      else if let [Prog| [[c₁']] || [[c₂']]] := c then
        if c₂ = c₂' then programSmallStepSemantics c₁ s a c₁' s' else 0
      else 0
    | Action.concurrentRight a =>
      if c = [Prog| ↯] then programSmallStepSemantics c₂ s a [Prog| ↯] s'
      else if let [Prog| [[c₁']] || [[c₂']]] := c then
        if c₁ = c₁' then programSmallStepSemantics c₂ s a c₂' s' else 0
      else 0
    | _ => 0

end Semantics
