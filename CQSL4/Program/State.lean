import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite

namespace State

open Rat Classical

def Stack (Variable : Type) : Type := Variable → Option ℚ
def Heap : Type := ℕ → Option ℚ

structure State (Variable : Type) where
  stack : Stack Variable
  heap : Heap

variable {Var : Type}


noncomputable def substituteStack
    (s : State Var) (v : Var) (q : ℚ) : State Var :=
  ⟨fun v' => if v = v' then some q else s.stack v',s.heap⟩

noncomputable def substituteHeap
    (s : State Var) (l : ℕ) (q : ℚ) : State Var :=
  ⟨s.stack, fun l' => if l = l' then some q else s.heap l'⟩

noncomputable def removeLocationHeap
    (s : State Var) (l : ℕ) : State Var :=
  ⟨s.stack, fun l' => if l = l' then none else s.heap l'⟩

noncomputable def isNotAlloc
    (s : State Var) (l : ℕ) (n : ℕ): Prop :=
  match n with
  | 0 => true
  | Nat.succ n => s.heap (l+n) = none ∧ isNotAlloc s l n

noncomputable def allocateHeap
    (s : State Var) (l : ℕ) (n : ℕ) : State Var :=
  match n with
  | 0 => s
  | Nat.succ n => substituteHeap (allocateHeap s l n) (l+n) 0

noncomputable def isAlloc
    (s : State Var) (l : ℕ) (n : ℕ) : Prop :=
  match n with
  | 0 => true
  | Nat.succ n => ∃ v, s.heap (l+n) = some v ∧ isAlloc s l n

noncomputable def freeHeap
    (s : State Var) (l : ℕ) (n : ℕ) : State Var :=
  match n with
  | 0 => s
  | Nat.succ n => removeLocationHeap (freeHeap s l n) (l+n)

end State
