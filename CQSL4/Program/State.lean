import Mathlib.Data.Rat.Defs

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
  ⟨fun v' => if v = v' then q else s.stack v', s.heap⟩

noncomputable def substituteHeap
    (s : State Var) (l : ℕ) (q : ℚ) : State Var :=
  ⟨s.stack, fun l' => if l = l' then q else s.heap l'⟩

end State
