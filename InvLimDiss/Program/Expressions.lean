import InvLimDiss.Program.State
import Mathlib.Topology.UnitInterval

/-
This file contains definitions and lemmas about expressions in our programming language.
To ease the process, we do not consider one syntax but allow arbitrary
(even noncomputable) lean functions here.
-/

namespace Syntax

open State unitInterval

variable (Variable : Type)

def ValueExp := (Stack Variable) → ℚ

@[simp]
noncomputable def substVal {Var : Type}
    (e : ValueExp Var) (v : Var) (e' : ValueExp Var) : ValueExp Var :=
  fun s => e (substituteVar s v (e' s))

@[simp]
noncomputable def varsValue {Var : Type} (e : ValueExp Var) : Set Var :=
  {x | ∃ s q, e (substituteVar s x q) ≠ e s}

def BoolExp := (Stack Variable) → Bool

@[simp]
noncomputable def substBool {Var : Type}
    (e : BoolExp Var) (v : Var) (e' : ValueExp Var) : BoolExp Var :=
  fun s => e (substituteVar s v (e' s))

@[simp]
noncomputable def varsBool {Var : Type} (e : BoolExp Var) : Set Var :=
  {x | ∃ s q, e (substituteVar s x q) ≠ e s}

def ProbExp := (Stack Variable) → I

@[simp]
noncomputable def substProb {Var : Type}
    (e : ProbExp Var) (v : Var) (e' : ValueExp Var) : ProbExp Var :=
  fun s => e (substituteVar s v (e' s))

@[simp]
noncomputable def varsProb {Var : Type} (e : ProbExp Var) : Set Var :=
  {x | ∃ s q, e (substituteVar s x q) ≠ e s}

end Syntax
