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

def BoolExp := (Stack Variable) → Bool

def ProbExp := (Stack Variable) → I

end Syntax
