import Mathlib.Data.Rat.Defs

namespace State

open Rat

variable (Variable : Type)

def State := Variable → Option ℚ

end State
