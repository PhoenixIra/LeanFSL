import InvLimDiss.SL.QuantitativeProofrules
import InvLimDiss.Program.Semantics

/-! Framing is the act of removing a part of the separation logic objects out of the entailment.
  In its trivial case, we can just use the monotonicity of the operation.
  However, when we also want to move it along a program semantics object, we require
  certain additional criteria on the program and the formula.
  We formulate these requirements here:
  * `writtenVarProgram` are the program variables on the left side of assignments
  * `varStateRV` are the program variables occuring in a random variable-/

open Syntax Semantics QSL State

namespace Syntax

variable {Var : Type}

/-- Variables on the left of assignments in a program -/
def writtenVarProgram : Program Var → Set Var
  | [Prog| ↓] => ∅
  | [Prog| ↯] => ∅
  | [Prog| skip] => ∅
  | [Prog| v ≔ _] => {v}
  | [Prog| _ *≔ _] => ∅
  | [Prog| v ≔* _] => {v}
  | [Prog| v ≔ cas(_, _, _)] => {v}
  | [Prog| v ≔ alloc(_)] => {v}
  | [Prog| free(_, _)] => ∅
  | [Prog| if _ then [[c₁]] else [[c₂]] fi] => writtenVarProgram c₁ ∪ writtenVarProgram c₂
  | [Prog| pif _ then [[c₁]] else [[c₂]] fi] => writtenVarProgram c₁ ∪ writtenVarProgram c₂
  | [Prog| [[c₁]] ; [[c₂]]] => writtenVarProgram c₁ ∪ writtenVarProgram c₂
  | [Prog| while _ begin [[c]] fi] => writtenVarProgram c
  | [Prog| [[c₁]] || [[c₂]]] => writtenVarProgram c₁ ∪ writtenVarProgram c₂

end Syntax

namespace QSL

/-- Variables occuring in an expression, semantically defined. I.e. variables that never change
  the outcome of `f`. -/
def varStateRV (f : StateRV Var) : Set Var := { v | ∃ s q, f s ≠ f (s.substituteStack v q)}

end QSL
