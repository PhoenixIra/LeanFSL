import InvLimDiss.SL.QuantitativeProofrules
import InvLimDiss.Program.Semantics

open Syntax Semantics QSL State

namespace Syntax

variable {Var : Type}

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

def varStateRV (f : StateRV Var) : Set Var := { v | ∃ s q, f s ≠ f (s.substituteStack v q)}

end QSL
